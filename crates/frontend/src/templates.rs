//! Post-hoc function templates for the compact `circuit.xbc`.
//!
//! The interpreter records the range of rows, witness ops and variables every wasm
//! call produced. After lowering, two calls whose rows are identical up to variable
//! renaming (variables the call allocated → offsets from its first one; variables
//! from outside → positional plugs) are the same template: the first becomes the
//! def and every matching call becomes a `CALL` record. Purely an encoding of the
//! flat circuit — expansion reproduces it exactly — so templates never change the
//! circuit, only its size and the cost of rolling it.

use std::collections::HashMap;

use xark_ir::primitive::WitnessGen;
use xark_ir::{LinearCombination, R1csConstraint, VarId};

use crate::builder::Builder;
use crate::output::{FunctionCall, FunctionTemplate, subst_witness_vars};

/// The rows, witness ops and variables one wasm call produced.
#[derive(Clone, Debug)]
pub(crate) struct Region {
    pub c0: usize,
    pub c1: usize,
    pub w0: usize,
    pub w1: usize,
    pub v0: VarId,
    pub v1: VarId,
    pub parent: Option<usize>,
    pub closed: bool,
}

/// Regions smaller than this stay inline: a `CALL` record isn't worth it.
pub(crate) const MIN_ROWS: usize = 8;

#[inline]
fn mix(h: u64, x: u64) -> u64 {
    (h.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95)
}

fn hash_fc(h: u64, fc: &xark_ir::FieldConst) -> u64 {
    match fc.as_i64() {
        Some(v) => mix(h, v as u64),
        None => fc
            .big()
            .to_signed_bytes_le()
            .chunks(8)
            .fold(mix(h, 0xb16), |h, c| {
                let mut w = [0u8; 8];
                w[..c.len()].copy_from_slice(c);
                mix(h, u64::from_le_bytes(w))
            }),
    }
}

/// Per-row work done once for the whole circuit: each constraint's constants and
/// shape hashed (independent of variable names), and each witness op's
/// constant/shape hash plus the variables it mentions in traversal order.
struct Prep {
    row: Vec<u64>,
    wit: Vec<u64>,
    wit_vars: Vec<VarId>,
    wit_off: Vec<u32>,
}

/// A stable code for a witness op's variant.
fn discriminant_code(w: &WitnessGen) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    std::mem::discriminant(w).hash(&mut h);
    h.finish()
}

fn prep(b: &Builder) -> Prep {
    use rayon::prelude::*;
    let row = b
        .constraints
        .par_iter()
        .map(|c| {
            [&c.a, &c.b, &c.c].iter().fold(0x5eed, |mut h, lc| {
                h = hash_fc(h, &lc.constant);
                h = mix(h, lc.terms.len() as u64);
                for t in &lc.terms {
                    h = hash_fc(h, &t.coeff);
                }
                h
            })
        })
        .collect();
    let mut wit = Vec::with_capacity(b.witness_gen.len());
    let mut wit_vars = Vec::new();
    let mut wit_off = Vec::with_capacity(b.witness_gen.len() + 1);
    for w in &b.witness_gen {
        wit_off.push(wit_vars.len() as u32);
        match w {
            Some(w) => {
                // Shape + constants (variables excluded), and the variables in
                // traversal order, in one pass. Fields the traversal doesn't visit
                // (a bit index, a limb width) are left to the exact comparison.
                let mut z = w.clone();
                let h = std::cell::Cell::new(mix(0x3a7, discriminant_code(w)));
                let vars = std::cell::RefCell::new(&mut wit_vars);
                subst_witness_vars(
                    &mut z,
                    &|v| {
                        vars.borrow_mut().push(v);
                        h.set(mix(h.get(), 0x1d));
                        v
                    },
                    &|l| {
                        let mut x = hash_fc(h.get(), &l.constant);
                        x = mix(x, l.terms.len() as u64);
                        for t in &l.terms {
                            vars.borrow_mut().push(t.var);
                            x = hash_fc(x, &t.coeff);
                        }
                        h.set(x);
                        l.clone()
                    },
                );
                wit.push(h.get());
            }
            None => wit.push(0),
        }
    }
    wit_off.push(wit_vars.len() as u32);
    Prep {
        row,
        wit,
        wit_vars,
        wit_off,
    }
}

/// Variable renaming for one region: internal → `2·offset`, external → `2·plug+1`
/// (plugs numbered by first appearance). `None` for a variable allocated after the
/// region (only a later merge can introduce one), which a template can't express.
struct Renamer<'a> {
    r: &'a Region,
    plugs: Vec<VarId>,
    plug_of: crate::builder::IdMap<VarId, u32>,
}

impl<'a> Renamer<'a> {
    fn new(r: &'a Region) -> Self {
        Renamer {
            r,
            plugs: Vec::new(),
            plug_of: Default::default(),
        }
    }
    #[inline]
    fn map(&mut self, v: VarId) -> Option<u64> {
        if v >= self.r.v1 {
            return None;
        }
        if v >= self.r.v0 {
            return Some(2 * (v - self.r.v0) as u64);
        }
        let n = self.plugs.len() as u32;
        let plugs = &mut self.plugs;
        let i = *self.plug_of.entry(v).or_insert_with(|| {
            plugs.push(v);
            n
        });
        Some(2 * i as u64 + 1)
    }
}

/// A region's form, hashed: constants and shapes (precomputed) mixed with the
/// renamed variables.
fn region_hash(b: &Builder, p: &Prep, r: &Region) -> Option<(u64, u64)> {
    let mut rn = Renamer::new(r);
    let (mut h1, mut h2) = (0x1234_5678u64, 0x8765_4321u64);
    let mut both = |x: u64| {
        h1 = mix(h1, x);
        h2 = mix(h2 ^ 0x9e37_79b9_7f4a_7c15, x);
    };
    both((r.c1 - r.c0) as u64);
    both((r.v1 - r.v0) as u64);
    for i in r.c0..r.c1 {
        both(p.row[i]);
        let c = &b.constraints[i];
        for lc in [&c.a, &c.b, &c.c] {
            for t in &lc.terms {
                both(rn.map(t.var)?);
            }
        }
    }
    for i in r.w0..r.w1 {
        if b.witness_gen[i].is_none() {
            continue;
        }
        both(p.wit[i]);
        for &v in &p.wit_vars[p.wit_off[i] as usize..p.wit_off[i + 1] as usize] {
            both(rn.map(v)?);
        }
    }
    for v in r.v0..r.v1 {
        both(match b.variables[v as usize].visibility {
            xark_ir::Visibility::Public => 1,
            xark_ir::Visibility::Private => 2,
            xark_ir::Visibility::Internal => 3,
        });
    }
    Some((h1, h2))
}

/// A region's rows and witness ops with variables renamed (for the exact check),
/// and its plugs.
fn normalized(
    b: &Builder,
    r: &Region,
) -> Option<(Vec<R1csConstraint>, Vec<WitnessGen>, Vec<VarId>)> {
    let rn = std::cell::RefCell::new(Renamer::new(r));
    let bad = std::cell::Cell::new(false);
    let map = |v: VarId| -> VarId {
        match rn.borrow_mut().map(v) {
            Some(x) => x as VarId,
            None => {
                bad.set(true);
                0
            }
        }
    };
    let map_lc = |l: &LinearCombination| -> LinearCombination {
        let mut l = l.clone();
        for t in &mut l.terms {
            t.var = map(t.var);
        }
        l
    };
    let rows: Vec<R1csConstraint> = b.constraints[r.c0..r.c1]
        .iter()
        .map(|c| R1csConstraint::general(0, map_lc(&c.a), map_lc(&c.b), map_lc(&c.c), ""))
        .collect();
    let wits: Vec<WitnessGen> = b.witness_gen[r.w0..r.w1]
        .iter()
        .flatten()
        .map(|w| {
            let mut w = w.clone();
            subst_witness_vars(&mut w, &map, &map_lc);
            w
        })
        .collect();
    if bad.get() {
        return None;
    }
    let plugs = rn.into_inner().plugs;
    Some((rows, wits, plugs))
}

fn same_rows(a: &[R1csConstraint], b: &[R1csConstraint]) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b)
            .all(|(x, y)| x.a == y.a && x.b == y.b && x.c == y.c)
}

/// Find repeated call regions and record them as templates + calls on `b`.
///
/// Templates nest: a def's body is its first instance's rows and witness ops, in
/// which repeated sub-calls are themselves `CALL`s (to defs found anywhere in the
/// circuit), so a scalar multiplication that repeats a field multiplication a
/// thousand times stores that multiplication once, not once per window.
pub(crate) fn detect(b: &mut Builder) {
    let regions = std::mem::take(&mut b.regions);
    let n = regions.len();
    // Children, in order, for the top-down walk.
    let mut children: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut roots = Vec::new();
    for (i, r) in regions.iter().enumerate() {
        match r.parent {
            Some(p) => children[p].push(i),
            None => roots.push(i),
        }
    }
    // Huge regions (a whole scalar multiplication) practically never repeat
    // exactly, and hashing every nesting level of them dominates detection.
    let max_rows = std::env::var("XARK_TPL_MAX")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or_else(|| (b.constraints.len() / 16).max(100_000));
    let eligible = |r: &Region| r.closed && r.c1 - r.c0 >= MIN_ROWS && r.c1 - r.c0 <= max_rows;

    // Group every eligible region by its form's hash.
    use rayon::prelude::*;
    let p = prep(b);
    // Only regions whose size repeats can repeat: hash just those, in parallel.
    let size_key = |r: &Region| (r.c1 - r.c0, r.w1 - r.w0, r.v1 - r.v0);
    let mut sizes: HashMap<(usize, usize, u32), u32> = HashMap::new();
    for r in regions.iter().filter(|r| eligible(r)) {
        *sizes.entry(size_key(r)).or_insert(0) += 1;
    }
    let bref: &Builder = b;
    type Key = (u64, u64, usize);
    let sig: Vec<Option<Key>> = regions
        .par_iter()
        .map(|r| {
            if !eligible(r) || sizes[&size_key(r)] < 2 {
                return None;
            }
            region_hash(bref, &p, r).map(|(h1, h2)| (h1, h2, r.c1 - r.c0))
        })
        .collect();
    let mut count: HashMap<Key, u32> = HashMap::new();
    for k in sig.iter().flatten() {
        *count.entry(*k).or_insert(0) += 1;
    }

    // Walk scopes top-down: the top level, then each new def's body (its first
    // instance's sub-calls). A region whose form repeats becomes a call; the first
    // instance of each form is its def. Then every call is checked byte-for-byte
    // against its def, in parallel; a mismatch (a hash collision) marks the region
    // and the walk is redone looking inside it instead.
    let mut bad: std::collections::HashSet<usize> = Default::default();
    // (region, def, enclosing def, plugs)
    #[allow(clippy::type_complexity)]
    let (mut templates, calls): (
        Vec<FunctionTemplate>,
        Vec<(usize, u32, Option<u32>, Vec<VarId>)>,
    ) = loop {
        let mut def_of: HashMap<Key, u32> = HashMap::new();
        let mut firsts: Vec<usize> = Vec::new(); // def → its first region
        let mut plan: Vec<(usize, u32, Option<u32>)> = Vec::new();
        let mut scopes: Vec<(Option<u32>, Option<Key>, Vec<usize>)> =
            vec![(None, None, roots.clone())];
        while let Some((parent, own, start)) = scopes.pop() {
            let mut stack: Vec<usize> = start.into_iter().rev().collect();
            while let Some(i) = stack.pop() {
                // A child spanning exactly its def's rows has the def's own form:
                // look inside it instead (a def can't call itself).
                if let Some(k) = sig[i]
                    && count[&k] >= 2
                    && Some(k) != own
                    && !bad.contains(&i)
                {
                    match def_of.get(&k) {
                        Some(&d) => plan.push((i, d, parent)),
                        None => {
                            let d = firsts.len() as u32;
                            firsts.push(i);
                            def_of.insert(k, d);
                            plan.push((i, d, parent));
                            scopes.push((Some(d), Some(k), children[i].clone()));
                        }
                    }
                    continue;
                }
                stack.extend(children[i].iter().rev());
            }
        }
        let forms: Vec<(Vec<R1csConstraint>, Vec<WitnessGen>, Vec<VarId>)> = firsts
            .par_iter()
            .map(|&i| normalized(bref, &regions[i]).expect("signed regions normalize"))
            .collect();
        let checked: Vec<Option<Vec<VarId>>> = plan
            .par_iter()
            .map(|&(i, d, _)| {
                let (dr, dw, dp) = &forms[d as usize];
                if firsts[d as usize] == i {
                    return Some(dp.clone());
                }
                let (rows, wits, plugs) = normalized(bref, &regions[i])?;
                (same_rows(dr, &rows) && *dw == wits).then_some(plugs)
            })
            .collect();
        let before = bad.len();
        bad.extend(
            plan.iter()
                .zip(&checked)
                .filter(|(_, c)| c.is_none())
                .map(|(p, _)| p.0),
        );
        if bad.len() == before {
            let templates = firsts
                .iter()
                .zip(forms)
                .map(|(&i, (_, _, plugs))| {
                    let r = &regions[i];
                    FunctionTemplate {
                        c0: r.c0,
                        c1: r.c1,
                        w0: r.w0,
                        w1: r.w1,
                        base_var: r.v0,
                        plug_vars: plugs,
                        outputs: Vec::new(),
                    }
                })
                .collect();
            let calls = plan
                .into_iter()
                .zip(checked)
                .map(|((i, d, parent), plugs)| (i, d, parent, plugs.expect("checked")))
                .collect();
            break (templates, calls);
        }
    };

    // Outputs: a template's internal variables that anything outside one of its
    // calls reads, in template coordinates (union over the calls, so a per-template
    // minimizer keeps every variable some caller needs). Calls nest, so a variable
    // can belong to a chain of calls; it is an output of each one the reader is
    // outside of.
    let reg = |ci: usize| &regions[calls[ci].0];
    let mut order: Vec<usize> = (0..calls.len())
        .filter(|&ci| reg(ci).v1 > reg(ci).v0)
        .collect();
    order.sort_by_key(|&ci| {
        let r = reg(ci);
        (r.v0, std::cmp::Reverse(r.v1), r.c0, std::cmp::Reverse(r.c1))
    });
    let v0s: Vec<VarId> = order.iter().map(|&ci| reg(ci).v0).collect();
    let mut up: Vec<Option<usize>> = vec![None; order.len()];
    {
        let mut st: Vec<usize> = Vec::new();
        for (pos, &ci) in order.iter().enumerate() {
            let r = reg(ci);
            while let Some(&top) = st.last() {
                if reg(order[top]).v1 <= r.v0 {
                    st.pop();
                } else {
                    break;
                }
            }
            up[pos] = st.last().copied();
            st.push(pos);
        }
    }
    use std::sync::atomic::{AtomicBool, Ordering::Relaxed};
    let outs: Vec<Vec<AtomicBool>> = calls
        .iter()
        .map(|(i, ..)| {
            (regions[*i].v0..regions[*i].v1)
                .map(|_| AtomicBool::new(false))
                .collect()
        })
        .collect();
    let mark = |v: VarId, row: usize, witness: bool| {
        let pos = v0s.partition_point(|&x| x <= v);
        if pos == 0 {
            return;
        }
        let mut q = Some(pos - 1);
        while let Some(x) = q {
            if v < reg(order[x]).v1 {
                break;
            }
            q = up[x];
        }
        while let Some(x) = q {
            let r = reg(order[x]);
            let inside = if witness {
                (r.w0..r.w1).contains(&row)
            } else {
                (r.c0..r.c1).contains(&row)
            };
            if inside {
                break; // inside this call, so inside every enclosing one too
            }
            outs[order[x]][(v - r.v0) as usize].store(true, Relaxed);
            q = up[x];
        }
    };
    if !order.is_empty() {
        b.constraints.par_iter().enumerate().for_each(|(row, c)| {
            for lc in [&c.a, &c.b, &c.c] {
                for t in &lc.terms {
                    mark(t.var, row, false);
                }
            }
        });
        (0..b.witness_gen.len()).into_par_iter().for_each(|row| {
            for &v in &p.wit_vars[p.wit_off[row] as usize..p.wit_off[row + 1] as usize] {
                mark(v, row, true);
            }
        });
    }
    let outs: Vec<Vec<bool>> = outs
        .into_iter()
        .map(|o| o.into_iter().map(AtomicBool::into_inner).collect())
        .collect();
    let mut union: Vec<Vec<bool>> = vec![Vec::new(); templates.len()];
    for ((_, d, _, _), o) in calls.iter().zip(&outs) {
        let u = &mut union[*d as usize];
        if u.is_empty() {
            *u = vec![false; o.len()];
        }
        for (a, &x) in u.iter_mut().zip(o) {
            *a |= x;
        }
    }
    // An output of a def that lies inside one of its body's sub-calls is an output
    // of that sub-call too (another instance of the def may be read where the
    // first isn't).
    loop {
        let mut changed = false;
        for (i, d, parent, _) in &calls {
            let Some(pd) = parent else { continue };
            let r = &regions[*i];
            let base = templates[*pd as usize].base_var;
            for o in 0..(r.v1 - r.v0) {
                let v = r.v0 + o;
                if union[*pd as usize][(v - base) as usize] && !union[*d as usize][o as usize] {
                    union[*d as usize][o as usize] = true;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    for (t, u) in templates.iter_mut().zip(&union) {
        t.outputs = u
            .iter()
            .enumerate()
            .filter(|(_, x)| **x)
            .map(|(i, _)| t.base_var + i as VarId)
            .collect();
    }

    b.function_templates = templates;
    for (i, def, parent, plugs) in calls {
        let r = &regions[i];
        b.function_calls.push(FunctionCall {
            def,
            parent,
            c0: r.c0,
            c1: r.c1,
            w0: r.w0,
            w1: r.w1,
            base: r.v0,
            plugs: plugs.into_iter().map(LinearCombination::var).collect(),
        });
    }
}
