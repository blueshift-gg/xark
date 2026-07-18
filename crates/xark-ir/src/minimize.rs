//! R1CS minimization by linear-variable elimination.
//!
//! Functionized lowering (and honest inlining) emit *linearly-defined* internal
//! variables: a materialized plug `p = <lc>`, a copy `w = v`, or a multiplication
//! output later pinned by an equality. Each such variable is uniquely determined
//! by one linear constraint, so it can be substituted away — Gaussian elimination
//! over the prime field. Because the eliminated variable is a *function* of the
//! survivors, every solution of the reduced system extends uniquely to the
//! original and vice versa: **satisfiability is preserved exactly, in both
//! directions**, so elimination can neither forge a witness (soundness) nor
//! reject an honest one (completeness). It only removes redundancy.
//!
//! This is where "optimal R1CS" lives for a flat proof system (Groth16): the
//! result is minimal under linear elimination + trivial-constraint drop, run to a
//! fixpoint — strictly at or below the inline baseline, and independent of how the
//! circuit was functionized (the bytecode structure never changes the *expanded*
//! constraints, only the artifact).
//!
//! Only `Internal` variables are eliminated; `Public`/`Private` inputs are the
//! circuit's interface and stay put (same ids, so the witness assignment and
//! public-input order are untouched — the caller's `assign` map remains a valid
//! superset).

use crate::field::FieldConst;
use crate::linear_combination::{LinearCombination, Term, VarId};
use crate::r1cs::{R1csConstraint, R1csProgram, Visibility};
use crate::solver::Fp;
#[cfg(test)]
use num_bigint::BigInt;
use num_bigint::BigUint;
use rayon::prelude::*;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::atomic::{AtomicBool, Ordering};

/// Fill-in guard: a variable is only eliminated when its replacement linear
/// combination has at most this many terms. Bounds the substitution cascade that
/// makes elimination superlinear on dense non-native (limb) arithmetic, while
/// leaving the overwhelmingly common cheap eliminations (plugs, copies, mul→eq
/// merges — a handful of terms) untouched.
const MAX_FILL_DEFAULT: usize = 32;

/// Fill-in threshold, overridable via `XARK_MAX_FILL` (higher = more reductions at
/// the cost of denser substitutions). Read once.
fn max_fill() -> usize {
    use std::sync::OnceLock;
    static V: OnceLock<usize> = OnceLock::new();
    *V.get_or_init(|| {
        #[cfg(feature = "debug")]
        {
            std::env::var("XARK_MAX_FILL")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(MAX_FILL_DEFAULT)
        }
        #[cfg(not(feature = "debug"))]
        {
            MAX_FILL_DEFAULT
        }
    })
}

/// A linear combination in reduced form: constant `k` plus `var → coeff`, every
/// value a field element, no zero coefficients. Coefficients are the same
/// Montgomery [`Fp`] the solver uses (native BN254 arithmetic — no `num-bigint`
/// alloc, no 254-bit `%` per op).
///
/// The term map is a `BTreeMap`, deliberately *not* a sorted `Vec`. The hot
/// operation is a sparse AXPY (`row += m·vlc`) where the row is often dense
/// (non-native limb reductions reach ~10⁵ terms) but `vlc` is small: the
/// `BTreeMap` touches only the `|vlc|` affected entries (`O(|vlc|·log|row|)`),
/// whereas a `Vec` merge would rewrite the *whole* row every time (`O(|row|)`) —
/// measured **4.7× slower** on the GLV circuit. Iteration is ascending-by-var,
/// which the R1CS output order and the "lowest-id internal pivot" rule both use.
#[derive(Clone)]
struct Lc {
    k: Fp,
    t: BTreeMap<VarId, Fp>,
}

/// `FieldConst → Fp` without a decimal string round-trip: the small-integer fast
/// path (the overwhelming majority of coefficients) goes straight through `i64`,
/// and the rare big constant converts from its `BigInt` bytes. `from_ir`/`to_ir`
/// run over every term of a ~million-constraint program, so the `to_string`/parse
/// the string path would do was ~half of `minimize`'s wall-clock.
fn fc_to_fp(fc: &FieldConst, m: &BigUint) -> Fp {
    match fc.as_i64() {
        Some(n) => Fp::from_i64(n, m),
        None => Fp::from_bigint(&fc.big(), m),
    }
}

impl Lc {
    fn from_ir(lc: &LinearCombination, m: &BigUint) -> Lc {
        let mut t = BTreeMap::new();
        for term in &lc.terms {
            let c = fc_to_fp(&term.coeff, m);
            if !c.is_zero() {
                // A repeated var (shouldn't occur post-`simplified`) accumulates.
                let e = t.entry(term.var).or_insert_with(|| Fp::zero(m));
                *e = e.add(&c);
                if e.is_zero() {
                    t.remove(&term.var);
                }
            }
        }
        Lc {
            k: fc_to_fp(&lc.constant, m),
            t,
        }
    }

    fn is_const(&self) -> bool {
        self.t.is_empty()
    }

    fn scale(&self, mul: &Fp) -> Lc {
        let mut t = BTreeMap::new();
        for (v, c) in &self.t {
            let nc = c.mul(mul);
            if !nc.is_zero() {
                t.insert(*v, nc);
            }
        }
        Lc {
            k: self.k.mul(mul),
            t,
        }
    }

    /// `self - other`.
    fn sub(&self, other: &Lc, m: &BigUint) -> Lc {
        let mut t = self.t.clone();
        for (v, c) in &other.t {
            let e = t.entry(*v).or_insert_with(|| Fp::zero(m));
            *e = e.sub(c);
            if e.is_zero() {
                t.remove(v);
            }
        }
        Lc {
            k: self.k.sub(&other.k),
            t,
        }
    }

    fn to_ir(&self) -> LinearCombination {
        // `self.t` is a `BTreeMap`, so `terms` is already ascending by var — the
        // R1CS wants that order, and skipping a re-sort matters on dense LCs.
        let terms: Vec<Term> = self
            .t
            .iter()
            .map(|(v, c)| Term {
                coeff: FieldConst::from_bigint(c.to_biguint().into()),
                var: *v,
            })
            .collect();
        LinearCombination {
            constant: FieldConst::from_bigint(self.k.to_biguint().into()),
            terms,
        }
    }
}

/// Substitute `v → vlc` into one constraint in place: `k += m·vlc.k` and
/// `lc += m·vlc` for the coefficient `m = lc[v]`, for each of `a,b,c`. Returns
/// `None` if the constraint didn't reference `v` (nothing to do), else `Some(new)`
/// where `new` is the set of vars *first introduced* into this constraint by the
/// substitution — exactly the `occ` entries the caller must add. A var that was
/// already present keeps its existing `occ` entry (append-only, never removed), so
/// reporting only the new insertions keeps `occ` and its later sort/dedup from
/// bloating to `fill_work` size on the dense reductions. `occ` itself is not
/// touched here, so the per-site work stays independent across the parallel sites.
fn subst_site(cj: &mut [Lc; 3], v: VarId, vlc: &Lc) -> Option<Vec<VarId>> {
    use std::collections::btree_map::Entry;
    let mut changed = false;
    let mut new_vars: Vec<VarId> = Vec::new();
    for lc in cj.iter_mut() {
        let Some(m) = lc.t.remove(&v) else { continue };
        changed = true;
        lc.k = lc.k.add(&m.mul(&vlc.k));
        for (var, co) in &vlc.t {
            match lc.t.entry(*var) {
                Entry::Occupied(mut e) => {
                    let nv = e.get().add(&m.mul(co));
                    if nv.is_zero() {
                        e.remove();
                    } else {
                        *e.get_mut() = nv;
                    }
                }
                Entry::Vacant(e) => {
                    // `m` and `co` are both nonzero ⇒ their product is nonzero in a
                    // prime field, so this is a genuine new term.
                    e.insert(m.mul(co));
                    new_vars.push(*var);
                }
            }
        }
    }
    changed.then_some(new_vars)
}

/// A raw pointer into the constraint vector, tagged `Send`/`Sync` so distinct
/// indices can be mutated from a `rayon` fan-out. Sound because the caller only
/// dispatches over a **deduped** site list — every worker touches a unique index,
/// so no two `&mut Option<[Lc; 3]>` ever alias, and the vector is not resized
/// during the parallel section.
#[derive(Clone, Copy)]
struct ConsPtr(*mut Option<[Lc; 3]>);
unsafe impl Send for ConsPtr {}
unsafe impl Sync for ConsPtr {}

/// Eliminations touching at least this many sites fan the substitution out across
/// threads; smaller ones stay serial (fan-out overhead would dominate). The dense
/// non-native reductions — the whole cost of an unguarded (`usize::MAX`) minimize
/// — touch hundreds-to-thousands of sites each, so they take the parallel path.
const PAR_SUBST_THRESHOLD: usize = 64;

/// The linear relation a constraint `a·b = c` imposes when it is *not* genuinely
/// quadratic — i.e. when `a` or `b` is a bare constant, so `a·b` is linear.
/// Returns `α·b − c` (or `β·a − c`), an `Lc` that the circuit forces to zero.
fn relation(a: &Lc, b: &Lc, c: &Lc, m: &BigUint) -> Option<Lc> {
    if a.is_const() {
        Some(b.scale(&a.k).sub(c, m))
    } else if b.is_const() {
        Some(a.scale(&b.k).sub(c, m))
    } else {
        None
    }
}

/// Minimize a program by eliminating every linearly-defined `Internal` variable
/// to a fixpoint. Returns a new program with the same field, the surviving
/// variables (original ids preserved), and rewritten constraints. If the field
/// modulus is unknown, the program is returned unchanged (elimination needs the
/// modulus for the coefficient inverse).
pub fn minimize(prog: &R1csProgram) -> R1csProgram {
    minimize_with_fill(prog, max_fill())
}

/// As [`minimize`], but with an explicit fill-in threshold. `usize::MAX` disables
/// the guard entirely — safe and reduction-complete on the *already per-template
/// reduced* R1CS (each dense elimination was bounded within a small template body,
/// so the flattened boundary pass no longer cascades), but catastrophic on a raw
/// unreduced circuit.
pub fn minimize_with_fill(prog: &R1csProgram, fill: usize) -> R1csProgram {
    let Some(mod_dec) = &prog.field.modulus_decimal else {
        return prog.clone();
    };
    let Ok(modulus) = mod_dec.parse::<BigUint>() else {
        return prog.clone();
    };

    // Size the var-indexed arrays (`is_internal`, `occ`, `referenced`) to cover
    // every id that appears — declared *or* referenced. A malformed program can
    // reference an undeclared ("dangling") id; it flows through here before the
    // caller's `validate()` rejects it, so we must not index out of bounds. A
    // dangling id is simply not `is_internal`, so it survives as a pseudo-input and
    // validation still catches it downstream.
    let max_referenced = prog
        .constraints
        .par_iter()
        .map(|c| {
            c.a.terms
                .iter()
                .chain(&c.b.terms)
                .chain(&c.c.terms)
                .map(|t| t.var as usize + 1)
                .max()
                .unwrap_or(0)
        })
        .max()
        .unwrap_or(0);
    let n_vars = prog
        .variables
        .iter()
        .map(|v| v.id as usize + 1)
        .max()
        .unwrap_or(0)
        .max(max_referenced);
    // Only `Internal` variables are eliminable. A flat var-id-indexed bitmap gives
    // O(1) pivot-eligibility tests in the hot loop instead of a `BTreeMap` lookup.
    let mut is_internal = vec![false; n_vars];
    for v in &prog.variables {
        if v.visibility == Visibility::Internal {
            is_internal[v.id as usize] = true;
        }
    }

    // Parse constraints; `None` marks an eliminated/trivial (dead) constraint.
    // Per-constraint `from_ir` is independent, so build in parallel — over a
    // million constraints, this parse (field-element construction per term) was a
    // serial chunk on par with the elimination loop itself.
    let mut cons: Vec<Option<[Lc; 3]>> = prog
        .constraints
        .par_iter()
        .map(|c| {
            Some([
                Lc::from_ir(&c.a, &modulus),
                Lc::from_ir(&c.b, &modulus),
                Lc::from_ir(&c.c, &modulus),
            ])
        })
        .collect();

    // Occurrence index: var → constraint indices that reference it. Flat,
    // var-id-indexed (ids are contiguous), and **append-only with stale
    // tolerance**: a constraint that dies or drops a var is *not* removed from the
    // lists — when a var is later eliminated, its site list is deduped and each
    // site is re-checked (`cons[j]` alive? `lc.t` still holds the var?), so stale
    // entries are cheap no-ops. This removes an O(log) `BTreeMap` lookup + a
    // `BTreeSet` insert from the hot per-fill-term path (the dominant cost — see
    // the fill_work profile), which the dense-substitution cascade runs millions
    // of times.
    let mut occ: Vec<Vec<usize>> = vec![Vec::new(); n_vars];
    for (i, c) in cons.iter().enumerate() {
        if let Some(c) = c {
            // Push keys directly (a var shared by two of `a,b,c` lists `i` twice —
            // harmless, deduped on consumption); avoids a per-constraint `BTreeSet`
            // allocation, which is costly on the dense (~10⁵-term) constraints.
            for lc in c {
                for v in lc.t.keys() {
                    occ[*v as usize].push(i);
                }
            }
        }
    }

    let mut queue: VecDeque<usize> = (0..cons.len()).collect();
    let mut in_queue = vec![true; cons.len()];
    let mut eliminated: BTreeSet<VarId> = BTreeSet::new();

    while let Some(i) = queue.pop_front() {
        in_queue[i] = false;
        let Some(c) = &cons[i] else { continue };
        let Some(rel) = relation(&c[0], &c[1], &c[2], &modulus) else {
            continue;
        };

        // Trivial `0 = 0` (or `0 = k` with no vars): drop it. A `0 = nonzero`
        // (infeasible) constraint is left in place so the backend still rejects it.
        // (Stale `occ` entries for `i` are left behind — harmless: a later visit to
        // this dead index short-circuits on `cons[i] == None`.)
        if rel.t.is_empty() {
            if rel.k.is_zero() {
                cons[i] = None;
            }
            continue;
        }

        // Pick the lowest-id Internal var to eliminate (`rel.t` iterates ascending
        // by var, so the first Internal is the lowest id; any nonzero coeff is
        // invertible in the prime field). Elimination order does not change the
        // result (the fixpoint is confluent) and — measured — does not change the
        // total substitution work either: lowest-id-first is already topological for
        // these circuits, so a ready-first/min-fill order buys nothing.
        let Some((&v, coeff)) = rel.t.iter().find(|(var, _)| is_internal[**var as usize]) else {
            continue;
        };

        // v = -(rel without v) / coeff.
        let mut rest = rel.clone();
        rest.t.remove(&v);
        let factor = coeff
            .inverse()
            .expect("nonzero field coeff is invertible")
            .neg();
        let vlc = rest.scale(&factor);

        // Fill-in guard: don't eliminate a var whose replacement LC is dense. A
        // dense `vlc` spliced into every referencing constraint (non-native limb
        // arithmetic) cascades into denser constraints and a superlinear blowup
        // (ecdsa's 6.4M didn't finish in minutes; ed25519's small-`vlc`
        // eliminations took 117s). Keeping `v` with its defining constraint is
        // still sound — just fewer eliminations. The cheap plug/copy/merge
        // eliminations (`|vlc|` tiny) are the bulk of the reduction and unaffected.
        if vlc.t.len() > fill {
            continue;
        }

        // Retire the defining constraint (stale `occ` entries for `i` are left
        // behind — harmless, as above).
        cons[i] = None;
        eliminated.insert(v);

        // Substitute v → vlc everywhere it appears. `sites` is deduped: the
        // append-only index can list a constraint more than once, and a repeat
        // would be a wasted (harmless) `lc.t` miss — dedup keeps the fill bounded.
        let mut sites = std::mem::take(&mut occ[v as usize]);
        sites.sort_unstable();
        sites.dedup();
        // Substitute into every site — in parallel for the dense (many-site)
        // eliminations, since the sites are distinct indices and each site's
        // update is independent. `changed` collects the sites that actually held
        // `v`; `occ` and the worklist are updated serially afterwards (an `occ`
        // push is O(1) and cheap next to the field arithmetic that was fanned out).
        let changed: Vec<(usize, Vec<VarId>)> = if sites.len() >= PAR_SUBST_THRESHOLD {
            let ptr = ConsPtr(cons.as_mut_ptr());
            sites
                .par_iter()
                .filter_map(|&j| {
                    // Capture the whole `ConsPtr` (Send+Sync), not the bare field —
                    // else edition-2021 disjoint capture grabs the raw pointer.
                    let p = ptr;
                    // SAFETY: `sites` is deduped, so `j` is unique to this worker;
                    // no other thread holds `&mut cons[j]`, and `cons` is not
                    // resized here. `p` outlives the fan-out (borrows `cons`).
                    let slot = unsafe { &mut *p.0.add(j) };
                    let cj = slot.as_mut()?;
                    subst_site(cj, v, &vlc).map(|new| (j, new))
                })
                .collect()
        } else {
            sites
                .iter()
                .filter_map(|&j| {
                    let cj = cons[j].as_mut()?;
                    subst_site(cj, v, &vlc).map(|new| (j, new))
                })
                .collect()
        };
        for (j, new_vars) in &changed {
            // Record only the vars newly introduced into `j` (see `subst_site`).
            // Direct per-(var,j) push into the flat `occ` is the fastest option here:
            // it's op-count-bound on `occ[var]` cells that stay cache-warm (a single
            // elimination touches the same small `vlc` var set across all its sites),
            // so grouping/sorting to batch it measured *slower*, and the billion-pair
            // scatter can't be partitioned by var cheaply enough to parallelize.
            for var in new_vars {
                occ[*var as usize].push(*j);
            }
            if !in_queue[*j] {
                in_queue[*j] = true;
                queue.push_back(*j);
            }
        }
    }

    // Fixpoint invariant (`XARK_VERIFY`): after minimization no surviving
    // constraint may still *linearly define* an eliminable (`Internal`) variable —
    // if one did, the loop missed an elimination and the output isn't optimal under
    // the rule set. This makes R1CS-optimality a checked property, not a claim.
    if crate::dbg_flag("XARK_VERIFY") {
        for c in cons.iter().flatten() {
            if let Some(rel) = relation(&c[0], &c[1], &c[2], &modulus) {
                if let Some((&v, coeff)) = rel.t.iter().find(|(var, _)| is_internal[**var as usize])
                {
                    // Fixpoint is relative to the fill-in guard: a survivor is only
                    // a missed elimination if its replacement LC is within budget.
                    let mut rest = rel.clone();
                    rest.t.remove(&v);
                    let factor = coeff
                        .inverse()
                        .expect("nonzero field coeff is invertible")
                        .neg();
                    let vlc = rest.scale(&factor);
                    if vlc.t.len() <= fill {
                        panic!(
                            "XARK_VERIFY: minimizer not at fixpoint — a cheap-to-eliminate \
                             Internal variable survives"
                        );
                    }
                }
            }
        }
    }

    // Surviving vars: every input, plus any Internal still referenced. A flat
    // var-id bitmap (O(1) mark) beats a `BTreeSet` here — the surviving dense
    // constraints carry billions of term references to sweep, so do it in parallel:
    // concurrent `true` stores to a shared bit are idempotent, and `Relaxed` is
    // enough since the flags are only read after the join.
    let referenced: Vec<AtomicBool> = (0..n_vars).map(|_| AtomicBool::new(false)).collect();
    cons.par_iter().filter_map(|c| c.as_ref()).for_each(|c| {
        for lc in c {
            for v in lc.t.keys() {
                referenced[*v as usize].store(true, Ordering::Relaxed);
            }
        }
    });
    let variables = prog
        .variables
        .iter()
        .filter(|v| !eliminated.contains(&v.id))
        .filter(|v| {
            v.visibility != Visibility::Internal
                || referenced[v.id as usize].load(Ordering::Relaxed)
        })
        .cloned()
        .collect();

    // Rebuild the surviving constraints. Collect the survivors first (this fixes
    // the id order — the flattened position), then serialize each `Lc` back to IR
    // in parallel: `to_ir` (per-term field-element → decimal) over a million dense
    // constraints was the other serial chunk.
    let survivors: Vec<&[Lc; 3]> = cons.iter().flatten().collect();
    let constraints = survivors
        .par_iter()
        .enumerate()
        .map(|(id, c)| R1csConstraint {
            id: id as u32,
            a: c[0].to_ir(),
            b: c[1].to_ir(),
            c: c[2].to_ir(),
            debug: None,
        })
        .collect();

    R1csProgram {
        field: prog.field.clone(),
        variables,
        constraints,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::linear_combination::LinearCombination;
    use crate::r1cs::{FieldSpec, R1csConstraint, Variable};
    use std::collections::BTreeMap;

    fn var(id: u32, vis: Visibility) -> Variable {
        Variable {
            id,
            name: format!("v{id}"),
            visibility: vis,
        }
    }

    /// Reduce into `[0, m)` — a self-contained reference reducer for the tests'
    /// independent BigInt satisfiability check (production code uses `Fp`).
    fn rm(x: BigInt, r: &BigInt) -> BigInt {
        let v = x % r;
        if v < BigInt::ZERO {
            v + r
        } else {
            v
        }
    }

    /// Evaluate a linear combination at `assign`, reduced mod `m` into `[0, m)`.
    fn eval_lc(lc: &LinearCombination, assign: &BTreeMap<VarId, BigInt>, m: &BigInt) -> BigInt {
        let mut acc = lc.constant.big();
        for t in &lc.terms {
            let x = assign
                .get(&t.var)
                .cloned()
                .unwrap_or_else(|| BigInt::from(0));
            acc += t.coeff.big() * x;
        }
        rm(acc, m)
    }

    /// Does `assign` satisfy every `a*b = c` constraint of `prog` over its field?
    fn satisfies(prog: &R1csProgram, assign: &BTreeMap<VarId, BigInt>) -> bool {
        let m: BigInt = prog
            .field
            .modulus_decimal
            .as_ref()
            .unwrap()
            .parse()
            .unwrap();
        prog.constraints.iter().all(|con| {
            let a = eval_lc(&con.a, assign, &m);
            let b = eval_lc(&con.b, assign, &m);
            let c = eval_lc(&con.c, assign, &m);
            rm(a * b - c, &m) == BigInt::from(0)
        })
    }

    /// The soundness guarantee: a satisfying witness of the original R1CS still
    /// satisfies the minimized one (elimination is a Gaussian substitution, so the
    /// solution set is preserved for the surviving variables).
    #[test]
    fn minimize_preserves_satisfying_witness() {
        use Visibility::{Internal, Public};
        // v0*v1 = v2 ;  v3 = v2 + v0  (linear, internal → eliminable) ;  v3*v1 = v4
        let prog = R1csProgram {
            field: FieldSpec::bn254(),
            variables: vec![
                var(0, Public),
                var(1, Public),
                var(2, Internal),
                var(3, Internal),
                var(4, Public),
            ],
            constraints: vec![
                R1csConstraint::mul(
                    0,
                    LinearCombination::var(0),
                    LinearCombination::var(1),
                    2,
                    "v0*v1=v2",
                ),
                R1csConstraint::general(
                    1,
                    LinearCombination::var(2) + LinearCombination::var(0),
                    LinearCombination::one(),
                    LinearCombination::var(3),
                    "v3=v2+v0",
                ),
                R1csConstraint::mul(
                    2,
                    LinearCombination::var(3),
                    LinearCombination::var(1),
                    4,
                    "v3*v1=v4",
                ),
            ],
        };
        // A satisfying witness: v0=3, v1=5 ⇒ v2=15, v3=18, v4=90.
        let assign: BTreeMap<VarId, BigInt> = [(0, 3), (1, 5), (2, 15), (3, 18), (4, 90)]
            .into_iter()
            .map(|(k, v)| (k, BigInt::from(v)))
            .collect();
        assert!(
            satisfies(&prog, &assign),
            "sanity: witness satisfies original"
        );

        let reduced = minimize(&prog);

        // An internal var is linearly defined here (v3, or equivalently v2 via the
        // same relation), so the minimizer eliminates one and retires its
        // constraint. Which one is an implementation detail; that *some* reduction
        // happens is not.
        assert!(
            reduced.variables.len() < prog.variables.len(),
            "an internal var should be eliminated"
        );
        assert!(
            reduced.constraints.len() < prog.constraints.len(),
            "a constraint should be retired"
        );
        // The SAME witness still satisfies the reduced system — soundness.
        assert!(
            satisfies(&reduced, &assign),
            "the satisfying witness must still satisfy the minimized R1CS"
        );
    }

    /// The fill-in guard keeps a variable whose substitution LC exceeds the cap,
    /// but must never change satisfiability.
    #[test]
    fn fill_in_guard_never_breaks_satisfiability() {
        use Visibility::{Internal, Public};
        // A linearly-defined internal var whose definition has 3 terms; with a
        // fill cap of 1 it is *kept*, with a large cap it is eliminated. Either
        // way the witness must satisfy the result.
        let prog = R1csProgram {
            field: FieldSpec::bn254(),
            variables: vec![
                var(0, Public),
                var(1, Public),
                var(2, Public),
                var(3, Internal),
                var(4, Public),
            ],
            constraints: vec![
                R1csConstraint::general(
                    0,
                    LinearCombination::var(0)
                        + LinearCombination::var(1)
                        + LinearCombination::var(2),
                    LinearCombination::one(),
                    LinearCombination::var(3),
                    "v3=v0+v1+v2",
                ),
                R1csConstraint::mul(
                    1,
                    LinearCombination::var(3),
                    LinearCombination::var(0),
                    4,
                    "v3*v0=v4",
                ),
            ],
        };
        let assign: BTreeMap<VarId, BigInt> = [(0, 2), (1, 3), (2, 4), (3, 9), (4, 18)]
            .into_iter()
            .map(|(k, v)| (k, BigInt::from(v)))
            .collect();
        assert!(satisfies(&prog, &assign));

        let kept = minimize_with_fill(&prog, 1); // guard blocks the 3-term elimination
        assert!(
            kept.variables.iter().any(|v| v.id == 3),
            "v3 kept under cap 1"
        );
        assert!(satisfies(&kept, &assign));

        let elim = minimize_with_fill(&prog, 64); // ample budget → eliminated
        assert!(
            elim.variables.iter().all(|v| v.id != 3),
            "v3 eliminated under cap 64"
        );
        assert!(satisfies(&elim, &assign));
    }
}
