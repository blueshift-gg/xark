//! Exhaustive witness search: with every input fixed, find *all* assignments of the
//! derived variables that satisfy the constraints — none, exactly one, or more.
//!
//! The honest solver ([`crate::solver::solve`]) only shows that the hint program's
//! witness satisfies the circuit; a malicious prover picks any values it likes. This
//! search is the adversary: a constraint-propagation solver (exact field values from
//! linear rows, integer interval reasoning on rows whose coefficients are small,
//! `{0,1}` from booleanity rows) with complete case splitting on bounded domains. Each
//! deduction is implied by the constraints, so its verdicts are proofs:
//!
//! * [`WitnessSearch::None`]: no assignment satisfies the circuit for these inputs;
//! * [`WitnessSearch::Unique`]: exactly one does (every variable is determined);
//! * [`WitnessSearch::Multiple`]: two different satisfying assignments exist.
//!
//! [`WitnessSearch::Inconclusive`] when propagation gets stuck on a variable with no
//! finite domain to split, or the node budget runs out. Meant for test-sized circuits.
//! Known blind spot: non-native modular relations (a limb-wise `λ·d ≡ n (mod q)` with a
//! ~256-bit `q`, as in the EC and bignum inverse gadgets). Their uniqueness is a number-
//! theoretic fact (`q` prime, `d ≠ 0`, `λ < q`) that propagation can't derive and
//! splitting can't reach at that size. It's proven in Lean
//! (`mul_mod_via_limbwise_constraints`, `ec_add_incomplete_*_sound`), and the same
//! gadget code over narrow limbs is searched exhaustively for both curve shapes,
//! `a = 0` and `a = −3` (`snapshot.rs`, `small_field_curve_gadgets_are_sound`).
//! Variables no constraint references are ignored (they can't affect acceptance).

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Signed, Zero};

use crate::linear_combination::VarId;
use crate::primitive::{PrimitiveProgram, VarRole};
use crate::solver::{Fp, SolveError};

/// The outcome of [`search_witnesses`].
#[derive(Debug)]
pub enum WitnessSearch {
    /// No assignment satisfies the constraints: the inputs are rejected.
    None,
    /// Exactly one assignment satisfies them (of every variable some constraint
    /// mentions; a variable in no constraint is unconstrained by definition).
    Unique(BTreeMap<VarId, Fp>),
    /// Two satisfying assignments that differ at `var`.
    Multiple { var: VarId, name: String },
    /// Neither proven: why the search stopped.
    Inconclusive(String),
}

#[derive(Clone, Debug)]
enum Dom {
    Val(Fp),
    /// The field elements `{lo mod p, …, hi mod p}`, `hi − lo < p`.
    Range(BigInt, BigInt),
    Free,
}

struct Conflict;

enum Trail {
    Dom(usize, Dom),
    /// `v` was aliased to `rep` (pushed onto `deps[rep]`).
    Alias(usize, usize),
}

/// A variable resolved through its aliases: a value, or `a·rep + b`.
enum Resolved {
    Known(Fp),
    Lin(usize, Fp, Fp),
}

/// A constraint with its coefficients reduced into the field and its variables
/// densely indexed once, up front (`process` runs it many times).
struct Row {
    konst: Fp,
    /// `c · left · right`.
    muls: Vec<(Fp, usize, usize)>,
    /// `c · var`.
    lins: Vec<(Fp, usize)>,
}

struct Search<'a> {
    program: &'a PrimitiveProgram,
    rows: Vec<Row>,
    /// `0` and `1` in the field.
    zero: Fp,
    one: Fp,
    p: BigUint,
    pi: BigInt,
    /// Dense index for each referenced variable.
    index: BTreeMap<VarId, usize>,
    ids: Vec<VarId>,
    var_cons: Vec<Vec<usize>>,
    dom: Vec<Dom>,
    /// `v = a·u + b` for an unknown `u`, learned from a two-unknown linear row;
    /// rows over `v` then reason about `u`.
    alias: Vec<Option<(usize, Fp, Fp)>>,
    /// The variables aliased to each variable.
    deps: Vec<Vec<usize>>,
    trail: Vec<Trail>,
    queue: Vec<usize>,
    queued: Vec<bool>,
    nodes: usize,
    budget: usize,
    deadline: Option<std::time::Instant>,
    /// Rows processed, to check the deadline every so often.
    steps: usize,
    found: Vec<Vec<Fp>>,
    /// [`search_projection`]: the projected variables, and their distinct values seen.
    project: Option<Vec<usize>>,
    proj_found: Vec<Vec<Fp>>,
    stuck: Option<String>,
    /// Set when some branch tried only sample values: `None`/`Unique` unproven.
    incomplete: Option<String>,
}

/// Search every satisfying assignment of `program`'s derived variables, with the
/// inputs fixed to `inputs` (decimal values by var id; every input must be given).
/// `budget` caps the case splits (a few thousand is plenty for fuzz-sized circuits).
pub fn search_witnesses(
    program: &PrimitiveProgram,
    inputs: &BTreeMap<VarId, String>,
    budget: usize,
) -> Result<WitnessSearch, SolveError> {
    search_witnesses_within(program, inputs, budget, None)
}

/// [`search_witnesses`], giving up (inconclusive) after `limit` of wall time.
pub fn search_witnesses_within(
    program: &PrimitiveProgram,
    inputs: &BTreeMap<VarId, String>,
    budget: usize,
    limit: Option<std::time::Duration>,
) -> Result<WitnessSearch, SolveError> {
    let mut s = match Search::new(program, inputs, budget, limit, false)? {
        Ok(s) => s,
        Err(why) => return Ok(WitnessSearch::Inconclusive(why)),
    };
    s.dfs();
    if s.found.len() >= 2 {
        let (a, b) = (&s.found[0], &s.found[1]);
        let i = (0..a.len()).find(|&i| a[i] != b[i]).unwrap_or(0);
        let var = s.ids[i];
        let name = program
            .vars
            .iter()
            .find(|v| v.id == var)
            .map(|v| v.name.clone())
            .unwrap_or_default();
        return Ok(WitnessSearch::Multiple { var, name });
    }
    if let Some(why) = s.stuck.or(s.incomplete) {
        return Ok(WitnessSearch::Inconclusive(why));
    }
    Ok(match s.found.pop() {
        None => WitnessSearch::None,
        Some(vals) => WitnessSearch::Unique(s.ids.iter().copied().zip(vals).collect()),
    })
}

/// The outcome of [`search_projection`].
#[derive(Debug)]
pub enum Projection {
    /// No assignment satisfies the constraints.
    None,
    /// Every satisfying assignment gives `project` these values (there may be several
    /// assignments, differing elsewhere).
    One(Vec<Fp>),
    /// Two satisfying assignments that differ on `project`.
    Many(Vec<Fp>, Vec<Fp>),
    /// Neither proven: why the search stopped.
    Inconclusive(String),
}

/// Whether the constraints **determine** `project`: search every satisfying assignment
/// with `fixed` set (inputs not in `fixed` are left free, like derived variables) and
/// compare their values on `project`. Freedom elsewhere (a non-canonical internal
/// value) is allowed; what's proven is that no two witnesses disagree on `project`.
pub fn search_projection(
    program: &PrimitiveProgram,
    fixed: &BTreeMap<VarId, String>,
    project: &[VarId],
    budget: usize,
    limit: Option<std::time::Duration>,
) -> Result<Projection, SolveError> {
    let mut s = match Search::new(program, fixed, budget, limit, true)? {
        Ok(s) => s,
        Err(why) => return Ok(Projection::Inconclusive(why)),
    };
    let mut proj = Vec::new();
    for v in project {
        match s.index.get(v) {
            Some(&i) => proj.push(i),
            None => {
                return Ok(Projection::Inconclusive(format!(
                    "projected var {v} is in no constraint"
                )));
            }
        }
    }
    s.project = Some(proj);
    s.dfs();
    if s.proj_found.len() >= 2 {
        let b = s.proj_found.pop().unwrap();
        let a = s.proj_found.pop().unwrap();
        return Ok(Projection::Many(a, b));
    }
    if let Some(why) = s.stuck.or(s.incomplete) {
        return Ok(Projection::Inconclusive(why));
    }
    Ok(match s.proj_found.pop() {
        None => Projection::None,
        Some(v) => Projection::One(v),
    })
}

impl<'a> Search<'a> {
    /// Index the program and fix the inputs. `Err(reason)` (inconclusive) for a
    /// missing input, unless `allow_free`.
    fn new(
        program: &'a PrimitiveProgram,
        inputs: &BTreeMap<VarId, String>,
        budget: usize,
        limit: Option<std::time::Duration>,
        allow_free: bool,
    ) -> Result<Result<Self, String>, SolveError> {
        let p = crate::solver::modulus_of(program)?;
        let mut index = BTreeMap::new();
        let mut ids = Vec::new();
        let mut cons_vars = Vec::with_capacity(program.constraints.len());
        for expr in &program.constraints {
            let mut vs: Vec<usize> = Vec::new();
            let mut add = |v: VarId| {
                let i = *index.entry(v).or_insert_with(|| {
                    ids.push(v);
                    ids.len() - 1
                });
                if !vs.contains(&i) {
                    vs.push(i);
                }
            };
            for mt in &expr.mul_terms {
                add(mt.left);
                add(mt.right);
            }
            for lt in &expr.linear_terms {
                add(lt.var);
            }
            cons_vars.push(vs);
        }
        let mut var_cons = vec![Vec::new(); ids.len()];
        for (ci, vs) in cons_vars.iter().enumerate() {
            for &v in vs {
                var_cons[v].push(ci);
            }
        }
        // Every given value must name an input: fixing a derived variable (or an
        // unknown id) would silently search a different question.
        for id in inputs.keys() {
            match program.vars.iter().find(|v| v.id == *id) {
                None => return Ok(Err(format!("no variable with id {id}"))),
                Some(v) if matches!(v.role, VarRole::Derived) => {
                    return Ok(Err(format!("`{}` is not an input", v.name)));
                }
                Some(_) => {}
            }
        }
        let mut dom = vec![Dom::Free; ids.len()];
        for var in &program.vars {
            if matches!(var.role, VarRole::Derived) {
                continue;
            }
            let Some(value) = inputs.get(&var.id) else {
                if allow_free {
                    continue;
                }
                return Ok(Err(format!("input `{}` not given", var.name)));
            };
            if let Some(&i) = index.get(&var.id) {
                dom[i] = Dom::Val(Fp::from_decimal(value, &p));
            }
        }
        let n_cons = program.constraints.len();
        let n_vars = dom.len();
        let rows = program
            .constraints
            .iter()
            .map(|e| Row {
                konst: Fp::from_const(&e.constant, &p),
                muls: e
                    .mul_terms
                    .iter()
                    .map(|t| {
                        (
                            Fp::from_const(&t.coeff, &p),
                            index[&t.left],
                            index[&t.right],
                        )
                    })
                    .collect(),
                lins: e
                    .linear_terms
                    .iter()
                    .map(|t| (Fp::from_const(&t.coeff, &p), index[&t.var]))
                    .collect(),
            })
            .collect();
        let s = Search {
            program,
            rows,
            zero: Fp::zero(&p),
            one: Fp::from_i64(1, &p),
            pi: BigInt::from_biguint(Sign::Plus, p.clone()),
            p,
            index,
            ids,
            alias: vec![None; n_vars],
            deps: vec![Vec::new(); n_vars],
            var_cons,
            dom,
            trail: Vec::new(),
            queue: (0..n_cons).rev().collect(),
            queued: vec![true; n_cons],
            nodes: 0,
            budget,
            deadline: limit.map(|l| std::time::Instant::now() + l),
            steps: 0,
            found: Vec::new(),
            project: None,
            proj_found: Vec::new(),
            stuck: None,
            incomplete: None,
        };
        Ok(Ok(s))
    }
}

fn floor_div(a: &BigInt, b: &BigInt) -> BigInt {
    let (q, r) = (a / b, a % b);
    if !r.is_zero() && (r.is_negative() != b.is_negative()) {
        q - 1
    } else {
        q
    }
}

fn ceil_div(a: &BigInt, b: &BigInt) -> BigInt {
    -floor_div(&-a, b)
}

impl Search<'_> {
    fn int(&self, x: &Fp) -> BigInt {
        BigInt::from_biguint(Sign::Plus, x.to_biguint())
    }

    fn fp(&self, z: &BigInt) -> Fp {
        let r = ((z % &self.pi) + &self.pi) % &self.pi;
        Fp::new(r.to_biguint().unwrap(), &self.p)
    }

    /// A field coefficient as a signed integer, when it is small (`|c| < 2^249`).
    fn small(&self, c: &Fp) -> Option<BigInt> {
        let z = self.int(c);
        let z = if z > &self.pi / 2 { z - &self.pi } else { z };
        (z.bits() < 250).then_some(z)
    }

    fn set(&mut self, v: usize, d: Dom) {
        let value = match &d {
            Dom::Val(x) => Some(x.clone()),
            _ => None,
        };
        let old = std::mem::replace(&mut self.dom[v], d);
        self.trail.push(Trail::Dom(v, old));
        self.touch(v);
        if let Some(x) = value {
            for k in 0..self.deps[v].len() {
                let d = self.deps[v][k];
                let (_, a, b) = self.alias[d].clone().expect("aliased");
                if matches!(self.dom[d], Dom::Free) {
                    self.set(d, Dom::Val(a.mul(&x).add(&b)));
                }
            }
        }
    }

    /// Queue the rows over `v` and over everything aliased to it.
    fn touch(&mut self, v: usize) {
        for k in 0..self.var_cons[v].len() {
            let ci = self.var_cons[v][k];
            if !self.queued[ci] {
                self.queued[ci] = true;
                self.queue.push(ci);
            }
        }
        for k in 0..self.deps[v].len() {
            self.touch(self.deps[v][k]);
        }
    }

    fn resolve(&self, v: usize) -> Resolved {
        // Fast path: no alias (the common case) — skip the `1·x + 0` arithmetic.
        if self.alias[v].is_none() {
            return match &self.dom[v] {
                Dom::Val(x) => Resolved::Known(x.clone()),
                _ => Resolved::Lin(v, self.one.clone(), self.zero.clone()),
            };
        }
        let (mut a, mut b, mut u) = (self.one.clone(), self.zero.clone(), v);
        loop {
            if let Dom::Val(x) = &self.dom[u] {
                return Resolved::Known(a.mul(x).add(&b));
            }
            match &self.alias[u] {
                Some((w, a2, b2)) => {
                    b = a.mul(b2).add(&b);
                    a = a.mul(a2);
                    u = *w;
                }
                None => return Resolved::Lin(u, a, b),
            }
        }
    }

    fn contains(&self, lo: &BigInt, hi: &BigInt, x: &Fp) -> bool {
        let z = self.int(x);
        let z = lo + ((z - lo) % &self.pi + &self.pi) % &self.pi;
        &z <= hi
    }

    fn assign(&mut self, v: usize, x: Fp) -> Result<(), Conflict> {
        match &self.dom[v] {
            Dom::Val(y) => return if *y == x { Ok(()) } else { Err(Conflict) },
            Dom::Range(lo, hi) if !self.contains(lo, hi, &x) => return Err(Conflict),
            _ => {}
        }
        self.set(v, Dom::Val(x));
        Ok(())
    }

    /// Narrow `v` to the integers `[lo, hi]` (an interval narrower than `p`).
    fn narrow(&mut self, v: usize, lo: BigInt, hi: BigInt) -> Result<(), Conflict> {
        let (lo, hi) = match &self.dom[v] {
            Dom::Val(x) => {
                return if self.contains(&lo, &hi, x) {
                    Ok(())
                } else {
                    Err(Conflict)
                };
            }
            Dom::Range(a, b) => {
                // Both are windows onto the same residues; align `[lo, hi]` to `a`'s.
                let shift = floor_div(&(a - &lo), &self.pi) * &self.pi;
                let (lo2, hi2) = (&lo + &shift, &hi + &shift);
                let mut best: Option<(BigInt, BigInt)> = None;
                for k in [-1i32, 0, 1] {
                    let off = &self.pi * k;
                    let (l, h) = ((&lo2 + &off).max(a.clone()), (&hi2 + &off).min(b.clone()));
                    if l <= h {
                        if best.is_some() {
                            // Two disjoint pieces: keep the wider domain (sound, coarser).
                            return Ok(());
                        }
                        best = Some((l, h));
                    }
                }
                let Some((l, h)) = best else {
                    return Err(Conflict);
                };
                if &l == a && &h == b {
                    return Ok(());
                }
                (l, h)
            }
            Dom::Free => (lo, hi),
        };
        if lo > hi {
            return Err(Conflict);
        }
        if lo == hi {
            let x = self.fp(&lo);
            self.set(v, Dom::Val(x));
        } else {
            self.set(v, Dom::Range(lo, hi));
        }
        Ok(())
    }

    /// Whether `process(ci)` can deduce nothing: the row has at least three
    /// unknowns, two of them unbounded. Then it is non-linear in two unknowns, or
    /// linear with two unbounded ones, and neither aliasing (two unknowns) nor
    /// interval reasoning (at most one unbounded) applies. Cheap — no field
    /// arithmetic, and it stops as soon as that is clear — where `process` would
    /// resolve every term: wide rows (bit sums) re-queued by each assignment were
    /// most of the search's time. Skipping only loses deductions (terms that
    /// cancel could leave fewer unknowns), never soundness: the row is re-queued
    /// whenever one of its variables changes.
    fn idle(&self, ci: usize) -> bool {
        let row = &self.rows[ci];
        // Up to three distinct unknown roots, and up to two distinct unbounded ones.
        let (mut seen, mut n) = ([usize::MAX; 3], 0usize);
        let (mut free, mut nf) = ([usize::MAX; 2], 0usize);
        let vars = row.lins.iter().map(|t| t.1);
        let vars = vars.chain(row.muls.iter().flat_map(|t| [t.1, t.2]));
        for v in vars {
            let mut u = v;
            while let Some((w, _, _)) = &self.alias[u] {
                u = *w;
            }
            match self.dom[u] {
                Dom::Val(_) => continue,
                Dom::Free if nf < 2 && !free[..nf].contains(&u) => {
                    free[nf] = u;
                    nf += 1;
                }
                _ => {}
            }
            if n < 3 && !seen[..n].contains(&u) {
                seen[n] = u;
                n += 1;
            }
            if n == 3 && nf == 2 {
                return true;
            }
        }
        false
    }

    /// Propagate one constraint.
    fn process(&mut self, ci: usize) -> Result<(), Conflict> {
        if self.idle(ci) {
            return Ok(());
        }
        let row = &self.rows[ci];
        let zero = self.zero.clone();
        let mut konst = row.konst.clone();
        // Terms per unknown, merged below (sorted, so a long row stays n·log n).
        let mut lin: Vec<(usize, Fp)> = Vec::new();
        let add_lin = |lin: &mut Vec<(usize, Fp)>, v: usize, c: Fp| lin.push((v, c));
        // A product of two unknowns: (left, right, coeff), `left <= right`.
        let mut quad: Vec<(usize, usize, Fp)> = Vec::new();
        for (c, l, r) in &row.muls {
            let (c, l, r) = (c, *l, *r);
            match (self.resolve(l), self.resolve(r)) {
                (Resolved::Known(x), Resolved::Known(y)) => konst = konst.add(&c.mul(&x).mul(&y)),
                (Resolved::Known(x), Resolved::Lin(u, a, b))
                | (Resolved::Lin(u, a, b), Resolved::Known(x)) => {
                    let cx = c.mul(&x);
                    add_lin(&mut lin, u, cx.mul(&a));
                    konst = konst.add(&cx.mul(&b));
                }
                (Resolved::Lin(u1, a1, b1), Resolved::Lin(u2, a2, b2)) => {
                    let k = c.mul(&a1).mul(&a2);
                    let key = (u1.min(u2), u1.max(u2));
                    if let Some(e) = quad.iter_mut().find(|e| (e.0, e.1) == key) {
                        e.2 = e.2.add(&k);
                    } else {
                        quad.push((key.0, key.1, k));
                    }
                    add_lin(&mut lin, u1, c.mul(&a1).mul(&b2));
                    add_lin(&mut lin, u2, c.mul(&b1).mul(&a2));
                    konst = konst.add(&c.mul(&b1).mul(&b2));
                }
            }
        }
        for (c, v) in &row.lins {
            match self.resolve(*v) {
                Resolved::Known(x) => konst = konst.add(&c.mul(&x)),
                Resolved::Lin(u, a, b) => {
                    add_lin(&mut lin, u, c.mul(&a));
                    konst = konst.add(&c.mul(&b));
                }
            }
        }
        lin.sort_by_key(|e| e.0);
        let mut merged: Vec<(usize, Fp)> = Vec::with_capacity(lin.len());
        for (v, c) in lin {
            match merged.last_mut() {
                Some(e) if e.0 == v => e.1 = e.1.add(&c),
                _ => merged.push((v, c)),
            }
        }
        let mut lin = merged;
        lin.retain(|e| !e.1.is_zero());
        quad.retain(|e| !e.2.is_zero());

        if !quad.is_empty() {
            // Univariate quadratic `a·v² + b·v + c` (every product is `v·v`).
            let v = quad[0].0;
            if quad.iter().any(|q| q.0 != v || q.1 != v) || lin.iter().any(|e| e.0 != v) {
                return Ok(());
            }
            let a = quad.iter().fold(zero.clone(), |s, q| s.add(&q.2));
            let b = lin.first().map(|e| e.1.clone()).unwrap_or(zero.clone());
            if a.is_zero() {
                // (Not reached: `quad` keeps only nonzero terms.) `linear` needs
                // nonzero coefficients.
                let lin = if b.is_zero() { vec![] } else { vec![(v, b)] };
                return self.linear(lin, konst);
            }
            // Roots `{0, 1}` exactly when `b = −a` and `c = 0` (booleanity).
            if konst.is_zero() && b == a.neg() {
                return self.narrow(v, BigInt::zero(), BigInt::one());
            }
            // Otherwise filter a small finite domain.
            if let Dom::Range(lo, hi) = &self.dom[v]
                && hi - lo < BigInt::from(64)
            {
                let (lo, hi) = (lo.clone(), hi.clone());
                let mut roots = Vec::new();
                let mut z = lo.clone();
                while z <= hi {
                    let x = self.fp(&z);
                    if a.mul(&x).mul(&x).add(&b.mul(&x)).add(&konst).is_zero() {
                        roots.push(z.clone());
                    }
                    z += 1;
                }
                return match roots.as_slice() {
                    [] => Err(Conflict),
                    [r0, .., r1] => self.narrow(v, r0.clone(), r1.clone()),
                    [r] => self.narrow(v, r.clone(), r.clone()),
                };
            }
            return Ok(());
        }
        self.linear(lin, konst)
    }

    /// `Σ cᵢ·vᵢ + konst = 0` over unknowns.
    fn linear(&mut self, lin: Vec<(usize, Fp)>, konst: Fp) -> Result<(), Conflict> {
        match lin.len() {
            0 => {
                if konst.is_zero() {
                    Ok(())
                } else {
                    Err(Conflict)
                }
            }
            1 => {
                let (v, c) = &lin[0];
                let x = konst.neg().mul(&c.inverse().expect("nonzero"));
                self.assign(*v, x)
            }
            2 => {
                // `c₀·u₀ + c₁·u₁ + k = 0` with `u₁` unbounded: `u₁ = a·u₀ + b`.
                let free = (0..2)
                    .rev()
                    .find(|&k| matches!(self.dom[lin[k].0], Dom::Free));
                let Some(k) = free else {
                    return self.intervals(&lin, &konst);
                };
                let (v, cv) = &lin[k];
                let (u, cu) = &lin[1 - k];
                let inv = cv.inverse().expect("nonzero").neg();
                let (a, b) = (cu.mul(&inv), konst.mul(&inv));
                self.alias[*v] = Some((*u, a, b));
                self.deps[*u].push(*v);
                self.trail.push(Trail::Alias(*v, *u));
                self.touch(*v);
                Ok(())
            }
            _ => self.intervals(&lin, &konst),
        }
    }

    /// Integer bounds propagation for a linear row with small coefficients: when the
    /// left side's integer range is narrower than `p`, the field equation is an
    /// integer equation, and each unknown is bounded by the others' ranges.
    fn intervals(&mut self, lin: &[(usize, Fp)], konst: &Fp) -> Result<(), Conflict> {
        let mut terms = Vec::with_capacity(lin.len());
        for (v, c) in lin {
            let Some(c) = self.small(c) else {
                return Ok(());
            };
            terms.push((*v, c));
        }
        let free: Vec<usize> = (0..terms.len())
            .filter(|&k| matches!(self.dom[terms[k].0], Dom::Free))
            .collect();
        let range = |s: &Self, v: usize, c: &BigInt| -> (BigInt, BigInt) {
            let Dom::Range(lo, hi) = &s.dom[v] else {
                unreachable!()
            };
            let (a, b) = (c * lo, c * hi);
            if a <= b { (a, b) } else { (b, a) }
        };
        let t = self.int(&konst.neg());
        match free.as_slice() {
            [] => {}
            // One unbounded unknown with coefficient ±1: it gets the others' range.
            [k] if terms[*k].1.abs().is_one() => {
                let (mut mn, mut mx) = (BigInt::zero(), BigInt::zero());
                for (j, (v, c)) in terms.iter().enumerate() {
                    if j != *k {
                        let (a, b) = range(self, *v, c);
                        mn += a;
                        mx += b;
                    }
                }
                if &mx - &mn >= self.pi {
                    return Ok(());
                }
                let (v, c) = &terms[*k];
                let (lo, hi) = (&t - &mx, &t - &mn);
                let (lo, hi) = if c.is_positive() {
                    (lo, hi)
                } else {
                    (-hi, -lo)
                };
                return self.narrow(*v, lo, hi);
            }
            _ => return Ok(()),
        }
        let bounds: Vec<(BigInt, BigInt)> = terms.iter().map(|(v, c)| range(self, *v, c)).collect();
        let mn: BigInt = bounds.iter().map(|b| &b.0).sum();
        let mx: BigInt = bounds.iter().map(|b| &b.1).sum();
        if &mx - &mn >= self.pi {
            return Ok(());
        }
        // The representative of `t` in `[mn, mn + p)`.
        let t = &mn + ((&t - &mn) % &self.pi + &self.pi) % &self.pi;
        if t > mx {
            return Err(Conflict);
        }
        for (j, (v, c)) in terms.iter().enumerate() {
            let (rest_lo, rest_hi) = (&mn - &bounds[j].0, &mx - &bounds[j].1);
            let (lo, hi) = (&t - rest_hi, &t - rest_lo);
            let (lo, hi) = if c.is_positive() {
                (ceil_div(&lo, c), floor_div(&hi, c))
            } else {
                (ceil_div(&hi, c), floor_div(&lo, c))
            };
            // Each variable appears once in `terms`, so its domain is the range
            // `bounds` was read from.
            let Dom::Range(a, b) = &self.dom[*v] else {
                unreachable!("a range variable narrowed twice in one pass")
            };
            let (lo, hi) = (lo.max(a.clone()), hi.min(b.clone()));
            if lo > hi {
                return Err(Conflict);
            }
            // Apply only a narrowing that fixes the value or shrinks the domain by a
            // quarter: two rows bounding each other can otherwise creep inward one
            // step at a time across a 2⁸⁶-wide domain. Skipping one is sound.
            let (old_w, new_w) = (b - a, &hi - &lo);
            if lo == hi || &new_w * 4 <= &old_w * 3 {
                self.narrow(*v, lo, hi)?;
            }
        }
        Ok(())
    }

    /// Debug: the undetermined variables after root propagation and their rows.
    fn dump(&self) {
        let name = |i: usize| {
            let id = self.ids[i];
            self.program
                .vars
                .iter()
                .find(|x| x.id == id)
                .map(|x| x.name.clone())
                .unwrap_or_default()
        };
        let show = |i: usize| match &self.dom[i] {
            Dom::Val(x) => format!("{}={}", name(i), x.to_decimal()),
            Dom::Range(lo, hi) => format!("{}∈[{lo},{hi}]", name(i)),
            Dom::Free => match &self.alias[i] {
                Some((u, a, b)) => format!(
                    "{}={}·{}+{}",
                    name(i),
                    self.small(a).map_or("<big>".to_string(), |z| z.to_string()),
                    name(*u),
                    self.small(b).map_or("<big>".to_string(), |z| z.to_string())
                ),
                None => format!("{}=?", name(i)),
            },
        };
        let mut rows = std::collections::BTreeSet::new();
        for (i, d) in self.dom.iter().enumerate() {
            if !matches!(d, Dom::Val(_)) {
                eprintln!("open {}", show(i));
                rows.extend(self.var_cons[i].iter().copied());
            }
        }
        for ci in rows {
            let e = &self.program.constraints[ci];
            let mut parts: Vec<String> = Vec::new();
            for mt in &e.mul_terms {
                parts.push(format!(
                    "{}·[{}]·[{}]",
                    Fp::from_const(&mt.coeff, &self.p).to_decimal(),
                    show(self.index[&mt.left]),
                    show(self.index[&mt.right])
                ));
            }
            for lt in &e.linear_terms {
                parts.push(format!(
                    "{}·[{}]",
                    Fp::from_const(&lt.coeff, &self.p).to_decimal(),
                    show(self.index[&lt.var])
                ));
            }
            eprintln!(
                "row {ci}: {} + {} = 0",
                parts.join(" + "),
                Fp::from_const(&e.constant, &self.p).to_decimal()
            );
        }
    }

    /// Stop: two witnesses (or two projections) found, or the search gave up.
    fn done(&self) -> bool {
        self.found.len() >= 2 || self.proj_found.len() >= 2 || self.stuck.is_some()
    }

    fn propagate(&mut self) -> Result<(), Conflict> {
        while let Some(ci) = self.queue.pop() {
            self.queued[ci] = false;
            self.process(ci)?;
            self.steps += 1;
            if self.steps.is_multiple_of(4096)
                && self.deadline.is_some_and(|d| std::time::Instant::now() > d)
            {
                self.stuck = Some("time limit exhausted".into());
                // Abandon this branch; the caller sees `stuck` and stops.
                return Err(Conflict);
            }
        }
        Ok(())
    }

    fn undo(&mut self, mark: usize) {
        while self.trail.len() > mark {
            match self.trail.pop().unwrap() {
                Trail::Dom(v, d) => self.dom[v] = d,
                Trail::Alias(v, u) => {
                    self.alias[v] = None;
                    // LIFO: `v` was the last dependent pushed onto `u`.
                    let popped = self.deps[u].pop();
                    debug_assert_eq!(popped, Some(v));
                }
            }
        }
        for ci in self.queue.drain(..) {
            self.queued[ci] = false;
        }
    }

    /// Depth-first search. The recursion depth is about the sum, over split
    /// variables, of `log2` of their range widths (≈ 86 frames per 86-bit limb).
    fn dfs(&mut self) {
        if self.done() {
            return;
        }
        self.nodes += 1;
        if self.nodes > self.budget {
            self.stuck = Some(format!("node budget ({}) exhausted", self.budget));
            return;
        }
        if self.propagate().is_err() {
            return;
        }
        // Split the narrowest finite domain.
        let mut pick: Option<(usize, BigInt)> = None;
        let mut free = None;
        for (v, d) in self.dom.iter().enumerate() {
            match d {
                Dom::Range(lo, hi) => {
                    let w = hi - lo;
                    if pick.as_ref().is_none_or(|(_, pw)| &w < pw) {
                        pick = Some((v, w));
                    }
                }
                Dom::Free if self.alias[v].is_none() => free = Some(v),
                Dom::Free | Dom::Val(_) => {}
            }
        }
        let Some((v, _)) = pick else {
            if let Some(v) = free {
                if std::env::var_os("XARK_WS_DEBUG").is_some() {
                    self.dump();
                }
                // No finite domain to split: try `0` and `1` — two solutions prove
                // the circuit two-valued; anything less leaves the search incomplete.
                let name = self
                    .program
                    .vars
                    .iter()
                    .find(|x| x.id == self.ids[v])
                    .map(|x| x.name.clone())
                    .unwrap_or_default();
                self.incomplete = Some(format!("no finite domain for `{name}`"));
                for z in [0, 1] {
                    let mark = self.trail.len();
                    if self.narrow(v, BigInt::from(z), BigInt::from(z)).is_ok() {
                        self.dfs();
                    }
                    self.undo(mark);
                    if self.done() {
                        return;
                    }
                }
                return;
            }
            // Every variable fixed and every row re-checked by propagation.
            let vals: Vec<Fp> = (0..self.dom.len())
                .map(|v| match self.resolve(v) {
                    Resolved::Known(x) => x,
                    Resolved::Lin(..) => unreachable!("every representative is fixed"),
                })
                .collect();
            match &self.project {
                Some(proj) => {
                    let pv: Vec<Fp> = proj.iter().map(|&i| vals[i].clone()).collect();
                    if self.proj_found.first() != Some(&pv) {
                        self.proj_found.push(pv);
                    }
                }
                None => self.found.push(vals),
            }
            return;
        };
        if self.nodes == 1 && std::env::var_os("XARK_WS_DEBUG").is_some() {
            self.dump();
        }
        let Dom::Range(lo, hi) = self.dom[v].clone() else {
            unreachable!()
        };
        let mid = floor_div(&(&lo + &hi), &BigInt::from(2));
        for (a, b) in [(lo, mid.clone()), (mid + 1, hi)] {
            let mark = self.trail.len();
            if self.narrow(v, a, b).is_ok() {
                self.dfs();
            }
            self.undo(mark);
            if self.done() {
                return;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::FieldConst;
    use crate::primitive::{Expression, FieldSpec, LinearTerm, MulTerm, Var};

    fn var(id: u32, name: &str, role: VarRole) -> Var {
        Var {
            id,
            name: name.into(),
            role,
        }
    }

    fn expr(mul: &[(i64, u32, u32)], lin: &[(i64, u32)], k: i64) -> Expression {
        Expression {
            mul_terms: mul
                .iter()
                .map(|&(c, l, r)| MulTerm {
                    coeff: FieldConst::from_i64(c),
                    left: l,
                    right: r,
                })
                .collect(),
            linear_terms: lin
                .iter()
                .map(|&(c, v)| LinearTerm {
                    coeff: FieldConst::from_i64(c),
                    var: v,
                })
                .collect(),
            constant: FieldConst::from_i64(k),
            note: None,
        }
    }

    /// `x` (input) decomposed into 4 bits `b0..b3` (derived).
    fn bits4() -> PrimitiveProgram {
        let mut vars = vec![var(0, "x", VarRole::PrivateInput)];
        let mut cons = Vec::new();
        for i in 1..=4 {
            vars.push(var(i, &format!("b{}", i - 1), VarRole::Derived));
            cons.push(expr(&[(1, i, i)], &[(-1, i)], 0));
        }
        cons.push(expr(&[], &[(1, 1), (2, 2), (4, 3), (8, 4), (-1, 0)], 0));
        PrimitiveProgram {
            field: FieldSpec::bn254(),
            vars,
            constraints: cons,
            witness_gen: Vec::new(),
        }
    }

    fn run(p: &PrimitiveProgram, x: &str) -> WitnessSearch {
        search_witnesses(p, &BTreeMap::from([(0, x.to_string())]), 1000).unwrap()
    }

    #[test]
    fn decomposition_is_unique_in_range_and_unsat_outside() {
        let p = bits4();
        assert!(matches!(run(&p, "11"), WitnessSearch::Unique(_)));
        assert!(matches!(run(&p, "16"), WitnessSearch::None));
        assert!(matches!(run(&p, "-1"), WitnessSearch::None));
    }

    #[test]
    fn a_free_bit_is_two_valued() {
        let mut p = bits4();
        // Drop `b3` from the recomposition: it is only boolean, so two-valued.
        p.constraints[4] = expr(&[], &[(1, 1), (2, 2), (4, 3), (-1, 0)], 0);
        assert!(matches!(
            run(&p, "5"),
            WitnessSearch::Multiple { var: 4, .. }
        ));
    }

    #[test]
    fn inverse_or_zero_is_unique() {
        // out = 1 − x·inv, x·out = 0, inv·out = 0 (`emit_is_zero`), with p = x·inv.
        let vars = vec![
            var(0, "x", VarRole::PrivateInput),
            var(1, "inv", VarRole::Derived),
            var(2, "p", VarRole::Derived),
        ];
        let cons = vec![
            expr(&[(1, 0, 1)], &[(-1, 2)], 0),
            expr(&[(-1, 0, 2)], &[(1, 0)], 0),
            expr(&[(-1, 1, 2)], &[(1, 1)], 0),
        ];
        let p = PrimitiveProgram {
            field: FieldSpec::bn254(),
            vars,
            constraints: cons,
            witness_gen: Vec::new(),
        };
        assert!(matches!(run(&p, "0"), WitnessSearch::Unique(_)));
        assert!(matches!(run(&p, "7"), WitnessSearch::Unique(_)));
        // Without `inv·out = 0`, `x = 0` leaves `inv` free.
        let mut q = p;
        q.constraints.pop();
        assert!(matches!(
            run(&q, "0"),
            WitnessSearch::Multiple { var: 1, .. }
        ));
    }

    /// `a = q·b + r`, `q, r, b − 1 − r` 3-bit: integer division by a witness.
    #[test]
    fn division_by_witness_is_unique_and_rejects_zero() {
        // vars: 0 a, 1 b (inputs); 2 q, 3 r, 4 t; bits 5..14 (q, r, t).
        let mut vars = vec![
            var(0, "a", VarRole::PrivateInput),
            var(1, "b", VarRole::PrivateInput),
            var(2, "q", VarRole::Derived),
            var(3, "r", VarRole::Derived),
            var(4, "t", VarRole::Derived),
        ];
        let mut cons = vec![
            expr(&[(1, 2, 1)], &[(1, 3), (-1, 0)], 0),
            expr(&[], &[(1, 4), (1, 3), (-1, 1)], 1),
        ];
        for (k, of) in [2u32, 3, 4].into_iter().enumerate() {
            let base = 5 + 3 * k as u32;
            let mut lin = vec![(-1, of)];
            for i in 0..3 {
                vars.push(var(base + i, &format!("bit{}", base + i), VarRole::Derived));
                cons.push(expr(&[(1, base + i, base + i)], &[(-1, base + i)], 0));
                lin.push((1 << i, base + i));
            }
            cons.push(expr(&[], &lin, 0));
        }
        let p = PrimitiveProgram {
            field: FieldSpec::bn254(),
            vars,
            constraints: cons,
            witness_gen: Vec::new(),
        };
        let run2 = |a: &str, b: &str| {
            search_witnesses(&p, &BTreeMap::from([(0, a.into()), (1, b.into())]), 1000).unwrap()
        };
        match run2("7", "2") {
            WitnessSearch::Unique(w) => {
                assert_eq!(w[&2].to_decimal(), "3");
                assert_eq!(w[&3].to_decimal(), "1");
            }
            other => panic!("{other:?}"),
        }
        assert!(matches!(run2("7", "0"), WitnessSearch::None));
        // 7 = q·1 + r has no 3-bit `q` with `r < 1`… except q = 7.
        assert!(matches!(run2("7", "1"), WitnessSearch::Unique(_)));
        assert!(matches!(run2("15", "1"), WitnessSearch::None));
    }
}
