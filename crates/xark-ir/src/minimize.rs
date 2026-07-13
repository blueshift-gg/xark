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
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

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
/// value canonically in `[0, r)`, no zero coefficients.
#[derive(Clone)]
struct Lc {
    k: BigInt,
    t: BTreeMap<VarId, BigInt>,
}

fn rm(x: BigInt, r: &BigInt) -> BigInt {
    let m = x % r;
    if m < BigInt::ZERO {
        m + r
    } else {
        m
    }
}

/// Modular inverse over the prime field (`x^(r-2) mod r`, Fermat).
fn inv(x: &BigInt, r: &BigInt) -> BigInt {
    let base = rm(x.clone(), r);
    base.modpow(&(r - 2), r)
}

impl Lc {
    fn from_ir(lc: &LinearCombination, r: &BigInt) -> Lc {
        let mut t = BTreeMap::new();
        for term in &lc.terms {
            let c = rm(term.coeff.big(), r);
            if c != BigInt::ZERO {
                // A repeated var (shouldn't occur post-`simplified`) accumulates.
                let e = t.entry(term.var).or_insert_with(|| BigInt::ZERO);
                *e = rm(std::mem::take(e) + c, r);
                if *e == BigInt::ZERO {
                    t.remove(&term.var);
                }
            }
        }
        Lc {
            k: rm(lc.constant.big(), r),
            t,
        }
    }

    fn is_const(&self) -> bool {
        self.t.is_empty()
    }

    fn scale(&self, m: &BigInt, r: &BigInt) -> Lc {
        let mut t = BTreeMap::new();
        for (v, c) in &self.t {
            let nc = rm(c * m, r);
            if nc != BigInt::ZERO {
                t.insert(*v, nc);
            }
        }
        Lc {
            k: rm(&self.k * m, r),
            t,
        }
    }

    /// `self - other`.
    fn sub(&self, other: &Lc, r: &BigInt) -> Lc {
        let mut t = self.t.clone();
        for (v, c) in &other.t {
            let e = t.entry(*v).or_insert_with(|| BigInt::ZERO);
            *e = rm(std::mem::take(e) - c, r);
            if *e == BigInt::ZERO {
                t.remove(v);
            }
        }
        Lc {
            k: rm(&self.k - &other.k, r),
            t,
        }
    }

    fn to_ir(&self) -> LinearCombination {
        let mut terms: Vec<Term> = self
            .t
            .iter()
            .map(|(v, c)| Term {
                coeff: FieldConst::from_bigint(c.clone()),
                var: *v,
            })
            .collect();
        terms.sort_by_key(|t| t.var);
        LinearCombination {
            constant: FieldConst::from_bigint(self.k.clone()),
            terms,
        }
    }
}

/// The linear relation a constraint `a·b = c` imposes when it is *not* genuinely
/// quadratic — i.e. when `a` or `b` is a bare constant, so `a·b` is linear.
/// Returns `α·b − c` (or `β·a − c`), an `Lc` that the circuit forces to zero.
fn relation(a: &Lc, b: &Lc, c: &Lc, r: &BigInt) -> Option<Lc> {
    if a.is_const() {
        Some(b.scale(&a.k, r).sub(c, r))
    } else if b.is_const() {
        Some(a.scale(&b.k, r).sub(c, r))
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
    let Ok(r) = mod_dec.parse::<BigInt>() else {
        return prog.clone();
    };

    let vis: BTreeMap<VarId, Visibility> = prog
        .variables
        .iter()
        .map(|v| (v.id, v.visibility.clone()))
        .collect();

    // Parse constraints; `None` marks an eliminated/trivial (dead) constraint.
    let mut cons: Vec<Option<[Lc; 3]>> = prog
        .constraints
        .iter()
        .map(|c| {
            Some([
                Lc::from_ir(&c.a, &r),
                Lc::from_ir(&c.b, &r),
                Lc::from_ir(&c.c, &r),
            ])
        })
        .collect();

    // Occurrence index: var → constraint indices that reference it.
    let mut occ: BTreeMap<VarId, BTreeSet<usize>> = BTreeMap::new();
    let con_vars = |c: &[Lc; 3]| -> BTreeSet<VarId> {
        let mut s = BTreeSet::new();
        for lc in c {
            s.extend(lc.t.keys().copied());
        }
        s
    };
    for (i, c) in cons.iter().enumerate() {
        if let Some(c) = c {
            for v in con_vars(c) {
                occ.entry(v).or_default().insert(i);
            }
        }
    }

    let mut queue: VecDeque<usize> = (0..cons.len()).collect();
    let mut in_queue = vec![true; cons.len()];
    let mut eliminated: BTreeSet<VarId> = BTreeSet::new();

    while let Some(i) = queue.pop_front() {
        in_queue[i] = false;
        let Some(c) = &cons[i] else { continue };
        let Some(rel) = relation(&c[0], &c[1], &c[2], &r) else {
            continue;
        };

        // Trivial `0 = 0` (or `0 = k` with no vars): drop it. A `0 = nonzero`
        // (infeasible) constraint is left in place so the backend still rejects it.
        if rel.t.is_empty() {
            if rel.k == BigInt::ZERO {
                for v in con_vars(c) {
                    if let Some(s) = occ.get_mut(&v) {
                        s.remove(&i);
                    }
                }
                cons[i] = None;
            }
            continue;
        }

        // Pick the lowest-id Internal var to eliminate (any nonzero coeff is
        // invertible in the prime field).
        let Some((&v, coeff)) = rel
            .t
            .iter()
            .find(|(var, _)| matches!(vis.get(var), Some(Visibility::Internal)))
        else {
            continue;
        };

        // v = -(rel without v) / coeff.
        let mut rest = rel.clone();
        rest.t.remove(&v);
        let factor = rm(-inv(coeff, &r), &r);
        let vlc = rest.scale(&factor, &r);

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

        // Retire the defining constraint.
        for w in con_vars(c) {
            if let Some(s) = occ.get_mut(&w) {
                s.remove(&i);
            }
        }
        cons[i] = None;
        eliminated.insert(v);

        // Substitute v → vlc everywhere it appears.
        let sites: Vec<usize> = occ
            .remove(&v)
            .map(|s| s.into_iter().collect())
            .unwrap_or_default();
        for j in sites {
            let Some(cj) = &mut cons[j] else { continue };
            for lc in cj.iter_mut() {
                let Some(m) = lc.t.remove(&v) else { continue };
                lc.k = rm(&lc.k + &m * &vlc.k, &r);
                for (var, co) in &vlc.t {
                    let e = lc.t.entry(*var).or_insert_with(|| BigInt::ZERO);
                    *e = rm(std::mem::take(e) + &m * co, &r);
                    if *e == BigInt::ZERO {
                        lc.t.remove(var);
                    } else {
                        occ.entry(*var).or_default().insert(j);
                    }
                }
            }
            if !in_queue[j] {
                in_queue[j] = true;
                queue.push_back(j);
            }
        }
    }

    // Fixpoint invariant (`XARK_VERIFY`): after minimization no surviving
    // constraint may still *linearly define* an eliminable (`Internal`) variable —
    // if one did, the loop missed an elimination and the output isn't optimal under
    // the rule set. This makes R1CS-optimality a checked property, not a claim.
    if crate::dbg_flag("XARK_VERIFY") {
        for c in cons.iter().flatten() {
            if let Some(rel) = relation(&c[0], &c[1], &c[2], &r) {
                if let Some((&v, coeff)) = rel
                    .t
                    .iter()
                    .find(|(var, _)| matches!(vis.get(var), Some(Visibility::Internal)))
                {
                    // Fixpoint is relative to the fill-in guard: a survivor is only
                    // a missed elimination if its replacement LC is within budget.
                    let mut rest = rel.clone();
                    rest.t.remove(&v);
                    let vlc = rest.scale(&rm(-inv(coeff, &r), &r), &r);
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

    // Surviving vars: every input, plus any Internal still referenced.
    let mut referenced: BTreeSet<VarId> = BTreeSet::new();
    for c in cons.iter().flatten() {
        referenced.extend(con_vars(c));
    }
    let variables = prog
        .variables
        .iter()
        .filter(|v| !eliminated.contains(&v.id))
        .filter(|v| v.visibility != Visibility::Internal || referenced.contains(&v.id))
        .cloned()
        .collect();

    let constraints = cons
        .iter()
        .flatten()
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

    fn var(id: u32, vis: Visibility) -> Variable {
        Variable {
            id,
            name: format!("v{id}"),
            visibility: vis,
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
