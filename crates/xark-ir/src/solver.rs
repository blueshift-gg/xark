//! Reference witness solver + constraint checker for the [primitive IR].
//!
//! This is a *reference implementation* of what the backend's lowering must do:
//! given values for the input variables, run the witness-generation program to
//! fill every derived/hint variable, then check that all AssertZero constraints
//! evaluate to zero. It exists so gadgets can be validated end-to-end (e.g.
//! against a known SHA-256 test vector) purely from the emitted IR — no proving
//! system required.
//!
//! [primitive IR]: crate::primitive

use std::collections::BTreeMap;

use num_bigint::BigUint;
use num_traits::{One, Zero};

use crate::linear_combination::{LinearCombination, VarId};
use crate::primitive::{Expression, PrimitiveProgram, WitnessGen};

/// A field element in `[0, modulus)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fp {
    value: BigUint,
    modulus: BigUint,
}

impl Fp {
    fn new(value: BigUint, modulus: &BigUint) -> Self {
        Fp {
            value: value % modulus,
            modulus: modulus.clone(),
        }
    }

    fn zero(modulus: &BigUint) -> Self {
        Fp {
            value: BigUint::zero(),
            modulus: modulus.clone(),
        }
    }

    /// Reduce a signed decimal string into the field.
    fn from_decimal(s: &str, modulus: &BigUint) -> Self {
        let trimmed = s.trim();
        if let Some(mag) = trimmed.strip_prefix('-') {
            let m = BigUint::parse_bytes(mag.as_bytes(), 10).unwrap_or_else(BigUint::zero) % modulus;
            // -m mod p = p - (m mod p)  (0 stays 0)
            let v = if m.is_zero() {
                BigUint::zero()
            } else {
                modulus - m
            };
            Fp::new(v, modulus)
        } else {
            let m = BigUint::parse_bytes(trimmed.as_bytes(), 10).unwrap_or_else(BigUint::zero);
            Fp::new(m, modulus)
        }
    }

    fn add(&self, other: &Fp) -> Fp {
        Fp::new(&self.value + &other.value, &self.modulus)
    }

    fn mul(&self, other: &Fp) -> Fp {
        Fp::new(&self.value * &other.value, &self.modulus)
    }

    /// Multiplicative inverse via Fermat's little theorem (`a^(p-2)`).
    fn inverse(&self) -> Option<Fp> {
        if self.value.is_zero() {
            return None;
        }
        let exp = &self.modulus - BigUint::from(2u32);
        Some(Fp {
            value: self.value.modpow(&exp, &self.modulus),
            modulus: self.modulus.clone(),
        })
    }

    fn neg(&self) -> Fp {
        if self.value.is_zero() {
            self.clone()
        } else {
            Fp {
                value: &self.modulus - &self.value,
                modulus: self.modulus.clone(),
            }
        }
    }

    fn sub(&self, other: &Fp) -> Fp {
        self.add(&other.neg())
    }

    fn is_zero(&self) -> bool {
        self.value.is_zero()
    }

    fn bit(&self, i: usize) -> Fp {
        let b = if (&self.value >> i) & BigUint::one() == BigUint::one() {
            BigUint::one()
        } else {
            BigUint::zero()
        };
        Fp::new(b, &self.modulus)
    }

    pub fn to_decimal(&self) -> String {
        self.value.to_str_radix(10)
    }

    fn to_biguint(&self) -> BigUint {
        self.value.clone()
    }
}

/// Errors from solving or checking.
#[derive(Debug)]
pub enum SolveError {
    MissingInput(VarId),
    DivisionByZero,
    NonInvertible,
    /// A hint's inputs were out of the range it assumes (e.g. limbs that do not
    /// satisfy `< modulus`), so its witness computation would underflow. Returned
    /// instead of panicking, so adversarial `--input` cannot crash the prover.
    MalformedHint(&'static str),
    /// A constraint (by index) was not satisfied.
    ConstraintFailed(usize),
    /// The program's field modulus is missing, unparseable, or `< 2` — the
    /// arithmetic (`% modulus`) would panic. Returned instead of panicking so a
    /// malformed artifact cannot crash the prover.
    MalformedModulus,
}

/// Largest `limb_bits` a hint may declare. Non-native limbs are 86 bits; this
/// bound stops an adversarial artifact from requesting a multi-gigabyte
/// BigUint shift (`1 << limb_bits`) and OOM-ing the prover.
const MAX_LIMB_BITS: u32 = 128;

fn modulus_of(program: &PrimitiveProgram) -> Result<BigUint, SolveError> {
    let m = BigUint::parse_bytes(program.field.modulus_decimal.as_bytes(), 10)
        .ok_or(SolveError::MalformedModulus)?;
    if m < BigUint::from(2u32) {
        return Err(SolveError::MalformedModulus);
    }
    Ok(m)
}

fn eval_lc(lc: &LinearCombination, assign: &BTreeMap<VarId, Fp>, modulus: &BigUint) -> Fp {
    let mut acc = Fp::from_decimal(&lc.constant.decimal, modulus);
    for term in &lc.terms {
        let coeff = Fp::from_decimal(&term.coeff.decimal, modulus);
        let var = assign
            .get(&term.var)
            .cloned()
            .unwrap_or_else(|| Fp::zero(modulus));
        acc = acc.add(&coeff.mul(&var));
    }
    acc
}

fn eval_expression(expr: &Expression, assign: &BTreeMap<VarId, Fp>, modulus: &BigUint) -> Fp {
    let mut acc = Fp::from_decimal(&expr.constant.decimal, modulus);
    for lt in &expr.linear_terms {
        let coeff = Fp::from_decimal(&lt.coeff.decimal, modulus);
        let v = assign.get(&lt.var).cloned().unwrap_or_else(|| Fp::zero(modulus));
        acc = acc.add(&coeff.mul(&v));
    }
    for mt in &expr.mul_terms {
        let coeff = Fp::from_decimal(&mt.coeff.decimal, modulus);
        let l = assign.get(&mt.left).cloned().unwrap_or_else(|| Fp::zero(modulus));
        let r = assign.get(&mt.right).cloned().unwrap_or_else(|| Fp::zero(modulus));
        acc = acc.add(&coeff.mul(&l).mul(&r));
    }
    acc
}

/// Run the witness-generation program, returning the full variable assignment.
pub fn solve(
    program: &PrimitiveProgram,
    inputs: &BTreeMap<VarId, String>,
) -> Result<BTreeMap<VarId, Fp>, SolveError> {
    let modulus = modulus_of(program)?;
    let mut assign: BTreeMap<VarId, Fp> = BTreeMap::new();

    // Seed inputs.
    for var in &program.vars {
        if matches!(
            var.role,
            crate::primitive::VarRole::PublicInput | crate::primitive::VarRole::PrivateInput
        ) {
            let decimal = inputs.get(&var.id).ok_or(SolveError::MissingInput(var.id))?;
            assign.insert(var.id, Fp::from_decimal(decimal, &modulus));
        }
    }

    // Run the hint program in order.
    for op in &program.witness_gen {
        match op {
            WitnessGen::Product { out, left, right } => {
                let l = eval_lc(left, &assign, &modulus);
                let r = eval_lc(right, &assign, &modulus);
                assign.insert(*out, l.mul(&r));
            }
            WitnessGen::Linear { out, lc } => {
                let v = eval_lc(lc, &assign, &modulus);
                assign.insert(*out, v);
            }
            WitnessGen::Xor { out, a, b } => {
                let av = eval_lc(a, &assign, &modulus);
                let bv = eval_lc(b, &assign, &modulus);
                let ab = av.mul(&bv);
                // a + b - 2ab
                let v = av.add(&bv).add(&ab.mul(&Fp::from_decimal("-2", &modulus)));
                assign.insert(*out, v);
            }
            WitnessGen::Or { out, a, b } => {
                let av = eval_lc(a, &assign, &modulus);
                let bv = eval_lc(b, &assign, &modulus);
                let ab = av.mul(&bv);
                // a + b - ab
                let v = av.add(&bv).add(&ab.mul(&Fp::from_decimal("-1", &modulus)));
                assign.insert(*out, v);
            }
            WitnessGen::Inverse { out, input } => {
                let v = eval_lc(input, &assign, &modulus);
                let inv = v.inverse().ok_or(SolveError::NonInvertible)?;
                assign.insert(*out, inv);
            }
            WitnessGen::InverseOrZero { out, input } => {
                // `x⁻¹` when `x ≠ 0`, else `0`. The zero case is fine: the
                // is_zero gadget multiplies this value by `x`, so it is
                // unconstrained (and irrelevant) exactly when `x = 0`.
                let v = eval_lc(input, &assign, &modulus);
                let inv = v.inverse().unwrap_or_else(|| Fp::zero(&modulus));
                assign.insert(*out, inv);
            }
            WitnessGen::Bit { out, input, index } => {
                let v = eval_lc(input, &assign, &modulus);
                assign.insert(*out, v.bit(*index as usize));
            }
            WitnessGen::DivRem { q, r, num, den } => {
                let n = eval_lc(num, &assign, &modulus);
                let d = eval_lc(den, &assign, &modulus);
                if d.is_zero() {
                    return Err(SolveError::DivisionByZero);
                }
                let quotient = &n.value / &d.value;
                let remainder = &n.value % &d.value;
                assign.insert(*q, Fp::new(quotient, &modulus));
                assign.insert(*r, Fp::new(remainder, &modulus));
            }
            WitnessGen::MulModDivMod {
                q,
                r,
                a,
                b,
                modulus: m,
                limb_bits,
            } => {
                if *limb_bits > MAX_LIMB_BITS {
                    return Err(SolveError::MalformedHint("limb_bits exceeds MAX_LIMB_BITS"));
                }
                let recompose = |limbs: &[LinearCombination]| -> BigUint {
                    let mut acc = BigUint::zero();
                    for (i, lc) in limbs.iter().enumerate() {
                        let v = eval_lc(lc, &assign, &modulus).to_biguint();
                        acc += v << (*limb_bits as usize * i);
                    }
                    acc
                };
                let a_big = recompose(a);
                let b_big = recompose(b);
                let m_big = recompose(m);
                if m_big.is_zero() {
                    return Err(SolveError::DivisionByZero);
                }
                let p = &a_big * &b_big;
                let quotient = &p / &m_big;
                let remainder = &p % &m_big;
                let mask = (BigUint::one() << *limb_bits as usize) - BigUint::one();
                for (i, &out) in q.iter().enumerate() {
                    let limb = (&quotient >> (*limb_bits as usize * i)) & &mask;
                    assign.insert(out, Fp::new(limb, &modulus));
                }
                for (i, &out) in r.iter().enumerate() {
                    let limb = (&remainder >> (*limb_bits as usize * i)) & &mask;
                    assign.insert(out, Fp::new(limb, &modulus));
                }
            }
            WitnessGen::ModInverse {
                out,
                a,
                modulus: m,
                limb_bits,
            } => {
                if *limb_bits > MAX_LIMB_BITS {
                    return Err(SolveError::MalformedHint("limb_bits exceeds MAX_LIMB_BITS"));
                }
                let recompose = |limbs: &[LinearCombination]| -> BigUint {
                    let mut acc = BigUint::zero();
                    for (i, lc) in limbs.iter().enumerate() {
                        let v = eval_lc(lc, &assign, &modulus).to_biguint();
                        acc += v << (*limb_bits as usize * i);
                    }
                    acc
                };
                let m_big = recompose(m);
                // Adversarial limbs could recompose to a degenerate modulus; guard
                // before the `%` (division by zero) and the `M-2` (underflow) below.
                if m_big < BigUint::from(2u32) {
                    return Err(SolveError::MalformedHint("mod_inverse: modulus < 2"));
                }
                let a_big = recompose(a) % &m_big;
                if a_big.is_zero() {
                    return Err(SolveError::DivisionByZero);
                }
                // Fermat inverse A^(M-2) mod M (M prime — holds for the secp256k1
                // base/scalar fields this hint targets).
                let w = a_big.modpow(&(&m_big - BigUint::from(2u32)), &m_big);
                let mask = (BigUint::one() << *limb_bits as usize) - BigUint::one();
                for (i, &o) in out.iter().enumerate() {
                    let limb = (&w >> (*limb_bits as usize * i)) & &mask;
                    assign.insert(o, Fp::new(limb, &modulus));
                }
            }
            WitnessGen::Sub2 {
                qabs,
                r,
                a,
                b,
                c,
                modulus: m,
                limb_bits,
            } => {
                if *limb_bits > MAX_LIMB_BITS {
                    return Err(SolveError::MalformedHint("limb_bits exceeds MAX_LIMB_BITS"));
                }
                let recompose = |limbs: &[LinearCombination]| -> BigUint {
                    let mut acc = BigUint::zero();
                    for (i, lc) in limbs.iter().enumerate() {
                        let v = eval_lc(lc, &assign, &modulus).to_biguint();
                        acc += v << (*limb_bits as usize * i);
                    }
                    acc
                };
                let a_big = recompose(a);
                let b_big = recompose(b);
                let c_big = recompose(c);
                let m_big = recompose(m);
                if m_big.is_zero() {
                    return Err(SolveError::DivisionByZero);
                }
                // s = a + 2m - b - c ∈ [2, 3m) (positive; a,b,c < m). Then r = s mod m,
                // and qabs = 2 - (s / m) ∈ {0,1,2} so that a + qabs·m = b + c + r.
                // With honest, range-checked limbs a,b,c < m these never underflow;
                // adversarial `--input` might, so guard each subtraction rather
                // than let BigUint underflow-panic.
                let lhs = &a_big + &m_big + &m_big;
                let rhs = &b_big + &c_big;
                if lhs < rhs {
                    return Err(SolveError::MalformedHint("sub2: a + 2m < b + c"));
                }
                let s = lhs - rhs;
                let remainder = &s % &m_big;
                let q_s = &s / &m_big;
                if q_s > BigUint::from(2u32) {
                    return Err(SolveError::MalformedHint(
                        "sub2: quotient out of range (inputs >= modulus)",
                    ));
                }
                let q_abs = BigUint::from(2u32) - &q_s;
                assign.insert(*qabs, Fp::new(q_abs, &modulus));
                let mask = (BigUint::one() << *limb_bits as usize) - BigUint::one();
                for (i, &out) in r.iter().enumerate() {
                    let limb = (&remainder >> (*limb_bits as usize * i)) & &mask;
                    assign.insert(out, Fp::new(limb, &modulus));
                }
            }
        }
    }

    Ok(assign)
}

/// Construct a field element from a decimal string against a program's field
/// (for tests / tooling that need to inject specific witness values).
pub fn fp_from_decimal(s: &str, program: &PrimitiveProgram) -> Fp {
    Fp::from_decimal(s, &modulus_of(program).expect("valid field modulus"))
}

/// Check that every constraint evaluates to zero under `assign`.
pub fn check(program: &PrimitiveProgram, assign: &BTreeMap<VarId, Fp>) -> Result<(), SolveError> {
    let modulus = modulus_of(program)?;
    for (i, c) in program.constraints.iter().enumerate() {
        if !eval_expression(c, assign, &modulus).is_zero() {
            return Err(SolveError::ConstraintFailed(i));
        }
    }
    Ok(())
}

/// Convenience: solve the witness from inputs and check all constraints hold.
pub fn solve_and_check(
    program: &PrimitiveProgram,
    inputs: &BTreeMap<VarId, String>,
) -> Result<BTreeMap<VarId, Fp>, SolveError> {
    let assign = solve(program, inputs)?;
    check(program, &assign)?;
    Ok(assign)
}

// ===========================================================================
// Under-constraint (soundness smoke-test) analyzer.
// ===========================================================================

/// A derived variable the analyzer could not prove is uniquely pinned by the
/// constraints (holding every other variable at the honest witness). This is a
/// potential under-constraint — a value a malicious prover might be able to
/// change without violating any constraint.
#[derive(Debug, Clone)]
pub struct UnderConstrained {
    pub var: VarId,
    pub name: String,
    pub reason: String,
}

/// Reduce a constraint to the univariate polynomial `a·v² + b·v + c` obtained by
/// fixing every variable except `v` at the honest assignment.
fn univariate(
    expr: &Expression,
    v: VarId,
    assign: &BTreeMap<VarId, Fp>,
    modulus: &BigUint,
) -> (Fp, Fp, Fp) {
    let zero = || Fp::zero(modulus);
    let get = |id: VarId| assign.get(&id).cloned().unwrap_or_else(zero);
    let (mut a, mut b, mut c) = (zero(), zero(), zero());
    for mt in &expr.mul_terms {
        let coeff = Fp::from_decimal(&mt.coeff.decimal, modulus);
        match (mt.left == v, mt.right == v) {
            (true, true) => a = a.add(&coeff),
            (true, false) => b = b.add(&coeff.mul(&get(mt.right))),
            (false, true) => b = b.add(&coeff.mul(&get(mt.left))),
            (false, false) => c = c.add(&coeff.mul(&get(mt.left)).mul(&get(mt.right))),
        }
    }
    for lt in &expr.linear_terms {
        let coeff = Fp::from_decimal(&lt.coeff.decimal, modulus);
        if lt.var == v {
            b = b.add(&coeff);
        } else {
            c = c.add(&coeff.mul(&get(lt.var)));
        }
    }
    c = c.add(&Fp::from_decimal(&expr.constant.decimal, modulus));
    (a, b, c)
}

/// Check every `Derived` variable is uniquely determined by the constraints,
/// given the honest witness `assign` (which must satisfy the program).
///
/// This is a *necessary* soundness check, not a full proof: it catches free /
/// two-valued variables (the dominant under-constraint bug class) by testing,
/// for each variable, whether any value other than the honest one also
/// satisfies every constraint that references it (all other variables fixed). A
/// variable pinned by a linear constraint is uniquely determined; one pinned
/// only by quadratics is checked against the quadratics' second roots (Vieta).
pub fn analyze_underconstrained(
    program: &PrimitiveProgram,
    assign: &BTreeMap<VarId, Fp>,
) -> Vec<UnderConstrained> {
    use crate::primitive::VarRole;
    let modulus = modulus_of(program).expect("valid field modulus");

    // Index: variable -> indices of constraints that reference it.
    let mut refs: BTreeMap<VarId, Vec<usize>> = BTreeMap::new();
    for (i, expr) in program.constraints.iter().enumerate() {
        let mut seen = std::collections::BTreeSet::new();
        for mt in &expr.mul_terms {
            seen.insert(mt.left);
            seen.insert(mt.right);
        }
        for lt in &expr.linear_terms {
            seen.insert(lt.var);
        }
        for v in seen {
            refs.entry(v).or_default().push(i);
        }
    }

    let mut out = Vec::new();
    for var in &program.vars {
        if !matches!(var.role, VarRole::Derived) {
            continue;
        }
        let v = var.id;
        let alpha = assign.get(&v).cloned().unwrap_or_else(|| Fp::zero(&modulus));
        let Some(cons) = refs.get(&v) else {
            out.push(UnderConstrained {
                var: v,
                name: var.name.clone(),
                reason: "no constraint references this variable".into(),
            });
            continue;
        };

        let mut pinned_linear = false;
        let mut restricted = false;
        let mut candidates: Vec<Fp> = Vec::new();
        for &ci in cons {
            let (a, b, c) = univariate(&program.constraints[ci], v, assign, &modulus);
            let _ = &c;
            if a.is_zero() && b.is_zero() {
                continue; // this constraint does not restrict v
            }
            restricted = true;
            if a.is_zero() {
                pinned_linear = true; // linear (b != 0): unique root
                break;
            }
            // Quadratic: the other root is (-b/a) - alpha (Vieta).
            let inv_a = a.inverse().expect("a != 0 in quadratic branch");
            candidates.push(b.neg().mul(&inv_a).sub(&alpha));
        }
        if pinned_linear {
            continue;
        }
        if !restricted {
            out.push(UnderConstrained {
                var: v,
                name: var.name.clone(),
                reason: "variable's coefficient is zero in every referencing constraint (free)".into(),
            });
            continue;
        }
        // Only quadratic pins: does any second root satisfy ALL referencing
        // constraints? If so, v is two-valued (under-constrained).
        for beta in &candidates {
            if *beta == alpha {
                continue;
            }
            let satisfies_all = cons.iter().all(|&ci| {
                let (a, b, c) = univariate(&program.constraints[ci], v, assign, &modulus);
                a.mul(beta).mul(beta).add(&b.mul(beta)).add(&c).is_zero()
            });
            if satisfies_all {
                out.push(UnderConstrained {
                    var: v,
                    name: var.name.clone(),
                    reason: "a different value also satisfies all its constraints (two-valued)".into(),
                });
                break;
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::primitive::{FieldSpec, PrimitiveProgram};

    fn program_with_modulus(modulus_decimal: &str) -> PrimitiveProgram {
        PrimitiveProgram {
            field: FieldSpec {
                name: "test".into(),
                modulus_decimal: modulus_decimal.into(),
            },
            vars: vec![],
            constraints: vec![],
            witness_gen: vec![],
        }
    }

    /// A malformed field modulus (`0`, `1`, or unparseable) is a clean
    /// `MalformedModulus` error, not a `% 0` / `.expect` panic — adversarial
    /// artifacts must not crash the prover.
    #[test]
    fn malformed_modulus_is_rejected_not_panicked() {
        for m in ["0", "1", "", "not-a-number"] {
            let program = program_with_modulus(m);
            assert!(
                matches!(solve(&program, &BTreeMap::new()), Err(SolveError::MalformedModulus)),
                "modulus {m:?} must be rejected"
            );
        }
        // A valid modulus still solves the (trivial) program.
        let ok = program_with_modulus("21888242871839275222246405745257275088548364400416034343698204186575808495617");
        assert!(solve(&ok, &BTreeMap::new()).is_ok());
    }
}
