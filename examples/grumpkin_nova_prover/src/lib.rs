//! Host-side **Nova folding prover** over the BN254↔Grumpkin cycle.
//!
//! Extracts a Xark circuit's R1CS `(A,B,C)` and folds committed **relaxed**
//! instances `Az∘Bz = u·Cz + E`:
//! - `eval_lc` / `abc` evaluate the constraint system on a witness (`z`, `u`);
//! - [`is_satisfied`] checks the relaxed relation;
//! - [`fold`] computes the cross-term `T`, folds two instances with challenge
//!   `r` (`u += r·u2`, `z += r·z2`, `E = E1 + r·T + r²·E2`), and the folded
//!   instance *satisfies the relaxed R1CS* — the Nova correctness anchor;
//! - [`commit_w`]/[`commit_e`] are Grumpkin Pedersen commitments. Because they're
//!   homomorphic, `comm_W1 + r·comm_W2` and `comm_E1 + r·comm_T + r²·comm_E2` are
//!   exactly what the `grumpkin_nova_fold` circuit verifies in-circuit.
//!
//! Grumpkin (`y² = x³ − 17`) has coordinates in `Fr_BN254` — the R1CS field — so
//! the group ops are implemented directly over `Fr`, no `ark-grumpkin` (and no
//! ark-version juggling with `xark-ir`). Its scalar field is `Fq_BN254 > r`, so
//! an `Fr` witness value is always a valid Grumpkin scalar.

use ark_bn254::{Fq, Fr};
use ark_ff::{BigInteger, Field, PrimeField, Zero};
use num_bigint::{BigUint, Sign};
use std::collections::BTreeMap;
use std::str::FromStr;
use xark_ir::field::FieldConst;
use xark_ir::linear_combination::{LinearCombination, VarId};
use xark_ir::r1cs::R1csProgram;

// ===================== R1CS over Fr =====================

/// A (possibly negative) R1CS coefficient into `Fr`.
fn fr_from_fc(fc: &FieldConst) -> Fr {
    let (sign, bytes) = fc.big().to_bytes_le();
    let mag = Fr::from_le_bytes_mod_order(&bytes);
    if sign == Sign::Minus { -mag } else { mag }
}

/// Evaluate a linear combination on `(z, u)`; the LC constant is the coefficient
/// of the relaxation / one-wire `u`.
fn eval_lc(lc: &LinearCombination, z: &BTreeMap<VarId, Fr>, u: Fr) -> Fr {
    let mut acc = fr_from_fc(&lc.constant) * u;
    for t in &lc.terms {
        acc += fr_from_fc(&t.coeff) * z.get(&t.var).copied().unwrap_or_else(Fr::zero);
    }
    acc
}

fn abc(r1cs: &R1csProgram, z: &BTreeMap<VarId, Fr>, u: Fr) -> (Vec<Fr>, Vec<Fr>, Vec<Fr>) {
    let mut a = Vec::new();
    let mut b = Vec::new();
    let mut c = Vec::new();
    for con in &r1cs.constraints {
        a.push(eval_lc(&con.a, z, u));
        b.push(eval_lc(&con.b, z, u));
        c.push(eval_lc(&con.c, z, u));
    }
    (a, b, c)
}

/// A committed relaxed-R1CS instance's *opening*: witness `z`, relaxation `u`,
/// error vector `E` (one entry per constraint).
#[derive(Clone)]
pub struct Relaxed {
    pub z: BTreeMap<VarId, Fr>,
    pub u: Fr,
    pub e: Vec<Fr>,
}

impl Relaxed {
    /// A fresh (strict) instance from a satisfying witness: `u = 1`, `E = 0`.
    pub fn fresh(r1cs: &R1csProgram, z: BTreeMap<VarId, Fr>) -> Self {
        Relaxed {
            z,
            u: Fr::from(1u64),
            e: vec![Fr::zero(); r1cs.constraints.len()],
        }
    }
}

/// `Az∘Bz == u·Cz + E` for every constraint.
pub fn is_satisfied(r1cs: &R1csProgram, inst: &Relaxed) -> bool {
    let (a, b, c) = abc(r1cs, &inst.z, inst.u);
    (0..r1cs.constraints.len()).all(|k| a[k] * b[k] == inst.u * c[k] + inst.e[k])
}

/// Fold two relaxed instances with challenge `r`; returns the folded instance
/// and the cross-term `T` (whose commitment the circuit consumes as `comm_T`).
pub fn fold(r1cs: &R1csProgram, i1: &Relaxed, i2: &Relaxed, r: Fr) -> (Relaxed, Vec<Fr>) {
    let (a1, b1, c1) = abc(r1cs, &i1.z, i1.u);
    let (a2, b2, c2) = abc(r1cs, &i2.z, i2.u);
    let m = r1cs.constraints.len();
    let t: Vec<Fr> = (0..m)
        .map(|k| a1[k] * b2[k] + a2[k] * b1[k] - i1.u * c2[k] - i2.u * c1[k])
        .collect();

    let u = i1.u + r * i2.u;
    let mut z = BTreeMap::new();
    for v in &r1cs.variables {
        let v1 = i1.z.get(&v.id).copied().unwrap_or_else(Fr::zero);
        let v2 = i2.z.get(&v.id).copied().unwrap_or_else(Fr::zero);
        z.insert(v.id, v1 + r * v2);
    }
    let e: Vec<Fr> = (0..m)
        .map(|k| i1.e[k] + r * t[k] + r * r * i2.e[k])
        .collect();
    (Relaxed { z, u, e }, t)
}

/// Run the folding **stepping loop**: start from the first instance as the
/// running relaxed accumulator, then fold each subsequent fresh instance in with
/// its challenge. The returned accumulator satisfies the relaxed R1CS iff every
/// step folded a satisfying instance — the invariant an IVC maintains across
/// steps. (`challenges.len() + 1 == steps.len()`.)
pub fn run_ivc(r1cs: &R1csProgram, steps: &[BTreeMap<VarId, Fr>], challenges: &[Fr]) -> Relaxed {
    assert_eq!(challenges.len() + 1, steps.len(), "one challenge per fold");
    let mut acc = Relaxed::fresh(r1cs, steps[0].clone());
    for i in 1..steps.len() {
        let fresh = Relaxed::fresh(r1cs, steps[i].clone());
        acc = fold(r1cs, &acc, &fresh, challenges[i - 1]).0;
    }
    acc
}

// ============ Grumpkin (y² = x³ − 17) Pedersen commitment over Fr ============

/// A Grumpkin point: `Some((x, y))` or `None` for the identity ∞.
pub type Commitment = Option<(Fr, Fr)>;

fn g_double(p: (Fr, Fr)) -> Commitment {
    let (x, y) = p;
    if y.is_zero() {
        return None;
    }
    let lam = (Fr::from(3u64) * x * x) * (y + y).inverse().unwrap();
    let x3 = lam * lam - x - x;
    Some((x3, lam * (x - x3) - y))
}

fn g_add(p: Commitment, q: Commitment) -> Commitment {
    match (p, q) {
        (None, _) => q,
        (_, None) => p,
        (Some((x1, y1)), Some((x2, y2))) => {
            if x1 == x2 {
                if y1 == y2 { g_double((x1, y1)) } else { None } // p = −q ⇒ ∞
            } else {
                let lam = (y2 - y1) * (x2 - x1).inverse().unwrap();
                let x3 = lam * lam - x1 - x2;
                Some((x3, lam * (x1 - x3) - y1))
            }
        }
    }
}

/// Integer scalar multiplication `k·P` (double-and-add).
fn g_mul(k: &BigUint, p: Commitment) -> Commitment {
    let mut acc = None;
    let mut base = p;
    for i in 0..k.bits() {
        if k.bit(i) {
            acc = g_add(acc, base);
        }
        base = g_add(base, base);
    }
    acc
}

/// Fixed Grumpkin base point `O = (5, …)` (shared with the circuit gadget).
fn base() -> Commitment {
    let y = Fr::from_le_bytes_mod_order(
        &BigUint::from_str("26447525821777463057023244913909144251512587297343525263882")
            .unwrap()
            .to_bytes_le(),
    );
    Some((Fr::from(5u64), y))
}

fn gen_for(i: u64) -> Commitment {
    g_mul(&BigUint::from(i + 1), base())
}
fn fq_to_biguint(x: Fq) -> BigUint {
    BigUint::from_bytes_le(&x.into_bigint().to_bytes_le())
}

/// Pedersen commitment `Σ vals[i]·G_{i+offset}` over Grumpkin, of **`Fq` values**.
/// `Fq` is Grumpkin's *scalar* field, so this is homomorphic w.r.t. `Fq`
/// arithmetic: `commit(a + r·b) = commit(a) + r·commit(b)` (all mod `q`).
///
/// FINDING (the CycleFold reason): the *primary* R1CS witness lives in `Fr ≠ Fq`,
/// and `Fr` arithmetic (mod `r`) does **not** match the group (mod `q`), so the
/// primary witness is **not** `Fr`-homomorphically committable on Grumpkin — the
/// cross-field commitment is the companion curve's job. Grumpkin natively folds
/// `Fq`-valued commitments (the companion circuit's witness): that is CycleFold.
pub fn commit_fq(vals: &[Fq], offset: u64) -> Commitment {
    vals.iter().enumerate().fold(None, |acc, (i, v)| {
        g_add(acc, g_mul(&fq_to_biguint(*v), gen_for(i as u64 + offset)))
    })
}

/// Scale a commitment by an `Fq` challenge — the `r·comm` the in-circuit fold does.
pub fn scale(p: Commitment, r: Fq) -> Commitment {
    g_mul(&fq_to_biguint(r), p)
}

/// Add two commitments (the `comm1 + comm2` the in-circuit fold does).
pub fn add(p: Commitment, q: Commitment) -> Commitment {
    g_add(p, q)
}
