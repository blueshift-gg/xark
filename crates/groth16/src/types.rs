//! Groth16 keys and proofs, and verification.
//!
//! The structs mirror `ark-groth16`'s field for field and derive the same
//! `CanonicalSerialize`, so `pk.bin` / `vk.bin` / `proof.bin` are byte-for-byte the
//! files arkworks reads and writes (the tests check this against `ark-groth16`,
//! kept as a dev-dependency only). Verification is the pairing check itself.

use ark_ec::AffineRepr;
use ark_ec::CurveGroup;
use ark_ec::pairing::{MillerLoopOutput, Pairing};
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// A Groth16 proof.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<E: Pairing> {
    /// `A`, in G1.
    pub a: E::G1Affine,
    /// `B`, in G2.
    pub b: E::G2Affine,
    /// `C`, in G1.
    pub c: E::G1Affine,
}

/// A Groth16 verifying key.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifyingKey<E: Pairing> {
    /// `α·G1`.
    pub alpha_g1: E::G1Affine,
    /// `β·G2`.
    pub beta_g2: E::G2Affine,
    /// `γ·G2`.
    pub gamma_g2: E::G2Affine,
    /// `δ·G2`.
    pub delta_g2: E::G2Affine,
    /// `γ⁻¹·(β·aᵢ + α·bᵢ + cᵢ)·G1` for the constant `1` and each public input.
    pub gamma_abc_g1: Vec<E::G1Affine>,
}

impl<E: Pairing> Default for Proof<E> {
    fn default() -> Self {
        Proof {
            a: E::G1Affine::default(),
            b: E::G2Affine::default(),
            c: E::G1Affine::default(),
        }
    }
}

impl<E: Pairing> Default for VerifyingKey<E> {
    fn default() -> Self {
        VerifyingKey {
            alpha_g1: E::G1Affine::default(),
            beta_g2: E::G2Affine::default(),
            gamma_g2: E::G2Affine::default(),
            delta_g2: E::G2Affine::default(),
            gamma_abc_g1: Vec::new(),
        }
    }
}

/// A Groth16 proving key.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProvingKey<E: Pairing> {
    /// The verifying key.
    pub vk: VerifyingKey<E>,
    /// `β·G1`.
    pub beta_g1: E::G1Affine,
    /// `δ·G1`.
    pub delta_g1: E::G1Affine,
    /// `aᵢ·G1`.
    pub a_query: Vec<E::G1Affine>,
    /// `bᵢ·G1`.
    pub b_g1_query: Vec<E::G1Affine>,
    /// `bᵢ·G2`.
    pub b_g2_query: Vec<E::G2Affine>,
    /// `hᵢ·G1`.
    pub h_query: Vec<E::G1Affine>,
    /// `lᵢ·G1`.
    pub l_query: Vec<E::G1Affine>,
}

/// A verification that couldn't be performed (as opposed to a proof that fails).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerifyError {
    /// The verifying key takes `expected` public inputs, `got` were given.
    PublicInputCount { expected: usize, got: usize },
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerifyError::PublicInputCount { expected, got } => write!(
                f,
                "the verifying key takes {expected} public input(s), {got} given"
            ),
        }
    }
}

impl std::error::Error for VerifyError {}

/// Verify `proof` for `public_inputs` under `vk`:
/// `e(A, B) = e(α, β) · e(Σ xᵢ·γ_abcᵢ, γ) · e(C, δ)`, checked as one multi-pairing.
/// `Ok(false)` for a proof that doesn't verify; `Err` when the number of public
/// inputs doesn't match the key (rather than silently ignoring or zero-filling
/// the difference).
pub fn verify<E: Pairing>(
    vk: &VerifyingKey<E>,
    public_inputs: &[E::ScalarField],
    proof: &Proof<E>,
) -> Result<bool, VerifyError> {
    Ok(Prepared::new(vk, public_inputs)?.verify(proof))
}

/// What a check needs from the verifying key alone: `e(−α, β)`'s Miller loop
/// and `−γ`, `−δ` prepared for theirs. A prover makes proof after proof under
/// one key, so the last key's are kept (the four points compared, not trusted
/// by address): a quarter of a millisecond a proof, on the path of a small one.
struct KeyParts<E: Pairing> {
    points: (E::G1Affine, E::G2Affine, E::G2Affine, E::G2Affine),
    alpha_beta: E::TargetField,
    gamma: E::G2Prepared,
    delta: E::G2Prepared,
}

fn key_parts<E: Pairing>(vk: &VerifyingKey<E>) -> std::sync::Arc<KeyParts<E>> {
    use std::any::Any;
    use std::sync::{Arc, Mutex};
    static LAST: Mutex<Option<Box<dyn Any + Send + Sync>>> = Mutex::new(None);
    let points = (vk.alpha_g1, vk.beta_g2, vk.gamma_g2, vk.delta_g2);
    let cached = LAST
        .lock()
        .ok()
        .and_then(|l| l.as_ref()?.downcast_ref::<Arc<KeyParts<E>>>().cloned())
        .filter(|k| k.points == points);
    if let Some(k) = cached {
        return k;
    }
    let neg = |p: E::G2Affine| E::G2Prepared::from((-p.into_group()).into_affine());
    let k = Arc::new(KeyParts {
        points,
        alpha_beta: E::multi_miller_loop([(-vk.alpha_g1.into_group()).into_affine()], [vk.beta_g2])
            .0,
        gamma: neg(vk.gamma_g2),
        delta: neg(vk.delta_g2),
    });
    if let Ok(mut l) = LAST.lock() {
        *l = Some(Box::new(k.clone()));
    }
    k
}

/// What a check of a proof for these public inputs under `vk` can compute before
/// the proof exists: the prover makes it while the MSMs run. The check is
/// `e(A, B)·e(acc, −γ)·e(C, −δ)·e(−α, β) = 1`, as one final exponentiation over
/// the Miller loops' product; the proof-free half, `e(acc, −γ)·e(−α, β)`, is
/// made here, and the rest can be made as A, B and C appear
/// ([`Self::verify_with`]).
pub(crate) struct Prepared<E: Pairing> {
    delta: E::G2Prepared,
    /// The Miller loops of `e(acc, −γ)` and `e(−α, β)`, multiplied.
    fixed: E::TargetField,
}

impl<E: Pairing> Prepared<E> {
    pub(crate) fn new(
        vk: &VerifyingKey<E>,
        public_inputs: &[E::ScalarField],
    ) -> Result<Self, VerifyError> {
        let expected = vk.gamma_abc_g1.len().saturating_sub(1);
        if public_inputs.len() != expected || vk.gamma_abc_g1.is_empty() {
            return Err(VerifyError::PublicInputCount {
                expected,
                got: public_inputs.len(),
            });
        }
        let mut acc = vk.gamma_abc_g1[0].into_group();
        for (x, base) in public_inputs.iter().zip(&vk.gamma_abc_g1[1..]) {
            acc += *base * x;
        }
        let k = key_parts(vk);
        Ok(Prepared {
            delta: k.delta.clone(),
            fixed: E::multi_miller_loop([acc.into_affine()], [k.gamma.clone()]).0 * k.alpha_beta,
        })
    }

    /// The check, given the product of the Miller loops of `e(A, B)` and
    /// `e(C, −δ)` (made however the caller likes).
    pub(crate) fn verify_with(&self, ab_c: E::TargetField) -> bool {
        E::final_exponentiation(MillerLoopOutput(ab_c * self.fixed)).is_some_and(|r| r.is_zero())
    }

    pub(crate) fn verify(&self, proof: &Proof<E>) -> bool {
        let (ab, c) = rayon::join(
            || E::multi_miller_loop([proof.a], [proof.b]).0,
            || E::multi_miller_loop([proof.c], [self.delta.clone()]).0,
        );
        let f = ab * self.fixed * c;
        E::final_exponentiation(MillerLoopOutput(f)).is_some_and(|r| r.is_zero())
    }
}
