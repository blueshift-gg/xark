//! Groth16 keys and proofs, and verification.
//!
//! The structs mirror `ark-groth16`'s field for field and derive the same
//! `CanonicalSerialize`, so `pk.bin` / `vk.bin` / `proof.bin` are byte-for-byte the
//! files arkworks reads and writes (the tests check this against `ark-groth16`,
//! kept as a dev-dependency only). Verification is the pairing check itself.

use ark_ec::AffineRepr;
use ark_ec::CurveGroup;
use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
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
    let expected = vk.gamma_abc_g1.len().saturating_sub(1);
    if public_inputs.len() != expected || vk.gamma_abc_g1.is_empty() {
        return Err(VerifyError::PublicInputCount {
            expected,
            got: public_inputs.len(),
        });
    }
    let mut acc = vk.gamma_abc_g1[0].into_group();
    for (x, base) in public_inputs.iter().zip(&vk.gamma_abc_g1[1..]) {
        acc += base.mul_bigint(x.into_bigint());
    }
    let lhs = E::multi_pairing(
        [proof.a, acc.into_affine(), proof.c],
        [
            proof.b,
            (-vk.gamma_g2.into_group()).into_affine(),
            (-vk.delta_g2.into_group()).into_affine(),
        ],
    );
    Ok(lhs == E::pairing(vk.alpha_g1, vk.beta_g2))
}
