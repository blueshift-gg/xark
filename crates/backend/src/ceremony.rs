//! Phase-2 MPC ceremony driver.
//!
//! Multi-contributor randomness chain on top of the phase-2 setup. Each
//! contributor samples a fresh secret `δ_i ∈ Fr*`, applies it to the
//! delta-scaled queries in place, and attaches a publicly verifiable proof of
//! contribution. The chain composes multiplicatively: after `n` contributors,
//! `δ = δ_0 · δ_1 ·... · δ_n`. As long as at least ONE contributor was honest
//! and discarded their `δ_i`, the trapdoor δ is unknown to any prover.
//!
//! # Contribution math (per contributor)
//!
//! For each contributor's secret `δ_i`:
//!
//! 1. `pk.delta_g1' = δ_i · pk.delta_g1` (and `vk.delta_g2' = δ_i · vk.delta_g2`).
//! 2. `pk.h_query[k]' = δ_i⁻¹ · pk.h_query[k]` for every `k`.
//! 3. `pk.l_query[i]' = δ_i⁻¹ · pk.l_query[i]` for every `i`.
//!
//! Queries scaled by α/β/γ (the `gamma_abc_g1` and `a_query`/`b_*_query`
//! components) are untouched — they live in the γ-scaled fiber.
//!
//! # Proof of contribution
//!
//! Each contributor publishes `δ_i · G2` and a Schnorr proof of knowledge
//! of `δ_i` (with respect to `G2`). The verifier then checks two pairings:
//!
//! * The Schnorr proof: `proof_response · G2 == proof_commitment + e · (δ_i · G2)`,
//!   where `e = H(prev_delta_g2 || new_delta_g2 || proof_commitment)`.
//! * The δ-consistency check: `e(new_delta_g1, G2) == e(prev_delta_g1, δ_i·G2)`.
//!
//! The first proves knowledge of `δ_i` as a scalar (no extraction shortcuts);
//! the second proves the same `δ_i` was used in both the G1 and G2 update.
//!
//! # Soundness summary
//!
//! After `verify_chain` accepts a transcript:
//! * Every contribution's `δ_i` is a scalar known to its contributor.
//! * Every contribution applied the same `δ_i` to the G1 and G2 deltas.
//! * The final delta is the product of all `δ_i`.
//!
//! If at least one honest contributor discarded their `δ_i`, the final
//! `δ` is information-theoretically hidden from any prover.
//!
//! The chain says nothing about the rest of the keys, which a coordinator ships:
//! [`verify_keys_match_initial`] checks them against the keys `init` made, which
//! anyone can recompute from the circuit, the `.ptau` and the recorded seed.

use ark_bn254::{Bn254, Fr, G1Affine, G2Affine};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField, UniformRand, Zero};
use rand::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::keys::Groth16Keys;

/// One contributor's public attestation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Contribution {
    /// `δ_i · G2`, the public commitment to this contributor's secret.
    #[serde(with = "ark_g2_hex")]
    pub delta_g2_contribution: G2Affine,
    /// Schnorr proof commitment `r · G2`.
    #[serde(with = "ark_g2_hex")]
    pub proof_commitment: G2Affine,
    /// Schnorr proof response `r + e · δ_i` as `Fr`.
    #[serde(with = "ark_fr_hex")]
    pub proof_response: Fr,
    /// `prev_delta_g1` snapshot for the pairing-consistency check.
    #[serde(with = "ark_g1_hex")]
    pub prev_delta_g1: G1Affine,
    /// `new_delta_g1` snapshot.
    #[serde(with = "ark_g1_hex")]
    pub new_delta_g1: G1Affine,
    /// Optional human-readable label for audit traceability.
    pub contributor_label: String,
}

/// Errors produced by [`contribute`] / [`verify_chain`].
#[derive(Debug, Error)]
pub enum CeremonyError {
    #[error("ceremony: secret δ_i must be non-zero")]
    ZeroSecret,
    #[error("ceremony: Schnorr proof check failed for contribution {index}")]
    SchnorrInvalid { index: usize },
    #[error("ceremony: δ-consistency pairing check failed for contribution {index}")]
    DeltaInconsistent { index: usize },
    #[error("ceremony: contribution {index} prev_delta_g1 does not match the running delta")]
    ChainBreak { index: usize },
    #[error(
        "ceremony: contribution {index} is degenerate (δ_i·G2 or the new δ·G1 is the identity) — \
         a zero contribution collapses the accumulated δ and makes the trapdoor trivially known"
    )]
    DegenerateContribution { index: usize },
    #[error(
        "ceremony: final accumulated δ is the identity — the trapdoor would be trivially known"
    )]
    DegenerateFinalDelta,
    #[error(
        "ceremony: the shipped keys do not match the verified contribution chain \
         (proving_key.delta_g1 ≠ the chain's final δ·G1, or vk.delta_g2 is inconsistent with it)"
    )]
    KeysDoNotMatchChain,
    #[error(
        "ceremony: the shipped keys' {part} differs from what the circuit and the .ptau \
         give — only δ may change in a ceremony"
    )]
    KeysDoNotMatchCircuit { part: &'static str },
}

/// Apply this contributor's secret `δ_i` to `keys` in place, returning the
/// `Contribution` attestation that downstream verifiers will check.
pub fn contribute<R: RngCore + CryptoRng>(
    keys: &mut Groth16Keys,
    contributor_label: &str,
    rng: &mut R,
) -> Result<Contribution, CeremonyError> {
    let delta_i = sample_nonzero_fr(rng)?;
    let delta_inv = delta_i.inverse().expect("δ_i != 0");
    let g2_generator = G2Affine::generator();

    let prev_delta_g1 = keys.proving_key.delta_g1;
    let prev_delta_g2 = keys.verifying_key.delta_g2;

    // δ_i · G2 (public commitment).
    let delta_g2_contribution = (g2_generator * delta_i).into_affine();

    // Apply δ_i to the delta-scaled queries first so the new_delta_g1 is
    // available for the (verifier-reconstructable) Schnorr challenge.
    keys.proving_key.delta_g1 = (prev_delta_g1 * delta_i).into_affine();
    let new_delta_g2 = (prev_delta_g2 * delta_i).into_affine();
    keys.proving_key.vk.delta_g2 = new_delta_g2;
    keys.verifying_key.delta_g2 = new_delta_g2;

    for q in keys.proving_key.h_query.iter_mut() {
        *q = (*q * delta_inv).into_affine();
    }
    for q in keys.proving_key.l_query.iter_mut() {
        *q = (*q * delta_inv).into_affine();
    }

    let new_delta_g1 = keys.proving_key.delta_g1;

    // Schnorr proof of knowledge of δ_i wrt G2, anchored to the public
    // (prev → new) delta state so the verifier can recompute it from the
    // chain.
    let r = sample_nonzero_fr(rng)?;
    let proof_commitment = (g2_generator * r).into_affine();
    let challenge = schnorr_challenge_v1(
        &prev_delta_g1,
        &new_delta_g1,
        &delta_g2_contribution,
        &proof_commitment,
    );
    let proof_response = r + challenge * delta_i;

    Ok(Contribution {
        delta_g2_contribution,
        proof_commitment,
        proof_response,
        prev_delta_g1,
        new_delta_g1,
        contributor_label: contributor_label.to_string(),
    })
}

/// Walk the contribution chain, confirming each contribution's Schnorr
/// proof and δ-consistency pairing check. `initial_delta_g1` is the
/// `delta_g1` from the un-contributed (post-phase-2) starting state.
pub fn verify_chain(
    initial_delta_g1: G1Affine,
    contributions: &[Contribution],
) -> Result<(), CeremonyError> {
    let g2_generator = G2Affine::generator();
    let mut running = initial_delta_g1;
    for (i, c) in contributions.iter().enumerate() {
        if c.prev_delta_g1 != running {
            return Err(CeremonyError::ChainBreak { index: i });
        }
        // reject a degenerate δ_i = 0 contribution: it passes the Schnorr and
        // δ-consistency checks yet zeroes the accumulated δ, so any proof verifies
        if c.delta_g2_contribution.is_zero() || c.new_delta_g1.is_zero() {
            return Err(CeremonyError::DegenerateContribution { index: i });
        }
        // Schnorr proof: proof_response · G2 == proof_commitment + e · (δ_i · G2).
        let challenge = schnorr_challenge_v1(
            &c.prev_delta_g1,
            &c.new_delta_g1,
            &c.delta_g2_contribution,
            &c.proof_commitment,
        );
        let lhs = (g2_generator * c.proof_response).into_affine();
        let rhs =
            (c.proof_commitment.into_group() + c.delta_g2_contribution * challenge).into_affine();
        if lhs != rhs {
            return Err(CeremonyError::SchnorrInvalid { index: i });
        }
        // δ-consistency pairing: e(new_delta_g1, G2) == e(prev_delta_g1, δ_i·G2).
        let pair_lhs = Bn254::pairing(c.new_delta_g1, g2_generator);
        let pair_rhs = Bn254::pairing(c.prev_delta_g1, c.delta_g2_contribution);
        if pair_lhs != pair_rhs {
            return Err(CeremonyError::DeltaInconsistent { index: i });
        }
        running = c.new_delta_g1;
    }
    // accumulated δ must not be the identity (also guarded per-contribution above)
    if running.is_zero() {
        return Err(CeremonyError::DegenerateFinalDelta);
    }
    Ok(())
}

/// Confirm the shipped keys are the ones the verified chain produced:
/// `proving_key.delta_g1` must equal the chain's final δ·G1, and `vk.delta_g2`
/// must carry the same δ (via `e(δ·G1, G2) == e(G1, δ·G2)`). Call after
/// [`verify_chain`] returns `Ok`.
pub fn verify_keys_consistent_with_chain(
    keys: &Groth16Keys,
    initial_delta_g1: G1Affine,
    contributions: &[Contribution],
) -> Result<(), CeremonyError> {
    let expected_delta_g1 = contributions
        .last()
        .map(|c| c.new_delta_g1)
        .unwrap_or(initial_delta_g1);
    if keys.proving_key.delta_g1 != expected_delta_g1 {
        return Err(CeremonyError::KeysDoNotMatchChain);
    }
    // δ·G1 and δ·G2 must share the same scalar δ: e(δ·G1, G2) == e(G1, δ·G2).
    let g1 = G1Affine::generator();
    let g2 = G2Affine::generator();
    if Bn254::pairing(keys.proving_key.delta_g1, g2)
        != Bn254::pairing(g1, keys.verifying_key.delta_g2)
    {
        return Err(CeremonyError::KeysDoNotMatchChain);
    }
    Ok(())
}

/// Confirm the shipped keys are `initial` (the keys `init` made, recomputed from the
/// circuit, the `.ptau` and the phase-2 seed) with only δ changed. Every part a
/// contribution doesn't touch must be `initial`'s exactly: a coordinator could
/// otherwise ship, say, `γ = δ`, which lets anyone prove anything (`A = α`, `B = β`,
/// `C = −Σ xᵢ·ICᵢ`) behind an honest chain. The δ-scaled `h` and `l` queries must
/// be `initial`'s times `δ₀/δ`, checked as one pairing over a random combination
/// of them: `e(Σ rₖ·Pₖ, δ·G2) == e(Σ rₖ·P⁰ₖ, δ₀·G2)`. Call after
/// [`verify_keys_consistent_with_chain`] (which ties `δ` to the chain).
pub fn verify_keys_match_initial<R: RngCore>(
    keys: &Groth16Keys,
    initial: &Groth16Keys,
    rng: &mut R,
) -> Result<(), CeremonyError> {
    use ark_ec::VariableBaseMSM;
    let (pk, pk0) = (&keys.proving_key, &initial.proving_key);
    let (vk, vk0) = (&keys.verifying_key, &initial.verifying_key);
    let differs = |part: &'static str| Err(CeremonyError::KeysDoNotMatchCircuit { part });
    if pk.vk != *vk {
        return differs("the proving key's copy of the verifying key");
    }
    if vk.alpha_g1 != vk0.alpha_g1 {
        return differs("α");
    }
    if vk.beta_g2 != vk0.beta_g2 || pk.beta_g1 != pk0.beta_g1 {
        return differs("β");
    }
    if vk.gamma_g2 != vk0.gamma_g2 {
        return differs("γ");
    }
    if vk.gamma_abc_g1 != vk0.gamma_abc_g1 {
        return differs("the public-input points (γ_abc)");
    }
    if pk.a_query != pk0.a_query {
        return differs("the A query");
    }
    if pk.b_g1_query != pk0.b_g1_query || pk.b_g2_query != pk0.b_g2_query {
        return differs("the B query");
    }
    if pk.h_query.len() != pk0.h_query.len() || pk.l_query.len() != pk0.l_query.len() {
        return differs("the H or L query's length");
    }
    let points: Vec<G1Affine> = pk.h_query.iter().chain(&pk.l_query).copied().collect();
    let points0: Vec<G1Affine> = pk0.h_query.iter().chain(&pk0.l_query).copied().collect();
    let r: Vec<Fr> = (0..points.len()).map(|_| Fr::rand(rng)).collect();
    let sum = <Bn254 as Pairing>::G1::msm(&points, &r).expect("one scalar per point");
    let sum0 = <Bn254 as Pairing>::G1::msm(&points0, &r).expect("one scalar per point");
    if Bn254::pairing(sum, vk.delta_g2) != Bn254::pairing(sum0, vk0.delta_g2) {
        return differs("the H or L query (not rescaled by the chain's δ alone)");
    }
    Ok(())
}

/// Schnorr challenge anchored to the public pre/post G1 deltas + the
/// `δ_i·G2` commitment + the proof commitment. Both `contribute` and
/// `verify_chain` recompute it from these public state values.
fn schnorr_challenge_v1(
    prev_delta_g1: &G1Affine,
    new_delta_g1: &G1Affine,
    delta_g2_contribution: &G2Affine,
    proof_commitment: &G2Affine,
) -> Fr {
    let mut h = Sha256::new();
    h.update(b"xark-ceremony-schnorr-v1");
    h.update(serialize_g1_for_hash(prev_delta_g1));
    h.update(serialize_g1_for_hash(new_delta_g1));
    h.update(serialize_g2_for_hash(delta_g2_contribution));
    h.update(serialize_g2_for_hash(proof_commitment));
    Fr::from_be_bytes_mod_order(&h.finalize())
}

fn serialize_g1_for_hash(p: &G1Affine) -> [u8; 64] {
    crate::solana::encode_g1(p)
}

fn serialize_g2_for_hash(p: &G2Affine) -> [u8; 128] {
    crate::solana::encode_g2(p)
}

fn sample_nonzero_fr<R: RngCore + CryptoRng>(rng: &mut R) -> Result<Fr, CeremonyError> {
    for _ in 0..16 {
        let candidate = Fr::rand(rng);
        if !candidate.is_zero() {
            return Ok(candidate);
        }
    }
    Err(CeremonyError::ZeroSecret)
}

// =============================================================================
// Serde helpers for ark-bn254 types
// =============================================================================

mod ark_g1_hex {
    use super::*;
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
    use serde::{Deserializer, Serializer};

    pub fn serialize<S: Serializer>(p: &G1Affine, s: S) -> Result<S::Ok, S::Error> {
        let mut buf = Vec::new();
        p.serialize_with_mode(&mut buf, Compress::Yes)
            .map_err(serde::ser::Error::custom)?;
        s.serialize_str(&hex::encode(buf))
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<G1Affine, D::Error> {
        use serde::Deserialize;
        let s: String = Deserialize::deserialize(d)?;
        let bytes = hex::decode(s).map_err(serde::de::Error::custom)?;
        G1Affine::deserialize_with_mode(bytes.as_slice(), Compress::Yes, Validate::Yes)
            .map_err(serde::de::Error::custom)
    }
}

mod ark_g2_hex {
    use super::*;
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
    use serde::{Deserializer, Serializer};

    pub fn serialize<S: Serializer>(p: &G2Affine, s: S) -> Result<S::Ok, S::Error> {
        let mut buf = Vec::new();
        p.serialize_with_mode(&mut buf, Compress::Yes)
            .map_err(serde::ser::Error::custom)?;
        s.serialize_str(&hex::encode(buf))
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<G2Affine, D::Error> {
        use serde::Deserialize;
        let s: String = Deserialize::deserialize(d)?;
        let bytes = hex::decode(s).map_err(serde::de::Error::custom)?;
        G2Affine::deserialize_with_mode(bytes.as_slice(), Compress::Yes, Validate::Yes)
            .map_err(serde::de::Error::custom)
    }
}

mod ark_fr_hex {
    use super::*;
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
    use serde::{Deserializer, Serializer};

    pub fn serialize<S: Serializer>(f: &Fr, s: S) -> Result<S::Ok, S::Error> {
        let mut buf = Vec::new();
        f.serialize_with_mode(&mut buf, Compress::Yes)
            .map_err(serde::ser::Error::custom)?;
        s.serialize_str(&hex::encode(buf))
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Fr, D::Error> {
        use serde::Deserialize;
        let s: String = Deserialize::deserialize(d)?;
        let bytes = hex::decode(s).map_err(serde::de::Error::custom)?;
        Fr::deserialize_with_mode(bytes.as_slice(), Compress::Yes, Validate::Yes)
            .map_err(serde::de::Error::custom)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keys::Groth16Keys;
    use ark_bn254::Fr;
    use ark_ec::CurveGroup;
    use ark_ec::PrimeGroup;
    use ark_ff::UniformRand;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use xark_groth16::{ConstraintSource, InMemoryPk, ProgramSource, ProverConfig};
    use xark_ir::LinearCombination;
    use xark_ir::r1cs::{FieldSpec, R1csConstraint, R1csProgram, Variable, Visibility};

    /// A test circuit: `x · x = y` with `y` public.
    fn square() -> R1csProgram {
        let var = |id, name: &str, visibility| Variable {
            id,
            name: name.into(),
            visibility,
        };
        R1csProgram {
            field: FieldSpec::bn254(),
            variables: vec![
                var(0, "y", Visibility::Public),
                var(1, "x", Visibility::Private),
            ],
            constraints: vec![R1csConstraint::mul(
                0,
                LinearCombination::var(1),
                LinearCombination::var(1),
                0,
                "x * x = y",
            )],
        }
    }

    /// Prove `x · x = y` with `keys` and verify it.
    fn proves(keys: &Groth16Keys, x: u64, rng: &mut ChaCha20Rng) -> bool {
        let prog = square();
        let src = ProgramSource::new(&prog);
        let y = Fr::from(x * x);
        let z = src
            .layout()
            .assignment(|id| Some(if id == 0 { y } else { Fr::from(x) }));
        let pk = &mut InMemoryPk::new(&keys.proving_key);
        let proof = xark_groth16::prove(&src, &z, pk, rng, &ProverConfig::default()).unwrap();
        xark_groth16::verify(&keys.verifying_key, &[y], &proof).unwrap()
    }

    /// Phase-2 keys for [`square`] from a synthetic ptau: the starting point for
    /// the ceremony tests.
    fn fresh_phase2_keys() -> Groth16Keys {
        let mut rng = ChaCha20Rng::seed_from_u64(0xDEADBEEF);
        let tau = Fr::rand(&mut rng);
        let alpha = Fr::rand(&mut rng);
        let beta = Fr::rand(&mut rng);
        let ptau = fake_ptau(4, tau, alpha, beta);
        let seed = [7u8; 32];
        crate::ptau::setup_from_ptau(&ProgramSource::new(&square()), &ptau, &seed)
            .expect("phase-2 setup succeeds")
    }

    fn fake_ptau(power: u32, tau: Fr, alpha: Fr, beta: Fr) -> crate::ptau::PtauFile {
        let n = 1usize << power;
        let g1 = ark_bn254::G1Projective::generator();
        let g2 = ark_bn254::G2Projective::generator();
        let mut tau_g1 = Vec::with_capacity(2 * n - 1);
        let mut tau_g2 = Vec::with_capacity(n);
        let mut alpha_tau_g1 = Vec::with_capacity(n);
        let mut beta_tau_g1 = Vec::with_capacity(n);
        let mut tau_pow = Fr::from(1u64);
        for k in 0..(2 * n - 1) {
            tau_g1.push((g1 * tau_pow).into_affine());
            if k < n {
                tau_g2.push((g2 * tau_pow).into_affine());
                alpha_tau_g1.push((g1 * (alpha * tau_pow)).into_affine());
                beta_tau_g1.push((g1 * (beta * tau_pow)).into_affine());
            }
            tau_pow *= tau;
        }
        let beta_g2 = (g2 * beta).into_affine();
        crate::ptau::PtauFile {
            power,
            tau_g1,
            tau_g2,
            alpha_tau_g1,
            beta_tau_g1,
            beta_g2,
        }
    }

    /// A transcript whose τ is a root of unity of its size passes every other check,
    /// yet makes the vanishing polynomial 0 at τ, so any witness would prove: refused.
    #[test]
    fn a_root_of_unity_tau_is_refused() {
        use ark_ff::FftField;
        let (alpha, beta) = (Fr::from(5u64), Fr::from(7u64));
        let i4 = Fr::get_root_of_unity(4).expect("a 4th root of unity");
        for tau in [-Fr::from(1u64), i4] {
            let ptau = fake_ptau(4, tau, alpha, beta);
            let r = crate::ptau::setup_from_ptau(&ProgramSource::new(&square()), &ptau, &[7u8; 32]);
            assert!(r.is_err(), "τ = {tau} was accepted");
        }
    }

    #[test]
    fn single_contribution_then_proof_verifies() {
        let mut keys = fresh_phase2_keys();
        let initial_delta_g1 = keys.proving_key.delta_g1;
        let mut rng = ChaCha20Rng::seed_from_u64(1);
        let c = contribute(&mut keys, "alice", &mut rng).expect("contribute");
        verify_chain(initial_delta_g1, &[c]).expect("verify chain");

        // The post-contribution keys still produce a valid proof.
        assert!(proves(&keys, 9, &mut rng));
    }

    #[test]
    fn three_contributions_compose_and_verify() {
        let mut keys = fresh_phase2_keys();
        let initial_delta_g1 = keys.proving_key.delta_g1;
        let mut rng = ChaCha20Rng::seed_from_u64(2);
        let contributions = vec![
            contribute(&mut keys, "alice", &mut rng).unwrap(),
            contribute(&mut keys, "bob", &mut rng).unwrap(),
            contribute(&mut keys, "carol", &mut rng).unwrap(),
        ];
        verify_chain(initial_delta_g1, &contributions).expect("verify chain");

        // End-to-end proof still works.
        assert!(proves(&keys, 11, &mut rng));
    }

    #[test]
    fn tampered_chain_link_is_rejected() {
        let mut keys = fresh_phase2_keys();
        let initial_delta_g1 = keys.proving_key.delta_g1;
        let mut rng = ChaCha20Rng::seed_from_u64(3);
        let mut c1 = contribute(&mut keys, "alice", &mut rng).unwrap();
        let c2 = contribute(&mut keys, "bob", &mut rng).unwrap();

        // Tamper: swap c1's prev_delta_g1 with c2's new_delta_g1 (chain break).
        c1.prev_delta_g1 = c2.new_delta_g1;
        let err = verify_chain(initial_delta_g1, &[c1, c2]).unwrap_err();
        assert!(matches!(err, CeremonyError::ChainBreak { index: 0 }));
    }

    #[test]
    fn tampered_schnorr_response_is_rejected() {
        let mut keys = fresh_phase2_keys();
        let initial_delta_g1 = keys.proving_key.delta_g1;
        let mut rng = ChaCha20Rng::seed_from_u64(4);
        let mut c = contribute(&mut keys, "alice", &mut rng).unwrap();
        c.proof_response += Fr::from(1u64);
        let err = verify_chain(initial_delta_g1, &[c]).unwrap_err();
        assert!(matches!(err, CeremonyError::SchnorrInvalid { index: 0 }));
    }

    #[test]
    fn tampered_delta_consistency_is_rejected() {
        // Swap one contribution's delta_g2_contribution for an unrelated G2 point.
        let mut keys = fresh_phase2_keys();
        let initial_delta_g1 = keys.proving_key.delta_g1;
        let mut rng = ChaCha20Rng::seed_from_u64(5);
        let mut c = contribute(&mut keys, "alice", &mut rng).unwrap();
        // Replace δ_i·G2 with G2 · 42 (unrelated to the G1 update).
        let g2 = G2Affine::generator();
        c.delta_g2_contribution = (g2 * Fr::from(42u64)).into_affine();
        // Schnorr is also broken (it's tied to delta_g2_contribution), so we
        // expect SchnorrInvalid first — the chain order is Schnorr → δ-consistency.
        let err = verify_chain(initial_delta_g1, &[c]).unwrap_err();
        assert!(matches!(
            err,
            CeremonyError::SchnorrInvalid { .. } | CeremonyError::DeltaInconsistent { .. }
        ));
    }

    #[test]
    fn degenerate_zero_delta_contribution_is_rejected() {
        // A δ_i = 0 contribution crafted to satisfy both the Schnorr proof and
        // the δ-consistency pairing (accepted pre-fix) must now be rejected — it
        // collapses the accumulated δ to the identity.
        let keys = fresh_phase2_keys();
        let initial = keys.proving_key.delta_g1;
        let g2 = G2Affine::generator();
        let r = Fr::from(12_345u64);
        let proof_commitment = (g2 * r).into_affine();

        let degenerate = Contribution {
            delta_g2_contribution: G2Affine::zero(),
            proof_commitment,
            proof_response: r,
            prev_delta_g1: initial,
            new_delta_g1: G1Affine::zero(),
            contributor_label: "attacker".into(),
        };
        let err = verify_chain(initial, &[degenerate]).unwrap_err();
        assert!(
            matches!(err, CeremonyError::DegenerateContribution { index: 0 }),
            "δ=0 contribution must be rejected, got {err:?}"
        );
    }

    #[test]
    fn keys_must_match_the_verified_chain() {
        let mut keys = fresh_phase2_keys();
        let initial = keys.proving_key.delta_g1;
        let mut rng = ChaCha20Rng::seed_from_u64(9);
        let c = contribute(&mut keys, "alice", &mut rng).unwrap();
        verify_chain(initial, std::slice::from_ref(&c)).unwrap();
        // Honest shipped keys are bound to the chain.
        verify_keys_consistent_with_chain(&keys, initial, std::slice::from_ref(&c))
            .expect("honest keys match");

        // a different vk.delta_g2 (δ they know) is caught by the pairing check
        keys.verifying_key.delta_g2 = (G2Affine::generator() * Fr::from(999u64)).into_affine();
        assert!(matches!(
            verify_keys_consistent_with_chain(&keys, initial, std::slice::from_ref(&c))
                .unwrap_err(),
            CeremonyError::KeysDoNotMatchChain
        ));

        // proving_key.delta_g1 not equal to the chain's final δ·G1.
        keys.proving_key.delta_g1 = (G1Affine::generator() * Fr::from(7u64)).into_affine();
        assert!(matches!(
            verify_keys_consistent_with_chain(&keys, initial, &[c]).unwrap_err(),
            CeremonyError::KeysDoNotMatchChain
        ));
    }

    /// Two contributions, then the shipped keys checked against freshly made initial
    /// ones (what `init` recomputes from the circuit, `.ptau` and seed).
    fn contributed() -> (Groth16Keys, Groth16Keys, ChaCha20Rng) {
        let initial = fresh_phase2_keys();
        let mut keys = initial.clone();
        let mut rng = ChaCha20Rng::seed_from_u64(10);
        let cs = vec![
            contribute(&mut keys, "alice", &mut rng).unwrap(),
            contribute(&mut keys, "bob", &mut rng).unwrap(),
        ];
        verify_chain(initial.proving_key.delta_g1, &cs).unwrap();
        verify_keys_consistent_with_chain(&keys, initial.proving_key.delta_g1, &cs).unwrap();
        (keys, initial, rng)
    }

    fn rejected(keys: &Groth16Keys, initial: &Groth16Keys, rng: &mut ChaCha20Rng) -> bool {
        matches!(
            verify_keys_match_initial(keys, initial, rng),
            Err(CeremonyError::KeysDoNotMatchCircuit { .. })
        )
    }

    #[test]
    fn honest_keys_match_the_initial_ones() {
        let (keys, initial, mut rng) = contributed();
        verify_keys_match_initial(&keys, &initial, &mut rng).expect("only δ changed");
        assert!(proves(&keys, 5, &mut rng));
    }

    /// A coordinator who ships `γ = δ` (no secret needed) lets anyone prove anything:
    /// `A = α`, `B = β`, `C = −IC(x)`. The chain and its δ checks still pass; the
    /// comparison with the initial keys doesn't.
    #[test]
    fn a_coordinator_setting_gamma_to_delta_is_caught() {
        let (mut keys, initial, mut rng) = contributed();
        keys.verifying_key.gamma_g2 = keys.verifying_key.delta_g2;
        keys.proving_key.vk = keys.verifying_key.clone();
        let vk = &keys.verifying_key;
        // Any `y`: 3 isn't a square of an integer.
        let y = Fr::from(3u64);
        let ic = vk.gamma_abc_g1[0].into_group() + vk.gamma_abc_g1[1] * y;
        let forged = xark_groth16::Proof {
            a: vk.alpha_g1,
            b: vk.beta_g2,
            c: (-ic).into_affine(),
        };
        assert!(
            xark_groth16::verify(vk, &[y], &forged).unwrap(),
            "the forgery verifies under γ = δ"
        );
        assert!(rejected(&keys, &initial, &mut rng));
    }

    #[test]
    fn any_other_changed_part_is_caught() {
        let (keys, initial, mut rng) = contributed();
        let g1 = G1Affine::generator();
        let tweak = |f: &dyn Fn(&mut Groth16Keys)| {
            let mut k = keys.clone();
            f(&mut k);
            k
        };
        let cases: Vec<(&str, Groth16Keys)> = vec![
            (
                "α",
                tweak(&|k| {
                    k.verifying_key.alpha_g1 = g1;
                    k.proving_key.vk.alpha_g1 = g1;
                }),
            ),
            (
                "IC",
                tweak(&|k| {
                    k.verifying_key.gamma_abc_g1[1] = g1;
                    k.proving_key.vk.gamma_abc_g1[1] = g1;
                }),
            ),
            ("vk copy", tweak(&|k| k.verifying_key.gamma_abc_g1[0] = g1)),
            ("A", tweak(&|k| k.proving_key.a_query[0] = g1)),
            ("H", tweak(&|k| k.proving_key.h_query[0] = g1)),
            (
                "L",
                tweak(&|k| {
                    let l = &mut k.proving_key.l_query;
                    l[0] = (l[0] * Fr::from(2u64)).into_affine();
                }),
            ),
        ];
        for (name, k) in cases {
            assert!(rejected(&k, &initial, &mut rng), "a changed {name} passed");
        }
    }
}
