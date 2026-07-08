//! Deterministic phase-2 Groth16 setup from a parsed Powers-of-Tau
//! transcript.
//!
//! Given a phase-1 transcript [`crate::ptau::PtauFile`] and a circuit
//! `C: ConstraintSynthesizer<Fr>`, this module computes a circuit-specific
//! `ProvingKey<Bn254>` + `VerifyingKey<Bn254>` without ever materialising
//! the trapdoor `τ` as a scalar. The phase-2 secrets `γ, δ` are derived
//! deterministically from a user-supplied 32-byte seed via ChaCha20.
//!
//! # Algorithm
//!
//! Let `N` be the QAP domain size, `M` the number of variables, and the
//! R1CS matrices be `A, B, C ∈ Fr^{N × M}` (sparse).
//!
//! 1. Compute Lagrange basis evaluations in the group:
//!    `Λ_g1[i] = [L_i(τ)]G1` for `i = 0..N-1` by inverse-FFT-ing
//!    `ptau.tau_g1[0..N]` (treated as `G1Projective`). Same for
//!    `Λ_g2`, `Λ_α_g1` (from `alpha_tau_g1`), `Λ_β_g1` (from `beta_tau_g1`).
//!
//! 2. For each variable column `j`, accumulate the sparse R1CS column
//!    against the four Lagrange tables to get
//!    `[u_j(τ)]G1, [v_j(τ)]G1, [v_j(τ)]G2, [α·v_j(τ)]G1, [β·u_j(τ)]G1, [w_j(τ)]G1`.
//!
//! 3. Combine: `gamma_abc[j] = γ⁻¹ · (β·u_j(τ) + α·v_j(τ) + w_j(τ))` for
//!    the public-input slot `j`, and `l_query[j] = δ⁻¹ · (...)` for the
//!    private witness slot `j`.
//!
//! 4. `h_query[k] = δ⁻¹ · [τ^k · t(τ)]G1` where the vanishing polynomial
//!    `t(X) = X^N - 1`, so `[τ^k · t(τ)]G1 = ptau.tau_g1[N+k] - ptau.tau_g1[k]`.
//!
//! 5. Construct the `ProvingKey` and `VerifyingKey`.
//!
//! # Soundness
//!
//! `τ, α, β` come from the phase-1 transcript; `γ, δ` are drawn from the caller's
//! seed. `τ, α, β` are safe unless phase-1 was malformed. `γ, δ` are **also
//! trapdoor components**: anyone with the phase-2 seed can forge proofs, so a
//! single-party phase-2 is safe only once the seed is discarded (a trustless
//! phase-2 needs a multi-party contribution).
//!
//! **The output keys are valid for production use only if (a) the phase-1
//! `.ptau` transcript came from an audited ceremony and (b) the
//! randomness seed was generated via OS RNG and discarded after use.**

use ark_bn254::{Bn254, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, Zero};
use ark_groth16::{ProvingKey, VerifyingKey};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, OptimizationGoal, SynthesisMode, R1CS_PREDICATE_LABEL,
};
use rand::RngCore;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use crate::keys::Groth16Keys;
use crate::ptau::{check_ptau_covers_circuit, Phase2Error, PtauFile};

/// Run the phase-2 deterministic setup from `ptau` and `randomness_seed`.
///
/// `circuit` is consumed by [`ConstraintSynthesizer::generate_constraints`]
/// in Setup mode (no witness values are required).
pub fn setup_from_ptau<C: ConstraintSynthesizer<Fr>>(
    circuit: C,
    ptau: &PtauFile,
    randomness_seed: &[u8; 32],
) -> Result<Groth16Keys, Phase2Error> {
    // -------------------------------------------------------------------
    // 1) Synthesise the circuit in Setup mode and pull out the matrices.
    // -------------------------------------------------------------------
    let cs = ConstraintSystem::<Fr>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(SynthesisMode::Setup);
    circuit
        .generate_constraints(cs.clone())
        .map_err(|e| Phase2Error::CircuitSynthesis(format!("{e}")))?;
    cs.finalize();

    let num_constraints = cs.num_constraints();
    let num_instance = cs.num_instance_variables();
    let num_witness = cs.num_witness_variables();
    let qap_num_variables = (num_instance - 1) + num_witness;

    check_ptau_covers_circuit(ptau, num_constraints, num_instance)?;

    // arkworks 0.6: `to_matrices` returns a map keyed by predicate label; the
    // plain R1CS predicate's entry is `[A, B, C]`.
    let matrices_map = cs
        .to_matrices()
        .expect("CS must be finalized to extract matrices");
    let matrices = &matrices_map[R1CS_PREDICATE_LABEL];
    let (mat_a, mat_b, mat_c) = (&matrices[0], &matrices[1], &matrices[2]);

    // -------------------------------------------------------------------
    // 2) Domain of size N = next_pow2(num_constraints + num_instance).
    // -------------------------------------------------------------------
    let domain_size = num_constraints + num_instance;
    let domain = GeneralEvaluationDomain::<Fr>::new(domain_size)
        .ok_or(Phase2Error::DomainConstruction(domain_size))?;
    let n = domain.size();

    // Bounds guard: a transcript from `parse_ptau` always has consistent
    // section lengths, but `setup_from_ptau` is public and `PtauFile`'s fields
    // are `pub`, so a hand-built or malformed transcript could have vectors
    // shorter than the QAP domain requires. Check up front so the slicing /
    // indexing below (`tau_g1[n + k]`, `tau_g2[..n]`, …) returns a graceful
    // error instead of panicking on an out-of-bounds access.
    check_ptau_section_lengths(ptau, n)?;

    // verify the transcript is a consistent (τ, α, β) ladder before deriving keys
    // (a malicious transcript would otherwise yield keys with a known trapdoor)
    crate::ptau::verify_powers_consistency(ptau)?;

    // -------------------------------------------------------------------
    // 3) Compute Lagrange evaluations in the group.
    // -------------------------------------------------------------------
    let lambda_g1: Vec<G1Projective> = ifft_g1_affine(&domain, &ptau.tau_g1[..n]);
    let lambda_g2: Vec<G2Projective> = ifft_g2_affine(&domain, &ptau.tau_g2[..n]);
    let lambda_alpha_g1: Vec<G1Projective> = ifft_g1_affine(&domain, &ptau.alpha_tau_g1[..n]);
    let lambda_beta_g1: Vec<G1Projective> = ifft_g1_affine(&domain, &ptau.beta_tau_g1[..n]);

    // -------------------------------------------------------------------
    // 4) Per-variable QAP evaluations in the group.
    // -------------------------------------------------------------------
    // Each of these vectors is indexed by variable index (0..qap_num_variables+1).
    // Index 0 is the "one" variable, then 1..num_instance are public inputs,
    // then num_instance..num_instance + num_witness are private witnesses.
    let total_vars = qap_num_variables + 1;
    let mut a_g1 = vec![G1Projective::zero(); total_vars];
    let mut b_g1 = vec![G1Projective::zero(); total_vars];
    let mut b_g2 = vec![G2Projective::zero(); total_vars];
    let mut alpha_b_g1 = vec![G1Projective::zero(); total_vars];
    let mut beta_a_g1 = vec![G1Projective::zero(); total_vars];
    let mut w_g1 = vec![G1Projective::zero(); total_vars];

    // Pad rows: ark-groth16's LibsnarkReduction maps each instance variable
    // i ∈ [0, num_instance) onto Lagrange row `num_constraints + i`.
    // Accumulate that into `a_g1[i]` (and only `a`, not `b` or `c`).
    for i in 0..num_instance {
        let row = num_constraints + i;
        a_g1[i] += lambda_g1[row];
        beta_a_g1[i] += lambda_beta_g1[row];
    }

    // For each constraint row, the row's sparse contributions to A, B, C
    // affect the corresponding column's Lagrange-weighted sum.
    for (row_idx, row) in mat_a.iter().enumerate() {
        for (coeff, col) in row {
            a_g1[*col] += lambda_g1[row_idx] * coeff;
            beta_a_g1[*col] += lambda_beta_g1[row_idx] * coeff;
        }
    }
    for (row_idx, row) in mat_b.iter().enumerate() {
        for (coeff, col) in row {
            b_g1[*col] += lambda_g1[row_idx] * coeff;
            b_g2[*col] += lambda_g2[row_idx] * coeff;
            alpha_b_g1[*col] += lambda_alpha_g1[row_idx] * coeff;
        }
    }
    for (row_idx, row) in mat_c.iter().enumerate() {
        for (coeff, col) in row {
            w_g1[*col] += lambda_g1[row_idx] * coeff;
        }
    }

    // -------------------------------------------------------------------
    // 5) Sample γ, δ from the user-supplied seed.
    // -------------------------------------------------------------------
    let mut rng = ChaCha20Rng::from_seed(*randomness_seed);
    let gamma: Fr = sample_nonzero_fr(&mut rng);
    let delta: Fr = sample_nonzero_fr(&mut rng);
    let gamma_inv = gamma.inverse().expect("γ != 0 by construction");
    let delta_inv = delta.inverse().expect("δ != 0 by construction");

    // -------------------------------------------------------------------
    // 6) Compose `combined[i] = β·a + α·b + w`, then split into γ-scaled
    // public-input batch and δ-scaled private-witness batch.
    // -------------------------------------------------------------------
    let mut combined: Vec<G1Projective> = Vec::with_capacity(total_vars);
    for i in 0..total_vars {
        combined.push(beta_a_g1[i] + alpha_b_g1[i] + w_g1[i]);
    }

    let mut gamma_abc_g1: Vec<G1Affine> = Vec::with_capacity(num_instance);
    for c in combined.iter().take(num_instance) {
        gamma_abc_g1.push(((*c) * gamma_inv).into_affine());
    }

    let mut l_query: Vec<G1Affine> = Vec::with_capacity(num_witness);
    for c in combined.iter().take(total_vars).skip(num_instance) {
        l_query.push(((*c) * delta_inv).into_affine());
    }

    // -------------------------------------------------------------------
    // 7) `h_query[k] = δ⁻¹ · (τ^{N+k} - τ^k) G1` for k = 0..N-1.
    // `t(τ) = τ^N - 1`, so `τ^k · t(τ) = τ^{N+k} - τ^k`.
    // -------------------------------------------------------------------
    let h_len = n - 1; // m_raw - 1 in ark-groth16 terms (number of h coeffs)
    let mut h_query: Vec<G1Affine> = Vec::with_capacity(h_len);
    for k in 0..h_len {
        let upper: G1Projective = ptau.tau_g1[n + k].into_group();
        let lower: G1Projective = ptau.tau_g1[k].into_group();
        let diff = upper - lower;
        h_query.push((diff * delta_inv).into_affine());
    }

    // -------------------------------------------------------------------
    // 8) Variable-batch queries: a_g1, b_g1, b_g2 cover ALL variables
    // (index 0..total_vars) projected onto the affine form.
    // -------------------------------------------------------------------
    let a_query: Vec<G1Affine> = a_g1.iter().map(|p| p.into_affine()).collect();
    let b_g1_query: Vec<G1Affine> = b_g1.iter().map(|p| p.into_affine()).collect();
    let b_g2_query: Vec<G2Affine> = b_g2.iter().map(|p| p.into_affine()).collect();

    // -------------------------------------------------------------------
    // 9) Assemble the keys. The α, β, δ G1/G2 elements come from ptau and
    // our locally-chosen γ, δ.
    // -------------------------------------------------------------------
    let alpha_g1 = ptau.alpha_tau_g1[0];
    let beta_g1 = ptau.beta_tau_g1[0];
    let beta_g2 = ptau.beta_g2;
    let g2_generator = G2Affine::generator();
    let g1_generator = G1Affine::generator();
    let gamma_g2 = (g2_generator * gamma).into_affine();
    let delta_g2 = (g2_generator * delta).into_affine();
    let delta_g1 = (g1_generator * delta).into_affine();

    let vk = VerifyingKey::<Bn254> {
        alpha_g1,
        beta_g2,
        gamma_g2,
        delta_g2,
        gamma_abc_g1,
    };

    let pk = ProvingKey::<Bn254> {
        vk: vk.clone(),
        beta_g1,
        delta_g1,
        a_query,
        b_g1_query,
        b_g2_query,
        h_query,
        l_query,
    };

    Ok(Groth16Keys {
        proving_key: pk,
        verifying_key: vk,
    })
}

/// Verify the ptau vectors are long enough for a QAP domain of size `n`.
///
/// The setup below reads `tau_g1[0..2n-1]` (Lagrange table `[..n]` plus the
/// `h_query` diffs `tau_g1[n + k]` for `k < n-1`), and `[..n]` of each of
/// `tau_g2`, `alpha_tau_g1`, `beta_tau_g1`. A malformed transcript with shorter
/// vectors would otherwise panic on an out-of-bounds index.
fn check_ptau_section_lengths(ptau: &PtauFile, n: usize) -> Result<(), Phase2Error> {
    let checks: [(&'static str, usize, usize); 4] = [
        ("tau_g1", 2 * n - 1, ptau.tau_g1.len()),
        ("tau_g2", n, ptau.tau_g2.len()),
        ("alpha_tau_g1", n, ptau.alpha_tau_g1.len()),
        ("beta_tau_g1", n, ptau.beta_tau_g1.len()),
    ];
    for (section, needed, actual) in checks {
        if actual < needed {
            return Err(Phase2Error::PtauSectionTooShort {
                section,
                needed,
                actual,
            });
        }
    }
    Ok(())
}

/// Inverse-FFT a slice of G1 affine points into a `Vec<G1Projective>`.
fn ifft_g1_affine(domain: &GeneralEvaluationDomain<Fr>, points: &[G1Affine]) -> Vec<G1Projective> {
    let mut buf: Vec<G1Projective> = points.iter().map(|p| p.into_group()).collect();
    domain.ifft_in_place(&mut buf);
    buf
}

/// Inverse-FFT a slice of G2 affine points into a `Vec<G2Projective>`.
fn ifft_g2_affine(domain: &GeneralEvaluationDomain<Fr>, points: &[G2Affine]) -> Vec<G2Projective> {
    let mut buf: Vec<G2Projective> = points.iter().map(|p| p.into_group()).collect();
    domain.ifft_in_place(&mut buf);
    buf
}

/// Sample a nonzero `Fr` from `rng`. Used to derive γ, δ from the user's
/// randomness seed.
fn sample_nonzero_fr(rng: &mut impl RngCore) -> Fr {
    loop {
        let mut bytes = [0u8; 32];
        rng.fill_bytes(&mut bytes);
        let candidate = Fr::from_random_bytes(&bytes).unwrap_or_else(Fr::zero);
        if !candidate.is_zero() {
            return candidate;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ptau::{Phase2Error, PtauFile};
    use ark_bn254::{Bn254, Fr};
    use ark_ec::{CurveGroup, PrimeGroup};
    use ark_ff::{One, UniformRand};
    use ark_groth16::Groth16;
    use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
    use ark_snark::SNARK;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    /// A test circuit: `x · x = y` with `y` public.
    #[derive(Clone)]
    struct Square {
        x: Option<Fr>,
        y: Option<Fr>,
    }

    impl ConstraintSynthesizer<Fr> for Square {
        fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
            let y = cs.new_input_variable(|| self.y.ok_or(SynthesisError::AssignmentMissing))?;
            let x = cs.new_witness_variable(|| self.x.ok_or(SynthesisError::AssignmentMissing))?;
            cs.enforce_r1cs_constraint(
                || ark_relations::gr1cs::LinearCombination::from((Fr::one(), x)),
                || ark_relations::gr1cs::LinearCombination::from((Fr::one(), x)),
                || ark_relations::gr1cs::LinearCombination::from((Fr::one(), y)),
            )?;
            Ok(())
        }
    }

    /// Build an in-memory `PtauFile` from a chosen `(τ, α, β)`. This is
    /// only for tests — a real ptau comes from a multi-party ceremony.
    fn fake_ptau(power: u32, tau: Fr, alpha: Fr, beta: Fr) -> PtauFile {
        let n = 1usize << power;
        let g1 = ark_bn254::G1Projective::generator();
        let g2 = ark_bn254::G2Projective::generator();
        let mut tau_g1 = Vec::with_capacity(2 * n - 1);
        let mut tau_g2 = Vec::with_capacity(n);
        let mut alpha_tau_g1 = Vec::with_capacity(n);
        let mut beta_tau_g1 = Vec::with_capacity(n);

        let mut tau_pow = Fr::one();
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

        PtauFile {
            power,
            tau_g1,
            tau_g2,
            alpha_tau_g1,
            beta_tau_g1,
            beta_g2,
        }
    }

    #[test]
    fn phase2_setup_produces_keys_that_verify_a_real_proof() {
        // Build a fake ptau, run phase-2, produce a proof, verify it.
        let mut rng = ChaCha20Rng::seed_from_u64(0xABCDEF);
        let tau = Fr::rand(&mut rng);
        let alpha = Fr::rand(&mut rng);
        let beta = Fr::rand(&mut rng);
        let ptau = fake_ptau(4, tau, alpha, beta);

        let seed = [42u8; 32];
        let circuit_for_setup = Square { x: None, y: None };
        let keys =
            setup_from_ptau(circuit_for_setup, &ptau, &seed).expect("phase-2 setup succeeds");

        // Prove + verify a concrete instance.
        let circuit_for_proof = Square {
            x: Some(Fr::from(9u64)),
            y: Some(Fr::from(81u64)),
        };
        let proof =
            Groth16::<Bn254>::prove(&keys.proving_key, circuit_for_proof, &mut rng).expect("prove");
        let public_inputs = vec![Fr::from(81u64)];
        let ok = Groth16::<Bn254>::verify(&keys.verifying_key, &public_inputs, &proof)
            .expect("verify call");
        assert!(ok, "phase-2 keys must verify a valid proof");
    }

    #[test]
    fn phase2_rejects_ptau_too_small() {
        let mut rng = ChaCha20Rng::seed_from_u64(1);
        let ptau = fake_ptau(
            1,
            Fr::rand(&mut rng),
            Fr::rand(&mut rng),
            Fr::rand(&mut rng),
        );
        let seed = [0u8; 32];
        let result = setup_from_ptau(Square { x: None, y: None }, &ptau, &seed);
        assert!(matches!(result, Err(Phase2Error::PtauTooSmall { .. })));
    }

    #[test]
    fn phase2_rejects_malformed_ptau_with_short_sections() {
        // A transcript whose `power` claims coverage but whose point vectors
        // have been truncated must be rejected gracefully, not panic on an
        // out-of-bounds index in the QAP loop.
        let mut rng = ChaCha20Rng::seed_from_u64(7);
        let mut ptau = fake_ptau(
            4,
            Fr::rand(&mut rng),
            Fr::rand(&mut rng),
            Fr::rand(&mut rng),
        );
        // Truncate tau_g1 to a single point while leaving `power` at 4.
        ptau.tau_g1.truncate(1);
        let seed = [0u8; 32];
        let result = setup_from_ptau(Square { x: None, y: None }, &ptau, &seed);
        assert!(matches!(
            result,
            Err(Phase2Error::PtauSectionTooShort {
                section: "tau_g1",
                ..
            })
        ));
    }

    #[test]
    fn powers_consistency_accepts_valid_and_rejects_tampered() {
        use crate::ptau::verify_powers_consistency;
        let mut rng = ChaCha20Rng::seed_from_u64(0x1234);
        let ptau = fake_ptau(
            4,
            Fr::rand(&mut rng),
            Fr::rand(&mut rng),
            Fr::rand(&mut rng),
        );
        // A genuine (τ, α, β) ladder passes.
        verify_powers_consistency(&ptau).expect("consistent ladder must pass");

        // One G1 power bumped off the ladder → rejected.
        let mut bad = ptau.clone();
        bad.tau_g1[3] = (bad.tau_g1[3].into_group() + G1Projective::generator()).into_affine();
        assert!(
            verify_powers_consistency(&bad).is_err(),
            "tampered tau_g1 power must reject"
        );

        // `beta_g2` no longer sharing β with `beta_tau_g1[0]` → rejected.
        let mut bad_beta = ptau.clone();
        bad_beta.beta_g2 =
            (bad_beta.beta_g2.into_group() + G2Projective::generator()).into_affine();
        assert!(
            verify_powers_consistency(&bad_beta).is_err(),
            "tampered beta_g2 must reject"
        );

        // An arbitrary (non-ladder) `tau_g1[1]` → rejected at the τ-link.
        let mut bad_link = ptau.clone();
        bad_link.tau_g1[1] = (G1Projective::generator() * Fr::from(99u64)).into_affine();
        assert!(
            verify_powers_consistency(&bad_link).is_err(),
            "non-ladder tau_g1[1] must reject"
        );
    }

    #[test]
    fn powers_consistency_rejects_degenerate_toxic_waste() {
        // a trivially-known trapdoor (τ ∈ {0,1}, α = 0, β = 0) passes every ladder
        // yet is fully backdoored, so it must be rejected
        use crate::ptau::verify_powers_consistency;
        let mut rng = ChaCha20Rng::seed_from_u64(0xD00D);
        let (t, a, b) = (Fr::rand(&mut rng), Fr::rand(&mut rng), Fr::rand(&mut rng));
        let zero = Fr::from(0u64);
        let one = Fr::from(1u64);

        assert!(
            verify_powers_consistency(&fake_ptau(4, zero, a, b)).is_err(),
            "τ=0 must reject"
        );
        assert!(
            verify_powers_consistency(&fake_ptau(4, one, a, b)).is_err(),
            "τ=1 must reject"
        );
        assert!(
            verify_powers_consistency(&fake_ptau(4, t, zero, b)).is_err(),
            "α=0 must reject"
        );
        assert!(
            verify_powers_consistency(&fake_ptau(4, t, a, zero)).is_err(),
            "β=0 must reject"
        );
        // The same nonzero (τ, α, β) still passes.
        verify_powers_consistency(&fake_ptau(4, t, a, b)).expect("nonzero toxic waste passes");
    }
}
