#![allow(dead_code)]
//! **Reference only (tests).** The original arkworks-based phase-2 setup, kept so
//! `xark-groth16`'s own `phase2_setup` (what `xark setup --ptau-file` and
//! `xark ceremony init` run) is checked byte-for-byte against an independent
//! implementation. Production code doesn't use it.
//!
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
use ark_ff::{Field, One, Zero};
use ark_groth16::{ProvingKey, VerifyingKey};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, OptimizationGoal, R1CS_PREDICATE_LABEL, SynthesisMode,
};
use rand::RngCore;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use xark_backend::ptau::{Phase2Error, PtauFile, check_ptau_covers_circuit};

/// Run the phase-2 deterministic setup from `ptau` and `randomness_seed`.
///
/// `circuit` is consumed by [`ConstraintSynthesizer::generate_constraints`]
/// in Setup mode (no witness values are required).
pub fn setup_from_ptau<C: ConstraintSynthesizer<Fr>>(
    circuit: C,
    ptau: &PtauFile,
    randomness_seed: &[u8; 32],
) -> Result<(ProvingKey<Bn254>, VerifyingKey<Bn254>), Phase2Error> {
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

    // The row-major scatter writes to shared columns, so it can't parallelize
    // over rows without races. Transpose each matrix to column-major once
    // (cheap), then sum every column's group contribution independently across
    // the rayon pool — this is the dominant cost of setup (millions of curve
    // scalar-muls).
    use rayon::prelude::*;
    let transpose = |mat: &[Vec<(Fr, usize)>]| -> Vec<Vec<(usize, Fr)>> {
        let mut cols: Vec<Vec<(usize, Fr)>> = vec![Vec::new(); total_vars];
        for (row_idx, row) in mat.iter().enumerate() {
            for (coeff, col) in row {
                cols[*col].push((row_idx, *coeff));
            }
        }
        cols
    };
    let (cols_a, cols_b, cols_c) = (transpose(mat_a), transpose(mat_b), transpose(mat_c));

    // Most R1CS coefficients are ±1, and `Projective * Fr::ONE` still runs a
    // full 254-bit double-and-add. Special-case ±1 to a plain group add/sub to
    // skip the scalar-mul for the ~90%+ of nonzeros that are ±1.
    let neg_one = -Fr::one();
    let weight = |base: G1Projective, coeff: &Fr| -> G1Projective {
        if coeff.is_one() {
            base
        } else if *coeff == neg_one {
            -base
        } else {
            base * coeff
        }
    };
    let weight_g2 = |base: G2Projective, coeff: &Fr| -> G2Projective {
        if coeff.is_one() {
            base
        } else if *coeff == neg_one {
            -base
        } else {
            base * coeff
        }
    };

    // mat_a → a_g1 (already seeded with the pad-row contributions above), beta_a_g1
    a_g1.par_iter_mut()
        .zip(beta_a_g1.par_iter_mut())
        .zip(cols_a.par_iter())
        .for_each(|((a, ba), col)| {
            for (row, coeff) in col {
                *a += weight(lambda_g1[*row], coeff);
                *ba += weight(lambda_beta_g1[*row], coeff);
            }
        });
    // mat_b → b_g1, b_g2, alpha_b_g1
    b_g1.par_iter_mut()
        .zip(b_g2.par_iter_mut())
        .zip(alpha_b_g1.par_iter_mut())
        .zip(cols_b.par_iter())
        .for_each(|(((bg1, bg2), abg1), col)| {
            for (row, coeff) in col {
                *bg1 += weight(lambda_g1[*row], coeff);
                *bg2 += weight_g2(lambda_g2[*row], coeff);
                *abg1 += weight(lambda_alpha_g1[*row], coeff);
            }
        });
    // mat_c → w_g1
    w_g1.par_iter_mut()
        .zip(cols_c.par_iter())
        .for_each(|(w, col)| {
            for (row, coeff) in col {
                *w += weight(lambda_g1[*row], coeff);
            }
        });

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
    let combined: Vec<G1Projective> = (0..total_vars)
        .into_par_iter()
        .map(|i| beta_a_g1[i] + alpha_b_g1[i] + w_g1[i])
        .collect();

    // Scale (γ⁻¹ / δ⁻¹) in parallel, then batch-normalize to affine (one field
    // inversion per vector via Montgomery's trick, not one per point).
    let gamma_abc_proj: Vec<G1Projective> = combined[..num_instance]
        .par_iter()
        .map(|c| *c * gamma_inv)
        .collect();
    let gamma_abc_g1 = G1Projective::normalize_batch(&gamma_abc_proj);

    let l_query_proj: Vec<G1Projective> = combined[num_instance..total_vars]
        .par_iter()
        .map(|c| *c * delta_inv)
        .collect();
    let l_query = G1Projective::normalize_batch(&l_query_proj);

    // -------------------------------------------------------------------
    // 7) `h_query[k] = δ⁻¹ · (τ^{N+k} - τ^k) G1` for k = 0..N-1.
    // `t(τ) = τ^N - 1`, so `τ^k · t(τ) = τ^{N+k} - τ^k`.
    // -------------------------------------------------------------------
    let h_len = n - 1; // m_raw - 1 in ark-groth16 terms (number of h coeffs)
    let h_query_proj: Vec<G1Projective> = (0..h_len)
        .into_par_iter()
        .map(|k| (ptau.tau_g1[n + k].into_group() - ptau.tau_g1[k].into_group()) * delta_inv)
        .collect();
    let h_query = G1Projective::normalize_batch(&h_query_proj);

    // -------------------------------------------------------------------
    // 8) Variable-batch queries: a_g1, b_g1, b_g2 cover ALL variables
    // (index 0..total_vars) projected onto the affine form (batch-normalized).
    // -------------------------------------------------------------------
    let a_query = G1Projective::normalize_batch(&a_g1);
    let b_g1_query = G1Projective::normalize_batch(&b_g1);
    let b_g2_query = G2Projective::normalize_batch(&b_g2);

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

    Ok((pk, vk))
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
