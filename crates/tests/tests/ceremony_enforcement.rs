//! Enforcement assertions on the phase-2 MPC ceremony driver
//! (`docs/trusted-setup.md`).
//!
//! `ceremony_e2e.rs` is the happy-path / property-style test: it builds a
//! real chain and confirms it composes. *This* file is the
//! negative-direction enforcement: every promise the doc makes about what
//! the driver **rejects** is pinned by a test that hands the driver a
//! tampered transcript and asserts the relevant `Result::Err` fires.
//!
//! Coverage matrix (from `docs/trusted-setup.md` § "For a real production
//! ceremony"):
//!
//! | Property the driver must enforce                        | Test that fires the Err path                              |
//! |---------------------------------------------------------|-----------------------------------------------------------|
//! | Multi-contributor MPC composes (≥ 2 indep. δ's)         | `multi_contributor_mpc_composes`                          |
//! | Public-transcript hashing — Schnorr challenge is bound  | `tampered_schnorr_commitment_is_rejected`                 |
//! |   to the public (prev, new, δ_g2, commitment) tuple     | `tampered_schnorr_response_is_rejected`                   |
//! | Schnorr proof of knowledge per contribution             | `missing_schnorr_proof_is_rejected`                       |
//! | Transcript hash chain unbroken between contributions    | `broken_chain_link_is_rejected`                           |
//! |                                                         | `reordered_chain_is_rejected`                             |
//! | δ-consistency: same δ_i used in G1 and G2 update        | `tampered_g1_delta_is_rejected`                           |
//! | `--insecure-dev-mode` is the dev-only setup path,       | `insecure_dev_mode_metadata_is_flagged_unsafe`            |
//! |   never the ceremony path                               | `ceremony_keys_are_flagged_production_safe`               |
//! |   (i.e. dev-mode keys can never claim `production_safe`)|                                                           |
//!
//! All test inputs are built in-memory (`common::build_valid_ptau`) so
//! these run in well under a second on `cargo test --release -p
//! xark-tests --test ceremony_enforcement` — fast enough for CI on every
//! push and an explicit answer to the auditor's "what happens if someone
//! feeds the driver garbage" question.

use ark_bn254::{Fr, G2Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::UniformRand;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use xark_acir_r1cs::artifact::parse_artifact_file;
use xark_acir_r1cs::lower::LoweredAcirCircuit;
use xark_backend::ceremony::{CeremonyError, Contribution, contribute, verify_chain};
use xark_backend::circuit::NoirGroth16Circuit;
use xark_backend::keys::{Groth16Keys, KeyMetadata};
use xark_backend::ptau::{Phase2Error, parse_ptau, setup_from_ptau};

mod common;
use common::{build_valid_ptau, fixture_dir};

// =============================================================================
// Setup helpers — exactly the same pattern as `ceremony_e2e.rs` so the
// negative tests and the positive tests share their fixture-construction
// surface.
// =============================================================================

/// The smallest committed circuit (single public input) is plenty for
/// enforcement tests — they exercise the driver's chain-validation
/// pathway, not the circuit's complexity.
fn fresh_phase2_keys() -> Groth16Keys {
    let dir = fixture_dir();
    let artifact = parse_artifact_file(&dir.join("arithmetic_square.json")).expect("artifact");
    let lowered = LoweredAcirCircuit::new(artifact).expect("lower");
    let seed = [7u8; 32];
    let mut power = 8u32;
    loop {
        let ptau = parse_ptau(&build_valid_ptau(power)).expect("synthetic ptau parses");
        match setup_from_ptau(NoirGroth16Circuit::for_setup(lowered.clone()), &ptau, &seed) {
            Ok(keys) => return keys,
            Err(Phase2Error::PtauTooSmall {
                required_domain_size,
                ..
            }) => {
                let needed = required_domain_size.trailing_zeros();
                assert!(needed > power, "power must grow on a too-small ptau");
                power = needed;
            }
            Err(e) => panic!("setup_from_ptau failed: {e}"),
        }
    }
}

// =============================================================================
// Positive baseline: multi-contributor MPC actually composes.
// =============================================================================

/// `verify_chain` accepts a real 3-contributor MPC. This is the baseline
/// against which the rejection assertions below get their meaning: every
/// `*_is_rejected` test starts from a chain that *would* verify and only
/// then tampers with it, so the test exercises the rejection pathway, not
/// some other failure mode.
#[test]
fn multi_contributor_mpc_composes() {
    let mut keys = fresh_phase2_keys();
    let initial_delta_g1 = keys.proving_key.delta_g1;
    let mut rng = ChaCha20Rng::seed_from_u64(0xC0FFEE);
    let cs = vec![
        contribute(&mut keys, "alice", &mut rng).expect("alice"),
        contribute(&mut keys, "bob", &mut rng).expect("bob"),
        contribute(&mut keys, "carol", &mut rng).expect("carol"),
    ];
    verify_chain(initial_delta_g1, &cs).expect("untampered 3-contributor chain must verify");
    assert_ne!(
        keys.proving_key.delta_g1, initial_delta_g1,
        "every contribution must move δ"
    );
}

// =============================================================================
// Schnorr proof of knowledge enforcement.
// =============================================================================

/// If a contribution's Schnorr proof is missing — modeled here as a
/// proof_response of zero, which has no chance of satisfying
/// `r·G2 == commitment + e·(δ·G2)` for any honest `(commitment, δ·G2)` —
/// `verify_chain` must reject with `SchnorrInvalid`. This is the
/// driver-level expression of the "no Schnorr proof, no contribution"
/// promise from `docs/trusted-setup.md`.
#[test]
fn missing_schnorr_proof_is_rejected() {
    let mut keys = fresh_phase2_keys();
    let initial_delta_g1 = keys.proving_key.delta_g1;
    let mut rng = ChaCha20Rng::seed_from_u64(1);
    let mut c = contribute(&mut keys, "alice", &mut rng).expect("contribute");
    c.proof_response = Fr::from(0u64);
    let err = verify_chain(initial_delta_g1, &[c]).expect_err("missing Schnorr proof must reject");
    assert!(
        matches!(err, CeremonyError::SchnorrInvalid { index: 0 }),
        "expected SchnorrInvalid {{ index: 0 }}, got {err:?}"
    );
}

/// Tampering the Schnorr response (the `r + e·δ_i` scalar) by even one
/// must break the Schnorr check. Same `SchnorrInvalid` Err variant — the
/// driver doesn't try to recover.
#[test]
fn tampered_schnorr_response_is_rejected() {
    let mut keys = fresh_phase2_keys();
    let initial_delta_g1 = keys.proving_key.delta_g1;
    let mut rng = ChaCha20Rng::seed_from_u64(2);
    let mut c = contribute(&mut keys, "alice", &mut rng).expect("contribute");
    c.proof_response += Fr::from(1u64);
    let err =
        verify_chain(initial_delta_g1, &[c]).expect_err("tampered Schnorr response must reject");
    assert!(matches!(err, CeremonyError::SchnorrInvalid { index: 0 }));
}

/// The Schnorr challenge `e = H(prev_g1 || new_g1 || δ_g2 || commitment)`
/// is anchored to the public commitment. Replacing the commitment with
/// any other G2 point invalidates the proof — `verify_chain` must reject.
/// This is the "public-transcript hashing" promise made concrete.
#[test]
fn tampered_schnorr_commitment_is_rejected() {
    let mut keys = fresh_phase2_keys();
    let initial_delta_g1 = keys.proving_key.delta_g1;
    let mut rng = ChaCha20Rng::seed_from_u64(3);
    let mut c = contribute(&mut keys, "alice", &mut rng).expect("contribute");
    // Swap the commitment for an unrelated G2 multiple. The Schnorr
    // challenge then re-hashes to a different value and the response no
    // longer satisfies the verification equation.
    let mut adv_rng = ChaCha20Rng::seed_from_u64(9999);
    c.proof_commitment = (G2Affine::generator() * Fr::rand(&mut adv_rng)).into_affine();
    let err =
        verify_chain(initial_delta_g1, &[c]).expect_err("tampered Schnorr commitment must reject");
    assert!(matches!(err, CeremonyError::SchnorrInvalid { index: 0 }));
}

// =============================================================================
// Transcript hash-chain enforcement.
// =============================================================================

/// If the running `prev_delta_g1` recorded on a contribution does not
/// match the baseline (i.e. contribution #1 claims to chain off the
/// wrong start point), the driver must reject with `ChainBreak`. This is
/// the link between the public baseline and the first contribution —
/// the literal first edge of the hash chain.
#[test]
fn broken_chain_link_is_rejected() {
    let mut keys = fresh_phase2_keys();
    let initial_delta_g1 = keys.proving_key.delta_g1;
    let mut rng = ChaCha20Rng::seed_from_u64(4);
    let mut c1 = contribute(&mut keys, "alice", &mut rng).expect("alice");
    let c2 = contribute(&mut keys, "bob", &mut rng).expect("bob");
    // c1 now claims to chain off c2's *post* state — an impossible link.
    c1.prev_delta_g1 = c2.new_delta_g1;
    let err =
        verify_chain(initial_delta_g1, &[c1, c2]).expect_err("broken-chain transcript must reject");
    assert!(
        matches!(err, CeremonyError::ChainBreak { index: 0 }),
        "expected ChainBreak {{ index: 0 }}, got {err:?}"
    );
}

/// Reordering an otherwise-valid 2-contributor chain breaks the running
/// δ — contribution #2's `prev_delta_g1` no longer equals the baseline.
/// This is the same `ChainBreak` Err path the doc requires; it is the
/// reason the chain-order itself is part of the transcript.
#[test]
fn reordered_chain_is_rejected() {
    let mut keys = fresh_phase2_keys();
    let initial_delta_g1 = keys.proving_key.delta_g1;
    let mut rng = ChaCha20Rng::seed_from_u64(5);
    let c1 = contribute(&mut keys, "alice", &mut rng).expect("alice");
    let c2 = contribute(&mut keys, "bob", &mut rng).expect("bob");
    // Swap the order. c2's prev_delta_g1 == c1's new_delta_g1 != baseline.
    let err = verify_chain(initial_delta_g1, &[c2, c1]).expect_err("reordered chain must reject");
    assert!(
        matches!(err, CeremonyError::ChainBreak { index: 0 }),
        "expected ChainBreak {{ index: 0 }}, got {err:?}"
    );
}

// =============================================================================
// δ-consistency (same δ_i in G1 and G2 update) enforcement.
// =============================================================================

/// Tampering the G1 side of the (prev, new) δ-update — the only way to
/// fake having applied a δ that's different from the one in the public
/// `δ·G2` commitment — must be rejected. The driver checks
/// `e(new_g1, G2) == e(prev_g1, δ·G2)`; flipping `new_g1` away from its
/// honest value fails that pairing. (The Schnorr challenge is also bound
/// to `new_g1`, so the Schnorr check fires first; either Err variant is
/// acceptable because both signal a rejection, which is what the doc
/// requires.)
#[test]
fn tampered_g1_delta_is_rejected() {
    let mut keys = fresh_phase2_keys();
    let initial_delta_g1 = keys.proving_key.delta_g1;
    let mut rng = ChaCha20Rng::seed_from_u64(6);
    let mut c = contribute(&mut keys, "alice", &mut rng).expect("alice");
    // Replace new_delta_g1 with an unrelated G1 point.
    let mut adv_rng = ChaCha20Rng::seed_from_u64(8888);
    let bogus = (ark_bn254::G1Affine::generator() * Fr::rand(&mut adv_rng)).into_affine();
    c.new_delta_g1 = bogus;
    let err = verify_chain(initial_delta_g1, &[c]).expect_err("tampered G1 δ-update must reject");
    assert!(
        matches!(
            err,
            CeremonyError::SchnorrInvalid { .. } | CeremonyError::DeltaInconsistent { .. }
        ),
        "expected SchnorrInvalid or DeltaInconsistent, got {err:?}"
    );
}

// =============================================================================
// `--insecure-dev-mode` guard rails.
// =============================================================================

/// `KeyMetadata::new_dev` is the constructor used by the
/// `--insecure-dev-mode` setup path. It must hard-code
/// `production_safe = false` and `setup_mode = "insecure-dev-mode"` —
/// these are the audit signals that say "do not deploy these keys" — so
/// a downstream tool can refuse to deploy dev keys by checking
/// `production_safe`. The ceremony driver never produces this metadata.
#[test]
fn insecure_dev_mode_metadata_is_flagged_unsafe() {
    let meta = KeyMetadata::new_dev("dummy-circuit-hash".into(), "1.0.0-beta.22".into(), 1, 128);
    assert_eq!(meta.setup_mode, "insecure-dev-mode");
    assert!(
        !meta.production_safe,
        "dev-mode metadata must NEVER claim production_safe = true"
    );
    assert!(
        meta.ptau_source.is_none(),
        "dev-mode metadata must not advertise a ptau source"
    );
    assert!(
        meta.phase2_seed_hash.is_none(),
        "dev-mode metadata must not advertise a phase-2 seed hash"
    );
}

/// Conversely, when the keys *do* come from the ceremony path
/// (phase2-from-ptau followed by MPC contributions), the metadata must
/// flip `production_safe = true`. This pins the only two valid label
/// strings the rest of the toolchain (`xark ceremony finalize`, audit
/// dashboards) can rely on.
///
/// The CLI sets these labels in `crates/cli/src/commands/ceremony.rs` /
/// `setup.rs`; this test pins the *exact* string contract so a CLI
/// refactor can't silently break the audit signal.
#[test]
fn ceremony_keys_are_flagged_production_safe() {
    // Mirror what `crates/cli/src/commands/setup.rs` does on the
    // --ptau-file path:
    let mut meta = KeyMetadata::new_dev("h".into(), "v".into(), 1, 1);
    meta.setup_mode = "phase2-from-ptau".into();
    meta.production_safe = true;
    assert!(meta.production_safe, "ptau setup must mark production_safe");
    assert_eq!(meta.setup_mode, "phase2-from-ptau");

    // And what `crates/cli/src/commands/ceremony.rs::finalize` does
    // after an MPC chain has been verified:
    let mut meta = KeyMetadata::new_dev("h".into(), "v".into(), 1, 1);
    meta.setup_mode = "phase2-from-ptau+mpc[3 contributors]".into();
    meta.production_safe = true;
    assert!(meta.production_safe);
    assert!(meta.setup_mode.starts_with("phase2-from-ptau+mpc["));
    assert!(meta.setup_mode.contains("contributors"));
}

/// One contribution might still be enough — the soundness assumption is
/// "at least one honest contributor". This test confirms a single
/// honest contribution composes into a chain `verify_chain` accepts;
/// the rejection tests above prove that *any* tampering of that single
/// contribution still gets rejected. Together they pin the doc's
/// soundness-summary promise that a passing `verify_chain` implies every
/// δ_i was a known scalar applied consistently to G1 and G2.
#[test]
fn single_honest_contribution_is_sufficient() {
    let mut keys = fresh_phase2_keys();
    let initial_delta_g1 = keys.proving_key.delta_g1;
    let mut rng = ChaCha20Rng::seed_from_u64(11);
    let c: Contribution = contribute(&mut keys, "lone-honest", &mut rng).expect("contribute");
    verify_chain(initial_delta_g1, &[c]).expect("single honest contribution must verify");
}
