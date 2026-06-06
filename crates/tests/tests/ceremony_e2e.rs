//! Fully self-contained, in-process end-to-end tests of xark's **own** trusted
//! setup ceremony — no snarkjs, no committed `.ptau` fixture.
//!
//! Each test exercises the whole production setup path with xark code only:
//!
//! 1. **Phase 1** — synthesize a valid Powers-of-Tau transcript in memory
//!    (`common::build_valid_ptau`, snarkjs binary layout) and parse it with the
//!    real `parse_ptau`.
//! 2. **Phase 2** — derive `ProvingKey`/`VerifyingKey` for a real circuit via
//!    `setup_from_ptau`.
//! 3. **MPC** — run two independent `contribute` steps and confirm the whole
//!    contribution chain with `verify_chain` (and that a reordered chain fails).
//! 4. **Use the finalized keys** — prove a real witness, verify the proof, and
//!    confirm **every** public input is bound (tampering any one fails).
//!
//! The phase-1 toxic waste is known to the test (it builds the transcript), so
//! this proves the pipeline is *correct* (well-formed keys, valid proofs, every
//! public input bound), not that a real ceremony is *secret*. Secrecy is an
//! operational property of an actual multi-party ceremony — see
//! `docs/trusted-setup.md`.

use ark_bn254::Fr;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use xark_acir_r1cs::artifact::parse_artifact_file;
use xark_acir_r1cs::lower::LoweredAcirCircuit;
use xark_acir_r1cs::witness::{WitnessMap, parse_witness_file};
use xark_backend::ceremony::{contribute, verify_chain};
use xark_backend::circuit::NoirGroth16Circuit;
use xark_backend::keys::Groth16Keys;
use xark_backend::ptau::{Phase2Error, parse_ptau, setup_from_ptau};

mod common;
use common::{build_valid_ptau, fixture_dir};

/// Derive phase-2 keys for `lowered` from a synthetic in-memory ptau, picking
/// the smallest sufficient ptau power. The first attempt that is too small
/// reports the exact required domain size, so this converges in one retry.
fn ceremony_setup(lowered: &LoweredAcirCircuit, seed: &[u8; 32]) -> Groth16Keys {
    let mut power = 8u32;
    loop {
        let ptau = parse_ptau(&build_valid_ptau(power)).expect("synthetic ptau parses");
        match setup_from_ptau(NoirGroth16Circuit::for_setup(lowered.clone()), &ptau, seed) {
            Ok(keys) => return keys,
            Err(Phase2Error::PtauTooSmall {
                required_domain_size,
                ..
            }) => {
                // `required_domain_size` is already a power of two.
                let needed = required_domain_size.trailing_zeros();
                assert!(needed > power, "power must grow on a too-small ptau");
                power = needed;
            }
            Err(e) => panic!("setup_from_ptau failed: {e}"),
        }
    }
}

/// Run the full ceremony → prove → verify path for one committed circuit and
/// assert the security-relevant properties. `expected_pi` documents (and pins)
/// how many public inputs the circuit has.
fn run_ceremony_e2e(circuit: &str, expected_pi: usize) {
    // --- the real circuit ----------------------------------------------------
    let dir = fixture_dir();
    let artifact = parse_artifact_file(&dir.join(format!("{circuit}.json"))).expect("artifact");
    let witness = parse_witness_file(&dir.join(format!("{circuit}.gz"))).expect("witness");
    let lowered = LoweredAcirCircuit::new(artifact).expect("lower");

    let public_of = |w: &WitnessMap<Fr>| -> Vec<Fr> {
        lowered
            .artifact
            .public_inputs
            .iter()
            .map(|idx| *w.get(idx).expect("public input present in witness"))
            .collect()
    };

    let pi = public_of(&witness);
    assert_eq!(
        pi.len(),
        expected_pi,
        "{circuit} should have {expected_pi} public input(s)"
    );

    // --- phase 1 + 2: synthetic ptau (no snarkjs) → keys ---------------------
    let seed = [7u8; 32];
    let mut keys = ceremony_setup(&lowered, &seed);
    let initial_delta_g1 = keys.proving_key.delta_g1;

    // --- MPC: two independent contributions ----------------------------------
    let mut rng = ChaCha20Rng::seed_from_u64(0xA11CE);
    let c1 = contribute(&mut keys, "alice", &mut rng).expect("alice contributes");
    let c2 = contribute(&mut keys, "bob", &mut rng).expect("bob contributes");

    // The chain verifies, and the contributions actually moved δ.
    verify_chain(initial_delta_g1, &[c1.clone(), c2.clone()]).expect("contribution chain verifies");
    assert_ne!(
        keys.proving_key.delta_g1, initial_delta_g1,
        "contributions must change δ"
    );
    // A reordered chain must be rejected.
    assert!(
        verify_chain(initial_delta_g1, &[c2, c1]).is_err(),
        "reordered contribution chain must fail verification"
    );

    // --- use the finalized keys: prove a real witness and verify -------------
    let proof = xark_backend::prove(
        &keys.proving_key,
        NoirGroth16Circuit::for_proving(lowered.clone(), witness.clone()),
        &pi,
        &mut rng,
    )
    .expect("prove with ceremony keys");

    assert!(
        xark_backend::verify(&keys.verifying_key, &proof, &pi).expect("verify"),
        "proof from ceremony keys must verify under the ceremony VK"
    );

    // Every public input is bound: flipping any single one makes the same proof
    // fail under the same VK. (For a 16-input circuit this is 16 distinct
    // statements the proof must be pinned to.)
    for i in 0..pi.len() {
        let mut bad = pi.clone();
        bad[i] += Fr::from(1u64);
        assert!(
            !xark_backend::verify(&keys.verifying_key, &proof, &bad).expect("verify (tampered)"),
            "{circuit}: tampering public input #{i} must invalidate the proof"
        );
    }
}

#[test]
fn arithmetic_square_single_public_input() {
    run_ceremony_e2e("arithmetic_square", 1);
}

#[test]
fn mixed_pi_two_public_inputs() {
    run_ceremony_e2e("mixed_pi", 2);
}

#[test]
fn large_pi_sixteen_public_inputs() {
    run_ceremony_e2e("large_pi", 16);
}
