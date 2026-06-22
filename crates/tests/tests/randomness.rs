//! Production randomness audit.
//!
//! Asserts that `xark setup` and `xark prove` use OS randomness by default
//! (so two consecutive invocations are non-deterministic) and that the
//! `--deterministic-rng <seed>` escape hatch is byte-reproducible.
//!
//! Both invariants matter for security:
//!
//! - **Setup**: the trapdoor τ is derived from setup randomness. A fixed
//!   seed embedded in the binary would let anyone reading the binary
//!   recover τ and forge proofs. The default path uses `OsRng`.
//! - **Prove**: Groth16 proof randomness blinds the witness across proofs.
//!   Reusing it would leak the witness across two proofs of the same
//!   statement. The default path uses `OsRng`; only the explicit opt-in
//!   `--deterministic-rng` path makes proofs reproducible (for fixtures).

use std::path::Path;

use xark_backend::keys::Groth16Keys;
use xark_backend::proof::ProofBundle;
use xark_backend::serialization::read_public_inputs;

mod common;
use common::{fixture_dir, run, tempdir};

fn read_bytes(path: &Path) -> Vec<u8> {
    std::fs::read(path).expect("read file")
}

/// Two `xark setup --insecure-dev-mode` runs without `--deterministic-rng`
/// must produce different verifying keys. If the default RNG were
/// deterministic, both VKs would hash identically and the Groth16
/// trapdoor would be effectively public.
#[test]
fn setup_default_rng_is_non_deterministic() {
    let tmp_a = tempdir();
    let tmp_b = tempdir();
    let artifact = fixture_dir().join("arithmetic_square.json");

    let (ok, _, err) = run(&[
        "setup",
        "--artifact",
        artifact.to_str().unwrap(),
        "--out",
        tmp_a.path().to_str().unwrap(),
        "--insecure-dev-mode",
    ]);
    assert!(ok, "setup A failed: {err}");

    let (ok, _, err) = run(&[
        "setup",
        "--artifact",
        artifact.to_str().unwrap(),
        "--out",
        tmp_b.path().to_str().unwrap(),
        "--insecure-dev-mode",
    ]);
    assert!(ok, "setup B failed: {err}");

    let vk_a = read_bytes(&tmp_a.path().join("verifying_key.bin"));
    let vk_b = read_bytes(&tmp_b.path().join("verifying_key.bin"));
    assert_ne!(
        vk_a, vk_b,
        "OS-randomness default setup produced identical VKs across two runs; \
 the production randomness path is wired up wrong (trapdoor leak risk)."
    );
}

/// `xark setup --insecure-dev-mode --deterministic-rng <seed>` must produce
/// byte-identical verifying keys across two runs with the same seed. This is
/// what makes test fixtures (and the A.5 frozen-format test) reproducible.
#[test]
fn setup_deterministic_seed_is_reproducible() {
    let tmp_a = tempdir();
    let tmp_b = tempdir();
    let artifact = fixture_dir().join("arithmetic_square.json");

    for out in [tmp_a.path(), tmp_b.path()] {
        let (ok, _, err) = run(&[
            "setup",
            "--artifact",
            artifact.to_str().unwrap(),
            "--out",
            out.to_str().unwrap(),
            "--insecure-dev-mode",
            "--deterministic-rng",
            "12345",
        ]);
        assert!(ok, "deterministic setup failed: {err}");
    }

    let vk_a = read_bytes(&tmp_a.path().join("verifying_key.bin"));
    let vk_b = read_bytes(&tmp_b.path().join("verifying_key.bin"));
    assert_eq!(
        vk_a, vk_b,
        "deterministic-rng setup produced different VKs across two runs; \
 test fixtures cannot be reproduced from this seed"
    );

    // Sanity-check that the metadata records the seed for traceability.
    let meta: serde_json::Value =
        serde_json::from_slice(&std::fs::read(tmp_a.path().join("metadata.json")).unwrap())
            .unwrap();
    assert_eq!(meta["deterministic_rng_seed"], serde_json::json!(12345u64));
}

/// Two `xark prove` invocations against a *shared* (deterministic) proving
/// key, *without* `--deterministic-rng`, must produce different proof bytes,
/// and both must verify true.
///
/// If proof randomness were deterministic on the default path, proofs would
/// be witness-leaking on top of being identical — that's the subtle Groth16
/// failure mode this test guards against.
#[test]
fn prove_default_rng_is_non_deterministic() {
    let tmp = tempdir();
    let artifact = fixture_dir().join("arithmetic_square.json");
    let witness = fixture_dir().join("arithmetic_square.gz");

    // Shared, deterministic setup so the test isn't conflating setup
    // randomness with prove randomness.
    let (ok, _, err) = run(&[
        "setup",
        "--artifact",
        artifact.to_str().unwrap(),
        "--out",
        tmp.path().to_str().unwrap(),
        "--insecure-dev-mode",
        "--deterministic-rng",
        "999",
    ]);
    assert!(ok, "setup failed: {err}");

    let pk = tmp.path().join("proving_key.bin");
    let vk_path = tmp.path().join("verifying_key.bin");

    let proof_a = tmp.path().join("proof_a.bin");
    let proof_b = tmp.path().join("proof_b.bin");

    for proof_path in [&proof_a, &proof_b] {
        let (ok, _, err) = run(&[
            "prove",
            "--artifact",
            artifact.to_str().unwrap(),
            "--witness",
            witness.to_str().unwrap(),
            "--proving-key",
            pk.to_str().unwrap(),
            "--out",
            proof_path.to_str().unwrap(),
        ]);
        assert!(ok, "prove failed: {err}");
    }

    let bytes_a = read_bytes(&proof_a);
    let bytes_b = read_bytes(&proof_b);
    assert_ne!(
        bytes_a, bytes_b,
        "OS-randomness default prove produced identical proofs across two \
 runs; proof randomness is not actually random."
    );

    // Both proofs must still verify against the shared VK + public inputs.
    let vk = Groth16Keys::read_verifying_key(&vk_path).expect("parse vk");
    let public_inputs =
        read_public_inputs(&tmp.path().join("public_inputs.bin")).expect("read public inputs");

    for proof_path in [&proof_a, &proof_b] {
        let proof = ProofBundle::read_proof(proof_path).expect("parse proof");
        let ok = xark_backend::verify(&vk, &proof, &public_inputs).expect("verify");
        assert!(
            ok,
            "non-deterministic proof at {} failed to verify",
            proof_path.display()
        );
    }
}
