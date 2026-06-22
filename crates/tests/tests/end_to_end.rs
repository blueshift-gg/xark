//! Integration tests driving the `xark` binary against committed fixtures.
//!
//! These tests bind the `crates/tests/fixtures/` directory directly so they
//! can verify the same artifact-vs-witness pair that comes out of nargo.

mod common;
use ark_bn254::Fr;
use ark_ff::PrimeField;
use common::{fixture_dir, run, tempdir};
use num_bigint::BigUint;
use xark_backend::serialization::{read_public_inputs, write_public_inputs};

#[test]
fn happy_path_arithmetic_square() {
    let tmp = tempdir();
    let artifact = fixture_dir().join("arithmetic_square.json");
    let witness = fixture_dir().join("arithmetic_square.gz");
    let groth_dir = tmp.path().join("groth16");

    // inspect
    let (ok, out, err) = run(&["inspect", "--artifact", artifact.to_str().unwrap()]);
    assert!(ok, "inspect failed: stdout={out} stderr={err}");
    assert!(out.contains("Supported opcode count: 1"));
    assert!(out.contains("Unsupported opcode count: 0"));

    // setup
    let (ok, _, err) = run(&[
        "setup",
        "--artifact",
        artifact.to_str().unwrap(),
        "--out",
        groth_dir.to_str().unwrap(),
        "--insecure-dev-mode",
    ]);
    assert!(ok, "setup failed: {err}");
    assert!(groth_dir.join("proving_key.bin").exists());
    assert!(groth_dir.join("verifying_key.bin").exists());
    assert!(groth_dir.join("metadata.json").exists());

    // prove
    let proof_path = groth_dir.join("proof.bin");
    let (ok, _, err) = run(&[
        "prove",
        "--artifact",
        artifact.to_str().unwrap(),
        "--witness",
        witness.to_str().unwrap(),
        "--proving-key",
        groth_dir.join("proving_key.bin").to_str().unwrap(),
        "--out",
        proof_path.to_str().unwrap(),
    ]);
    assert!(ok, "prove failed: {err}");
    assert!(proof_path.exists());
    assert!(groth_dir.join("snarkjs-proof.json").exists());
    assert!(groth_dir.join("snarkjs-public.json").exists());
    assert!(groth_dir.join("public_inputs.bin").exists());

    // verify (happy path)
    let (ok, out, err) = run(&[
        "verify",
        "--verifying-key",
        groth_dir.join("verifying_key.bin").to_str().unwrap(),
        "--proof",
        proof_path.to_str().unwrap(),
        "--public-inputs",
        groth_dir.join("public_inputs.bin").to_str().unwrap(),
    ]);
    assert!(ok, "verify failed: out={out} err={err}");
    assert!(out.contains("Proof verified: true"));
}

#[test]
fn tampered_public_input_fails_verification() {
    let tmp = tempdir();
    let artifact = fixture_dir().join("arithmetic_square.json");
    let witness = fixture_dir().join("arithmetic_square.gz");
    let groth_dir = tmp.path().join("groth16");

    assert!(
        run(&[
            "setup",
            "--artifact",
            artifact.to_str().unwrap(),
            "--out",
            groth_dir.to_str().unwrap(),
            "--insecure-dev-mode",
        ])
        .0
    );
    let proof_path = groth_dir.join("proof.bin");
    assert!(
        run(&[
            "prove",
            "--artifact",
            artifact.to_str().unwrap(),
            "--witness",
            witness.to_str().unwrap(),
            "--proving-key",
            groth_dir.join("proving_key.bin").to_str().unwrap(),
            "--out",
            proof_path.to_str().unwrap(),
        ])
        .0
    );

    // Mutate the public input.
    // arithmetic_square: x=9, y=81 => public input is 81.
    let pi_path = groth_dir.join("public_inputs.bin");
    let mut pi = read_public_inputs(&pi_path).unwrap();
    assert_eq!(pi[0], Fr::from(81u64), "fixture changed: update test");
    pi[0] += Fr::from(1u64);
    write_public_inputs(&pi, &pi_path).unwrap();

    let (ok, out, _) = run(&[
        "verify",
        "--verifying-key",
        groth_dir.join("verifying_key.bin").to_str().unwrap(),
        "--proof",
        proof_path.to_str().unwrap(),
        "--public-inputs",
        pi_path.to_str().unwrap(),
    ]);
    assert!(!ok, "verify unexpectedly succeeded on tampered input");
    assert!(out.contains("Proof verified: false"));
}

#[test]
fn setup_without_insecure_flag_fails() {
    let tmp = tempdir();
    let artifact = fixture_dir().join("arithmetic_square.json");
    let groth_dir = tmp.path().join("groth16");
    let (ok, _, err) = run(&[
        "setup",
        "--artifact",
        artifact.to_str().unwrap(),
        "--out",
        groth_dir.to_str().unwrap(),
    ]);
    assert!(!ok);
    assert!(
        err.contains("--insecure-dev-mode"),
        "expected insecure-dev-mode mention, got: {err}"
    );
}

#[test]
fn inspect_marks_blake2s_as_supported() {
    // Blake2s support landed here. The legacy
    // `unsupported_blake2s.json` fixture is the same Noir source as the
    // `blake2s_basic` example; xark now classifies its Blake2s opcode as
    // supported. The unsupported-opcode rejection path is still covered by
    // the `OpcodeClass::is_supported` unit tests in
    // `crates/acir-r1cs/src/opcodes/mod.rs` and by `xark inspect`'s coverage
    // counter on Noir programs that touch genuinely unsupported black-box
    // calls (none currently committed as fixtures).
    let artifact = fixture_dir().join("unsupported_blake2s.json");
    let (ok, out, err) = run(&["inspect", "--artifact", artifact.to_str().unwrap()]);
    assert!(ok, "inspect failed: out={out} err={err}");
    assert!(
        out.contains("Unsupported opcode count: 0"),
        "expected 0 unsupported opcodes for blake2s, got: {out}"
    );
    assert!(
        !out.contains("BlackBoxFuncCall::blake2s"),
        "blake2s should no longer appear in the unsupported list: {out}"
    );
}

#[test]
fn inspect_shows_range_as_supported() {
    let artifact = fixture_dir().join("range_basic.json");
    let (ok, out, err) = run(&["inspect", "--artifact", artifact.to_str().unwrap()]);
    assert!(ok, "inspect failed: out={out} err={err}");
    assert!(out.contains("Unsupported opcode count: 0"), "out={out}");
}

#[test]
fn range_basic_happy_path() {
    let tmp = tempdir();
    let artifact = fixture_dir().join("range_basic.json");
    let witness = fixture_dir().join("range_basic.gz");
    let groth_dir = tmp.path().join("groth16");

    let (ok, _, err) = run(&[
        "setup",
        "--artifact",
        artifact.to_str().unwrap(),
        "--out",
        groth_dir.to_str().unwrap(),
        "--insecure-dev-mode",
    ]);
    assert!(ok, "setup failed: {err}");
    let proof_path = groth_dir.join("proof.bin");
    let (ok, _, err) = run(&[
        "prove",
        "--artifact",
        artifact.to_str().unwrap(),
        "--witness",
        witness.to_str().unwrap(),
        "--proving-key",
        groth_dir.join("proving_key.bin").to_str().unwrap(),
        "--out",
        proof_path.to_str().unwrap(),
    ]);
    assert!(ok, "prove failed: {err}");
    let (ok, out, _) = run(&[
        "verify",
        "--verifying-key",
        groth_dir.join("verifying_key.bin").to_str().unwrap(),
        "--proof",
        proof_path.to_str().unwrap(),
        "--public-inputs",
        groth_dir.join("public_inputs.bin").to_str().unwrap(),
    ]);
    assert!(ok);
    assert!(out.contains("Proof verified: true"));
}

#[test]
fn sha256_compression_happy_path() {
    // This exercises the SHA-256 black-box gadget end-to-end against Noir's
    // `std::hash::sha256_compression` on the padded "abc" block + IV.
    let tmp = tempdir();
    let artifact = fixture_dir().join("sha256_basic.json");
    let witness = fixture_dir().join("sha256_basic.gz");
    let groth_dir = tmp.path().join("groth16");

    let (ok, _, err) = run(&[
        "setup",
        "--artifact",
        artifact.to_str().unwrap(),
        "--out",
        groth_dir.to_str().unwrap(),
        "--insecure-dev-mode",
    ]);
    assert!(ok, "setup failed: {err}");

    let proof_path = groth_dir.join("proof.bin");
    let (ok, _, err) = run(&[
        "prove",
        "--artifact",
        artifact.to_str().unwrap(),
        "--witness",
        witness.to_str().unwrap(),
        "--proving-key",
        groth_dir.join("proving_key.bin").to_str().unwrap(),
        "--out",
        proof_path.to_str().unwrap(),
    ]);
    assert!(ok, "prove failed: {err}");

    let (ok, out, _) = run(&[
        "verify",
        "--verifying-key",
        groth_dir.join("verifying_key.bin").to_str().unwrap(),
        "--proof",
        proof_path.to_str().unwrap(),
        "--public-inputs",
        groth_dir.join("public_inputs.bin").to_str().unwrap(),
    ]);
    assert!(ok, "verify failed: {out}");
    assert!(out.contains("Proof verified: true"));
}

#[test]
fn sha256_tampered_public_digest_fails() {
    let tmp = tempdir();
    let artifact = fixture_dir().join("sha256_basic.json");
    let witness = fixture_dir().join("sha256_basic.gz");
    let groth_dir = tmp.path().join("groth16");

    assert!(
        run(&[
            "setup",
            "--artifact",
            artifact.to_str().unwrap(),
            "--out",
            groth_dir.to_str().unwrap(),
            "--insecure-dev-mode",
        ])
        .0
    );
    let proof_path = groth_dir.join("proof.bin");
    assert!(
        run(&[
            "prove",
            "--artifact",
            artifact.to_str().unwrap(),
            "--witness",
            witness.to_str().unwrap(),
            "--proving-key",
            groth_dir.join("proving_key.bin").to_str().unwrap(),
            "--out",
            proof_path.to_str().unwrap(),
        ])
        .0
    );

    // Flip a bit in the first public input.
    let pi_path = groth_dir.join("public_inputs.bin");
    let mut pi = read_public_inputs(&pi_path).unwrap();
    let orig: BigUint = pi[0].into();
    pi[0] = Fr::from_le_bytes_mod_order(&(orig ^ BigUint::from(1u64)).to_bytes_le());
    write_public_inputs(&pi, &pi_path).unwrap();

    let (ok, out, _) = run(&[
        "verify",
        "--verifying-key",
        groth_dir.join("verifying_key.bin").to_str().unwrap(),
        "--proof",
        proof_path.to_str().unwrap(),
        "--public-inputs",
        pi_path.to_str().unwrap(),
    ]);
    assert!(!ok);
    assert!(out.contains("Proof verified: false"));
}

#[test]
fn inspect_json_output_is_valid_json() {
    let artifact = fixture_dir().join("arithmetic_square.json");
    let (ok, out, _) = run(&[
        "inspect",
        "--artifact",
        artifact.to_str().unwrap(),
        "--json",
    ]);
    assert!(ok);
    let v: serde_json::Value = serde_json::from_str(&out).expect("valid JSON");
    assert_eq!(v["circuit_name"], "arithmetic_square");
    assert_eq!(v["supported_opcode_count"], 1);
    assert_eq!(v["unsupported_opcode_count"], 0);
}
