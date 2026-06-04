//! Integration tests driving the `xark` binary against committed fixtures.
//!
//! These tests bind the workspace `tests/fixtures/` directory directly so they
//! can verify the same artifact-vs-witness pair that comes out of nargo.

use std::env;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn xark_bin() -> PathBuf {
    // Cargo sets `CARGO_BIN_EXE_<name>` for integration tests of binary crates.
    PathBuf::from(env!("CARGO_BIN_EXE_xark"))
}

fn workspace_dir() -> PathBuf {
    // crates/xark-cli/tests/end_to_end.rs -> crates/xark-cli/ -> crates/ -> workspace root.
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

fn fixture_dir() -> PathBuf {
    workspace_dir().join("tests").join("fixtures")
}

fn run(args: &[&str]) -> (bool, String, String) {
    let output = Command::new(xark_bin())
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("invoke xark");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    (output.status.success(), stdout, stderr)
}

#[test]
fn happy_path_arithmetic_square() {
    let tmp = tempdir();
    let artifact = fixture_dir().join("arithmetic_square.json");
    let witness = fixture_dir().join("arithmetic_square.gz");
    let groth_dir = tmp.path().join("groth16");

    // inspect
    let (ok, out, err) = run(&["inspect", "--artifact", artifact.to_str().unwrap()]);
    assert!(ok, "inspect failed: stdout={out} stderr={err}");
    assert!(out.contains("Supported opcode count:       1"));
    assert!(out.contains("Unsupported opcode count:     0"));

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
    assert!(groth_dir.join("proof.json").exists());
    assert!(groth_dir.join("public_inputs.json").exists());

    // verify (happy path)
    let (ok, out, err) = run(&[
        "verify",
        "--verifying-key",
        groth_dir.join("verifying_key.bin").to_str().unwrap(),
        "--proof",
        proof_path.to_str().unwrap(),
        "--public-inputs",
        groth_dir.join("public_inputs.json").to_str().unwrap(),
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
    let pi_path = groth_dir.join("public_inputs.json");
    let pi = std::fs::read_to_string(&pi_path).unwrap();
    let bad = pi.replace("\"81\"", "\"82\"");
    assert_ne!(pi, bad, "fixture changed: update test");
    std::fs::write(&pi_path, bad).unwrap();

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
    // ROADMAP step WS-D.2 lit up Blake2s support. The legacy
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
        out.contains("Unsupported opcode count:     0"),
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
    assert!(out.contains("Unsupported opcode count:     0"), "out={out}");
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
        groth_dir.join("public_inputs.json").to_str().unwrap(),
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
        groth_dir.join("public_inputs.json").to_str().unwrap(),
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

    // Flip a bit in the first public-input word of the digest.
    let pi_path = groth_dir.join("public_inputs.json");
    let pi: serde_json::Value = serde_json::from_slice(&std::fs::read(&pi_path).unwrap()).unwrap();
    let mut inputs: Vec<String> = pi["inputs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_str().unwrap().to_string())
        .collect();
    let orig: u64 = inputs[0].parse().unwrap();
    inputs[0] = (orig ^ 1).to_string();
    let mut tampered = pi.clone();
    tampered["inputs"] =
        serde_json::Value::Array(inputs.into_iter().map(serde_json::Value::String).collect());
    std::fs::write(&pi_path, serde_json::to_vec_pretty(&tampered).unwrap()).unwrap();

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

// -----------------------------------------------------------------------------
// Tiny tempdir helper to avoid pulling in another crate.
// -----------------------------------------------------------------------------

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

fn tempdir() -> TempDir {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let n = COUNTER.fetch_add(1, Ordering::SeqCst);
    let pid = std::process::id();
    let path = env::temp_dir().join(format!("xark-test-{pid}-{n}"));
    std::fs::create_dir_all(&path).expect("mkdir tempdir");
    TempDir { path }
}
