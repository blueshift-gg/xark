//! Integration tests for `BlackBoxFuncCall::EmbeddedCurveAdd` and
//! `BlackBoxFuncCall::MultiScalarMul` lowering (ROADMAP step WS-D.5).
//!
//! Exercises the `curve_basic` Noir fixture end-to-end through the `xark`
//! binary: inspect coverage, setup, prove, verify happy path, plus
//! tampered-output rejection. Mirrors the helpers in `blake3.rs`
//! intentionally — we deliberately do not share helpers across integration
//! tests.

use std::env;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn xark_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_xark"))
}

fn workspace_dir() -> PathBuf {
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
fn curve_basic_verifies() {
    let tmp = tempdir();
    let artifact = fixture_dir().join("curve_basic.json");
    let witness = fixture_dir().join("curve_basic.gz");
    let groth_dir = tmp.path().join("groth16");

    // inspect: every opcode (MultiScalarMul + AssertZeros) should be supported.
    let (ok, out, err) = run(&["inspect", "--artifact", artifact.to_str().unwrap()]);
    assert!(ok, "inspect failed: stdout={out} stderr={err}");
    assert!(
        out.contains("Unsupported opcode count:     0"),
        "expected 0 unsupported opcodes, got: {out}"
    );

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
    assert!(out.contains("Proof verified: true"), "out={out}");
}

#[test]
fn curve_tampered_x_fails() {
    let tmp = tempdir();
    let artifact = fixture_dir().join("curve_basic.json");
    let witness = fixture_dir().join("curve_basic.gz");
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

    // Flip the low bit of the first public input (expected_x). Any flip in
    // the x-coordinate must make verification fail.
    let pi_path = groth_dir.join("public_inputs.json");
    let pi: serde_json::Value = serde_json::from_slice(&std::fs::read(&pi_path).unwrap()).unwrap();
    let mut inputs: Vec<String> = pi["inputs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_str().unwrap().to_string())
        .collect();
    assert!(
        !inputs.is_empty(),
        "fixture has no public inputs: {inputs:?}"
    );
    // Tamper: flip a decimal digit deterministically. Decrement the last
    // digit by 1 if non-zero, else change it to '9'. Any change breaks the
    // verification commitment.
    let mut digits: Vec<char> = inputs[0].chars().collect();
    let last = digits.len() - 1;
    digits[last] = match digits[last] {
        '0' => '9',
        c => char::from_digit(c.to_digit(10).unwrap() - 1, 10).unwrap(),
    };
    inputs[0] = digits.into_iter().collect();
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
    assert!(!ok, "verify unexpectedly succeeded on tampered x");
    assert!(out.contains("Proof verified: false"), "out={out}");
}

// -----------------------------------------------------------------------------
// Tiny tempdir helper (mirrors the other integration test files).
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
    let path = env::temp_dir().join(format!("xark-curve-test-{pid}-{n}"));
    std::fs::create_dir_all(&path).expect("mkdir tempdir");
    TempDir { path }
}
