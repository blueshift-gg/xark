//! Integration tests covering non-trivial public-input layouts:
//! return-values-only, mixed public-param + return, reordered public params,
//! and a large (16-element) public-input vector.
//!
//! Mirrors the helper structure in `end_to_end.rs` but lives in its own
//! file so the two test suites can be edited independently.

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

fn end_to_end(fixture_name: &str) -> (bool, String) {
    let tmp = tempdir();
    let artifact = fixture_dir().join(format!("{fixture_name}.json"));
    let witness = fixture_dir().join(format!("{fixture_name}.gz"));
    let groth_dir = tmp.path().join("groth16");

    let (ok, _, err) = run(&[
        "setup",
        "--artifact",
        artifact.to_str().unwrap(),
        "--out",
        groth_dir.to_str().unwrap(),
        "--insecure-dev-mode",
    ]);
    assert!(ok, "setup failed for {fixture_name}: {err}");

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
    assert!(ok, "prove failed for {fixture_name}: {err}");

    let (ok, out, err) = run(&[
        "verify",
        "--verifying-key",
        groth_dir.join("verifying_key.bin").to_str().unwrap(),
        "--proof",
        proof_path.to_str().unwrap(),
        "--public-inputs",
        groth_dir.join("public_inputs.json").to_str().unwrap(),
    ]);
    assert!(ok, "verify failed for {fixture_name}: out={out} err={err}");
    (out.contains("Proof verified: true"), out)
}

#[test]
fn return_values_only_verifies() {
    // `fn main(x: Field) -> pub Field { x * x }` — no `pub` param, just a
    // return value. Exercises the path where public inputs come entirely
    // from `return_values`, not `public_parameters`.
    let (verified, out) = end_to_end("return_values_only");
    assert!(verified, "expected verified=true, got: {out}");
}

#[test]
fn mixed_pi_verifies() {
    // `fn main(x: Field, y: pub Field) -> pub Field { x * y + x }` — one
    // public parameter and one return value, mixed together.
    let (verified, out) = end_to_end("mixed_pi");
    assert!(verified, "expected verified=true, got: {out}");
}

#[test]
fn reorder_pi_verifies() {
    // `fn main(a: pub Field, b: Field, c: pub Field) { assert(b * b == a + c); }`
    // — non-contiguous public-input witness indices (private `b` between two
    // public params).
    let (verified, out) = end_to_end("reorder_pi");
    assert!(verified, "expected verified=true, got: {out}");
}

#[test]
fn large_pi_verifies() {
    // 16 public inputs at once, asserting xs[0] + xs[15] = 30.
    let (verified, out) = end_to_end("large_pi");
    assert!(verified, "expected verified=true, got: {out}");
}

#[test]
fn reorder_pi_tampered_first_input_fails() {
    // Flip the first public input on a non-contiguous layout and confirm
    // verification fails. Exercises the public-input *order* contract: if
    // we accidentally re-sorted public inputs, this would still pass with
    // a different `inputs[0]` value. Tampering must fail.
    let tmp = tempdir();
    let artifact = fixture_dir().join("reorder_pi.json");
    let witness = fixture_dir().join("reorder_pi.gz");
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

    // Bump the first public input by one.
    let pi_path = groth_dir.join("public_inputs.json");
    let pi: serde_json::Value = serde_json::from_slice(&std::fs::read(&pi_path).unwrap()).unwrap();
    let mut inputs: Vec<String> = pi["inputs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_str().unwrap().to_string())
        .collect();
    let orig: u64 = inputs[0].parse().unwrap();
    inputs[0] = (orig + 1).to_string();
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
    assert!(!ok, "expected verify to fail, got success");
    assert!(out.contains("Proof verified: false"), "got: {out}");
}

// -----------------------------------------------------------------------------
// Tiny tempdir helper, mirroring the one in end_to_end.rs.
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
    let path = env::temp_dir().join(format!("xark-pi-test-{pid}-{n}"));
    std::fs::create_dir_all(&path).expect("mkdir tempdir");
    TempDir { path }
}
