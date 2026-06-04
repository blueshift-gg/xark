//! Integration tests for `BlackBoxFuncCall::Poseidon2Permutation` lowering.
//!
//! Exercises the `poseidon_basic` Noir fixture end-to-end through the
//! `xark` binary: setup, prove, verify happy path, plus tampered-public-input
//! rejection. Mirrors the helpers in `end_to_end.rs` so this file is
//! self-contained (we deliberately do not share helpers across integration
//! tests — see ROADMAP step WS-D.4).

use std::env;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn xark_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_xark"))
}

fn workspace_dir() -> PathBuf {
    // crates/xark-cli/tests/poseidon.rs -> crates/xark-cli/ -> crates/ -> root.
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
fn poseidon_basic_verifies() {
    let tmp = tempdir();
    let artifact = fixture_dir().join("poseidon_basic.json");
    let witness = fixture_dir().join("poseidon_basic.gz");
    let groth_dir = tmp.path().join("groth16");

    // inspect: Poseidon2Permutation + 4 equality AssertZeros must all be
    // classified as supported.
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
fn poseidon_tampered_output_fails() {
    let tmp = tempdir();
    let artifact = fixture_dir().join("poseidon_basic.json");
    let witness = fixture_dir().join("poseidon_basic.gz");
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

    // Flip the first public-output Field element. The Prover.toml declares
    // the permuted state in `pub [Field; 4]`, so all four public inputs are
    // poseidon outputs — perturbing any one of them must make verification
    // fail.
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
    // Bump the first public output by 1 mod field order. Since the original
    // value is a 254-bit decimal, +1 cannot overflow into the field modulus
    // even ignoring reduction.
    inputs[0] = bump_decimal(&inputs[0]);
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
    assert!(
        !ok,
        "verify unexpectedly succeeded on tampered poseidon output"
    );
    assert!(out.contains("Proof verified: false"), "out={out}");
}

/// Add 1 to a non-negative decimal string. Used to perturb a `Field` public
/// input without relying on big-int arithmetic libraries.
fn bump_decimal(s: &str) -> String {
    let mut digits: Vec<u8> = s.bytes().map(|b| b - b'0').collect();
    let mut carry = 1u8;
    for d in digits.iter_mut().rev() {
        let v = *d + carry;
        *d = v % 10;
        carry = v / 10;
        if carry == 0 {
            break;
        }
    }
    if carry == 1 {
        digits.insert(0, 1);
    }
    digits.into_iter().map(|d| (d + b'0') as char).collect()
}

// -----------------------------------------------------------------------------
// Tiny tempdir helper (mirrors the one in end_to_end.rs / bitwise.rs;
// kept local so test files stay independent).
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
    let path = env::temp_dir().join(format!("xark-poseidon-test-{pid}-{n}"));
    std::fs::create_dir_all(&path).expect("mkdir tempdir");
    TempDir { path }
}
