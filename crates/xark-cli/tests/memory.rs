//! Integration tests for ACIR `MemoryInit` + `MemoryOp` lowering at constant
//! indices (ROADMAP step **WS-C.4**, design note in `docs/memory.md`).
//!
//! The fixture is `memory_const.json` / `memory_const.gz`, generated from
//! `examples/memory_const/` (an array whose elements depend on a private
//! input so Noir doesn't constant-fold the array away, with a hardcoded
//! constant index read). The lowering layer emits a single equality
//! constraint per read to the matching init slot.
//!
//! Tests:
//! * `memory_const_verifies` — happy path: setup → prove → verify true.
//! * `memory_const_tampered_y_fails` — tampering with the public output
//!   `y` makes verification fail.
//!
//! See `docs/memory.md` for the soundness argument and the
//! `extract_pinned_constants` detector for the precise shape of
//! `AssertZero` Noir emits for constant indices.

use std::env;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn xark_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_xark"))
}

fn workspace_dir() -> PathBuf {
    // crates/xark-cli/tests/memory.rs -> crates/xark-cli/ -> crates/ -> root.
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
fn memory_const_verifies() {
    let tmp = tempdir();
    let artifact = fixture_dir().join("memory_const.json");
    let witness = fixture_dir().join("memory_const.gz");
    let groth_dir = tmp.path().join("groth16");

    // inspect: MemoryInit + MemoryOp + the surrounding AssertZero/Brillig
    // opcodes must all be classified as supported after WS-C.4.
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
fn memory_const_tampered_y_fails() {
    let tmp = tempdir();
    let artifact = fixture_dir().join("memory_const.json");
    let witness = fixture_dir().join("memory_const.gz");
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

    // Flip the lowest bit of the public `y` input — this is the slot the
    // constant-index read pins to `arr[1]`, so the resulting equality
    // constraint `value_witness == arr[1]_witness` must fail.
    let pi_path = groth_dir.join("public_inputs.json");
    let pi: serde_json::Value = serde_json::from_slice(&std::fs::read(&pi_path).unwrap()).unwrap();
    let mut inputs: Vec<String> = pi["inputs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_str().unwrap().to_string())
        .collect();
    assert!(!inputs.is_empty(), "fixture has no public inputs");
    let last = inputs.len() - 1;
    let orig: u64 = inputs[last].parse().unwrap();
    inputs[last] = (orig ^ 1).to_string();
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
    assert!(!ok, "verify unexpectedly succeeded on tampered y");
    assert!(out.contains("Proof verified: false"), "out={out}");
}

// -----------------------------------------------------------------------------
// Tiny tempdir helper (mirrors the one in bitwise.rs / brillig.rs / blake3.rs).
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
    let path = env::temp_dir().join(format!("xark-memory-test-{pid}-{n}"));
    std::fs::create_dir_all(&path).expect("mkdir tempdir");
    TempDir { path }
}
