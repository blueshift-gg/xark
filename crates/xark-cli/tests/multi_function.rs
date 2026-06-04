//! Integration tests for ROADMAP step WS-B.4: multi-function ACIR programs.
//!
//! The fixture (`tests/fixtures/multi_function.{json,gz}`) is built from
//! `examples/multi_function/` with `nargo execute`. Its source uses the
//! `#[fold]` attribute to force Noir to keep the `square` helper as a
//! separate ACIR function — i.e. `program.functions.len() == 2` with
//! `main` invoking the helper via `Opcode::Call`.
//!
//! What B.4 guarantees:
//!   * The parser accepts the multi-function artifact (it used to reject).
//!   * `xark inspect` reports `helper_function_count = 1` and the helper's
//!     name in both human-readable and JSON modes.
//!   * `Opcode::Call` is still rejected by the lowering layer (deferred to
//!     B.5) — surfaced as `unsupported_opcode_count: 1`, kind `"Call"`.
//!
//! The existing `arithmetic_square` end-to-end pipeline implicitly covers
//! the "main function proves and verifies" half of B.4's acceptance: any
//! single-function artifact is still accepted and reports
//! `helper_function_count: 0`, asserted below.

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
fn multi_function_inspect_reports_helpers() {
    let artifact = fixture_dir().join("multi_function.json");
    let (ok, out, err) = run(&[
        "inspect",
        "--artifact",
        artifact.to_str().unwrap(),
        "--json",
    ]);
    assert!(ok, "inspect failed: out={out} err={err}");
    let v: serde_json::Value = serde_json::from_str(&out).expect("valid JSON");
    assert_eq!(v["circuit_name"], "multi_function");
    let helper_count = v["helper_function_count"]
        .as_u64()
        .expect("helper_function_count present");
    assert!(
        helper_count >= 1,
        "expected at least 1 helper function, got: {helper_count} (full report: {out})"
    );
    let names = v["helper_function_names"]
        .as_array()
        .expect("helper_function_names is an array");
    assert_eq!(names.len() as u64, helper_count);
    assert!(
        names.iter().any(|n| n.as_str() == Some("square")),
        "expected 'square' in helper_function_names, got: {names:?}"
    );

    // Post-B.5: `Opcode::Call` is now lowered (predicate-1 inlining with
    // witness-index shifting). The fixture should report 0 unsupported
    // opcodes.
    let unsupported = v["unsupported_opcode_count"]
        .as_u64()
        .expect("unsupported_opcode_count");
    assert_eq!(unsupported, 0, "Call should now be supported (B.5)");
}

#[test]
fn multi_function_inspect_human_output_lists_helpers() {
    let artifact = fixture_dir().join("multi_function.json");
    let (ok, out, err) = run(&["inspect", "--artifact", artifact.to_str().unwrap()]);
    assert!(ok, "inspect failed: out={out} err={err}");
    assert!(
        out.contains("Helper function count:        1"),
        "expected helper function count line, got: {out}"
    );
    assert!(
        out.contains("Helper functions:"),
        "expected helper functions header, got: {out}"
    );
    assert!(
        out.contains("- square"),
        "expected square in helper list, got: {out}"
    );
}

#[test]
fn single_function_inspect_reports_zero_helpers() {
    // Regression: pre-B.4, single-function artifacts had no helper field at
    // all. Post-B.4, they should report `helper_function_count: 0` and an
    // empty `helper_function_names` array.
    let artifact = fixture_dir().join("arithmetic_square.json");
    let (ok, out, err) = run(&[
        "inspect",
        "--artifact",
        artifact.to_str().unwrap(),
        "--json",
    ]);
    assert!(ok, "inspect failed: out={out} err={err}");
    let v: serde_json::Value = serde_json::from_str(&out).expect("valid JSON");
    assert_eq!(v["helper_function_count"], 0);
    assert_eq!(
        v["helper_function_names"]
            .as_array()
            .expect("helper_function_names is an array")
            .len(),
        0
    );
}

#[test]
fn multi_function_main_proves_and_verifies_after_call_lowered() {
    // B.4 scope note: Noir's compiler in v1.0.0-beta.21 only emits separate
    // ACIR functions when the call survives inlining (`#[fold]` forces this).
    // That means every multi-function Noir artifact we can produce uses
    // `Opcode::Call` in `main`, which is the "Scenario B" rejected by the
    // lowering layer per B.4 scope. The full prove/verify pipeline on a
    // multi-function artifact must wait for B.5 ("Call opcode (cross-circuit)").
    //
    // Post-B.5: Call opcodes are inlined with witness-index shifting. The
    // multi-function fixture should now prove and verify end-to-end.
    let tmp = env::temp_dir().join(format!(
        "xark-multifn-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&tmp).unwrap();

    let artifact = fixture_dir().join("multi_function.json");
    let witness = fixture_dir().join("multi_function.gz");

    let (ok, _stdout, stderr) = run(&[
        "setup",
        "--artifact",
        artifact.to_str().unwrap(),
        "--out",
        tmp.to_str().unwrap(),
        "--insecure-dev-mode",
    ]);
    assert!(ok, "setup failed: {stderr}");

    let proof_path = tmp.join("proof.bin");
    let (ok, _, err) = run(&[
        "prove",
        "--artifact",
        artifact.to_str().unwrap(),
        "--witness",
        witness.to_str().unwrap(),
        "--proving-key",
        tmp.join("proving_key.bin").to_str().unwrap(),
        "--out",
        proof_path.to_str().unwrap(),
    ]);
    assert!(ok, "prove failed: {err}");

    let (ok, out, _) = run(&[
        "verify",
        "--verifying-key",
        tmp.join("verifying_key.bin").to_str().unwrap(),
        "--proof",
        proof_path.to_str().unwrap(),
        "--public-inputs",
        tmp.join("public_inputs.json").to_str().unwrap(),
    ]);
    assert!(ok, "verify failed: {out}");
    assert!(out.contains("Proof verified: true"));

    let _ = std::fs::remove_dir_all(&tmp);
}

#[test]
fn nested_calls_main_proves_and_verifies() {
    // B.5 follow-up: nested cross-circuit calls. Fixture comes from
    // `examples/nested_calls/`, where `main` invokes `square_plus_one`,
    // which itself invokes `square` (both folded). Exercises the
    // recursive branch of `lower_call_at` and the running call-offset
    // allocator in `R1csBuilder`.
    let tmp = env::temp_dir().join(format!(
        "xark-nested-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&tmp).unwrap();

    let artifact = fixture_dir().join("nested_calls.json");
    let witness = fixture_dir().join("nested_calls.gz");

    let (ok, _stdout, stderr) = run(&[
        "setup",
        "--artifact",
        artifact.to_str().unwrap(),
        "--out",
        tmp.to_str().unwrap(),
        "--insecure-dev-mode",
    ]);
    assert!(ok, "setup failed: {stderr}");

    let proof_path = tmp.join("proof.bin");
    let (ok, _, err) = run(&[
        "prove",
        "--artifact",
        artifact.to_str().unwrap(),
        "--witness",
        witness.to_str().unwrap(),
        "--proving-key",
        tmp.join("proving_key.bin").to_str().unwrap(),
        "--out",
        proof_path.to_str().unwrap(),
    ]);
    assert!(ok, "prove failed: {err}");

    let (ok, out, _) = run(&[
        "verify",
        "--verifying-key",
        tmp.join("verifying_key.bin").to_str().unwrap(),
        "--proof",
        proof_path.to_str().unwrap(),
        "--public-inputs",
        tmp.join("public_inputs.json").to_str().unwrap(),
    ]);
    assert!(ok, "verify failed: {out}");
    assert!(out.contains("Proof verified: true"));

    let _ = std::fs::remove_dir_all(&tmp);
}

#[test]
fn nested_calls_inspect_reports_two_helpers() {
    let artifact = fixture_dir().join("nested_calls.json");
    let (ok, out, err) = run(&[
        "inspect",
        "--artifact",
        artifact.to_str().unwrap(),
        "--json",
    ]);
    assert!(ok, "inspect failed: out={out} err={err}");
    let v: serde_json::Value = serde_json::from_str(&out).expect("inspect emits valid JSON");
    assert_eq!(v["circuit_name"], "nested_calls");
    assert_eq!(
        v["helper_function_count"]
            .as_u64()
            .expect("helper_function_count is integer"),
        2,
        "expected exactly two helper functions (square_plus_one + square)"
    );
    let names = v["helper_function_names"]
        .as_array()
        .expect("helper_function_names is an array");
    let names_str: Vec<&str> = names.iter().filter_map(|n| n.as_str()).collect();
    assert!(
        names_str.contains(&"square"),
        "expected 'square' in helper_function_names, got: {names_str:?}"
    );
    assert!(
        names_str.contains(&"square_plus_one"),
        "expected 'square_plus_one' in helper_function_names, got: {names_str:?}"
    );
}
