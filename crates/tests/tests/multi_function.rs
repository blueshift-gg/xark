//! CLI `inspect` tests for multi-function ACIR programs.
//!
//! The `multi_function` / `nested_calls` fixtures keep their helper functions
//! as separate ACIR functions (Noir's `#[fold]` attribute forces this), so
//! `main` invokes them via `Opcode::Call`. These tests cover how `xark inspect`
//! reports helper functions — count and names, in both human and JSON output.
//! The prove/verify pipeline for these circuits lives in `circuits.rs`.

mod common;
use common::{fixture_dir, run};

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

    // `Opcode::Call` is lowered (inlined with witness-index shifting), so the
    // fixture reports 0 unsupported opcodes.
    let unsupported = v["unsupported_opcode_count"]
        .as_u64()
        .expect("unsupported_opcode_count");
    assert_eq!(unsupported, 0, "Call should be supported");
}

#[test]
fn multi_function_inspect_human_output_lists_helpers() {
    let artifact = fixture_dir().join("multi_function.json");
    let (ok, out, err) = run(&["inspect", "--artifact", artifact.to_str().unwrap()]);
    assert!(ok, "inspect failed: out={out} err={err}");
    assert!(
        out.contains("Helper function count: 1"),
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
    // A single-function artifact should report `helper_function_count: 0` and
    // an empty `helper_function_names` array.
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
