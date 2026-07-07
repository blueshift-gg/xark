//! Correctness + soundness test for the BLAKE3 single-block gadget against a
//! real BLAKE3 known-answer vector.
//!
//! Vector: BLAKE3("") = af1349b9 f5f9a1a6 a0404dea 36dcc949
//!                      9bcb25c9 adc112b7 cc9a93ca e41f3262
//! (the canonical empty-input BLAKE3 digest). Message bytes = 0 → all 16 input
//! words are 0 and `len = 0`. The digest words are the LE-`u32` values of the
//! digest bytes (word i = bytes 4i..4i+4, little-endian).

use std::collections::BTreeMap;
use xark_ir::{primitive, solver};

/// Compile `examples/blake3` to R1CS via the shared test harness.
fn compile() -> primitive::PrimitiveProgram {
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/blake3/src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "blake3", "bn254");
    assert!(c.status_success, "compiling examples/blake3 failed: {}", c.stderr);
    c.program()
}

#[test]
fn blake3_empty_matches_vector() {
    let program = compile();
    let id = |name: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == name)
            .unwrap_or_else(|| panic!("missing var {name}"))
            .id
    };

    // BLAKE3("") digest words (LE-u32 of the digest bytes).
    let digest: [&str; 8] = [
        "3108574127", // 0xb94913af
        "2795633141", // 0xa6a1f9f5
        "3930931360", // 0xea4d40a0
        "1237965878", // 0x49c9dc36
        "3374697371", // 0xc925cb9b
        "3071459757", // 0xb712c1ad
        "3398671052", // 0xca939acc
        "1647452132", // 0x62321fe4
    ];

    let mut inputs = BTreeMap::new();
    // Empty message: all 16 words and the length are zero.
    for i in 0..16 {
        inputs.insert(id(&format!("m[{i}]")), "0".to_string());
    }
    inputs.insert(id("len"), "0".to_string());
    for i in 0..8 {
        inputs.insert(id(&format!("d[{i}]")), digest[i].to_string());
    }

    // Honest witness solves and satisfies every constraint.
    let assign =
        solver::solve_and_check(&program, &inputs).expect("BLAKE3(\"\") must verify");

    // Soundness smoke-test: no derived variable is left under-constrained.
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "blake3 under-constrained: {holes:?}");

    // A wrong claimed digest word must be rejected.
    let mut bad = inputs.clone();
    bad.insert(id("d[0]"), "123".to_string());
    assert!(
        solver::solve_and_check(&program, &bad).is_err(),
        "a wrong digest must be rejected"
    );
}

#[test]
fn blake3_abc_matches_vector() {
    // A non-trivial (non-zero) vector: BLAKE3("abc") = 6437b3ac...
    // Message "abc" = 3 bytes -> word0 = LE-u32 of [0x61,0x62,0x63,0x00], len=3.
    let program = compile();
    let id = |name: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == name)
            .unwrap_or_else(|| panic!("missing var {name}"))
            .id
    };

    let msg_word0 = "6513249"; // 0x00636261
    let digest: [&str; 8] = [
        "2897426276",
        "860964408",
        "1966847743",
        "3045931559",
        "1180222792",
        "64715101",
        "1822176765",
        "2241707477",
    ];

    let mut inputs = BTreeMap::new();
    inputs.insert(id("m[0]"), msg_word0.to_string());
    for i in 1..16 {
        inputs.insert(id(&format!("m[{i}]")), "0".to_string());
    }
    inputs.insert(id("len"), "3".to_string());
    for i in 0..8 {
        inputs.insert(id(&format!("d[{i}]")), digest[i].to_string());
    }

    let assign =
        solver::solve_and_check(&program, &inputs).expect("BLAKE3(\"abc\") must verify");
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "blake3 under-constrained: {holes:?}");

    // Corrupting the message must break the digest constraint.
    let mut bad = inputs.clone();
    bad.insert(id("m[0]"), "6513250".to_string());
    assert!(
        solver::solve_and_check(&program, &bad).is_err(),
        "a tampered message must be rejected"
    );
}
