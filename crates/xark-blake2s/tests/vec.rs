//! Correctness + soundness test for the BLAKE2s single-block gadget against real
//! BLAKE2s known-answer vectors (verified with Python `hashlib`):
//!
//!   blake2s("")    = 69217a30 79908094 e11121d0 42354a7c
//!                    1f55b648 2ca1a51e 1b250dfd 1ed0eef9
//!   blake2s("abc") = 508c5e8c 327c14e2 e1a72ba3 4eeb452f
//!                    37458b20 9ed63a29 4d999b4c 86675982
//!
//! The digest words fed to the circuit are the LE-`u32` values of the digest
//! bytes (word i = bytes 4i..4i+4, little-endian).

use std::collections::BTreeMap;
use xark_ir::{primitive, solver};

/// Compile `examples/blake2s` to R1CS via the shared test harness.
fn compile() -> primitive::PrimitiveProgram {
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/blake2s/src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "blake2s", "bn254");
    assert!(c.status_success, "compiling examples/blake2s failed: {}", c.stderr);
    c.program()
}

#[test]
fn blake2s_empty_matches_vector() {
    let program = compile();
    let id = |name: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == name)
            .unwrap_or_else(|| panic!("missing var {name}"))
            .id
    };

    // blake2s("") digest words (LE-u32 of the digest bytes).
    let digest: [&str; 8] = [
        "813310313",  // 0x307a2169
        "2491453561", // 0x94809079
        "3491828193", // 0xd02111e1
        "2085238082", // 0x7c4a3542
        "1219908895", // 0x48b6551f
        "514171180",  // 0x1ea5a12c
        "4245497115", // 0xfd0d251b
        "4193177630", // 0xf9eed01e
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
    let assign = solver::solve_and_check(&program, &inputs)
        .expect("BLAKE2s(\"\") must verify");

    // Soundness smoke-test: no derived variable is left under-constrained.
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "blake2s under-constrained: {holes:?}");

    // A wrong claimed digest word must be rejected.
    let mut bad = inputs.clone();
    bad.insert(id("d[0]"), "123".to_string());
    assert!(
        solver::solve_and_check(&program, &bad).is_err(),
        "a wrong digest must be rejected"
    );
}

#[test]
fn blake2s_abc_matches_vector() {
    // A non-trivial (non-zero) vector: blake2s("abc").
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
        "2355006544", // 0x8c5e8c50
        "3792993330", // 0xe2147c32
        "2737547233", // 0xa32ba7e1
        "793111374",  // 0x2f45eb4e
        "545998135",  // 0x208b4537
        "691721886",  // 0x293ad69e
        "1285265741", // 0x4c9b994d
        "2186897286", // 0x82596786
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

    let assign = solver::solve_and_check(&program, &inputs)
        .expect("BLAKE2s(\"abc\") must verify");
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "blake2s under-constrained: {holes:?}");

    // Corrupting the message must break the digest constraint.
    let mut bad = inputs.clone();
    bad.insert(id("m[0]"), "6513250".to_string());
    assert!(
        solver::solve_and_check(&program, &bad).is_err(),
        "a tampered message must be rejected"
    );
}
