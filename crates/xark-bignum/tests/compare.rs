//! Solve-and-check the sound non-native comparison-bit primitive `is_lt` against
//! `examples/is_lt_check` (`assert_eq(is_lt(a, b), claim)` over 2×64-bit limbs).
//! Confirms: (1) the derived comparison bit matches `a < b` on a spread of vectors
//! (incl. high-limb-dominant), (2) the circuit is analyzer-clean (the bit and every
//! borrow are fully pinned — the soundness smoke test), and (3) a wrong claimed bit
//! is rejected.

use std::collections::BTreeMap;
use xark_ir::{primitive, solver};

fn load() -> primitive::PrimitiveProgram {
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/is_lt_check/src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "is_lt_check", "bn254");
    assert!(
        c.status_success,
        "compiling examples/is_lt_check failed: {}",
        c.stderr
    );
    c.program()
}

/// `value = limb[0] + limb[1]·2^64`, little-endian 2×64.
fn inputs(
    p: &primitive::PrimitiveProgram,
    a: [&str; 2],
    b: [&str; 2],
    claim: &str,
) -> BTreeMap<u32, String> {
    let id = |n: &str| {
        p.vars
            .iter()
            .find(|v| v.name == n)
            .unwrap_or_else(|| panic!("missing circuit var `{n}`"))
            .id
    };
    let mut m = BTreeMap::new();
    m.insert(id("a[0]"), a[0].to_string());
    m.insert(id("a[1]"), a[1].to_string());
    m.insert(id("b[0]"), b[0].to_string());
    m.insert(id("b[1]"), b[1].to_string());
    m.insert(id("claim"), claim.to_string());
    m
}

#[test]
fn is_lt_matches_reference_and_is_sound() {
    let p = load();

    // (1) accepting vectors: `claim` equals the true `a < b` bit.
    let cases = [
        (["5", "0"], ["7", "0"], "1"),   // 5 < 7
        (["7", "0"], ["5", "0"], "0"),   // 7 > 5
        (["5", "0"], ["5", "0"], "0"),   // equal → not <
        (["100", "0"], ["0", "1"], "1"), // 100 < 2^64 (high limb decides)
        (["0", "1"], ["100", "0"], "0"), // 2^64 > 100
        (["0", "1"], ["1", "1"], "1"),   // 2^64 < 2^64+1 (low limb tiebreak)
    ];
    for (a, b, claim) in cases {
        let assign = solver::solve_and_check(&p, &inputs(&p, a, b, claim))
            .unwrap_or_else(|e| panic!("is_lt({a:?},{b:?})=={claim} must accept: {e:?}"));
        // (2) analyzer-clean: the comparison bit and borrows are all pinned.
        let holes = solver::analyze_underconstrained(&p, &assign);
        assert!(holes.is_empty(), "is_lt under-constrained: {holes:?}");
    }

    // (3) a wrong claimed bit is rejected.
    assert!(
        solver::solve_and_check(&p, &inputs(&p, ["5", "0"], ["7", "0"], "0")).is_err(),
        "claiming 5 ≥ 7 must be rejected"
    );
    assert!(
        solver::solve_and_check(&p, &inputs(&p, ["0", "1"], ["100", "0"], "1")).is_err(),
        "claiming 2^64 < 100 must be rejected"
    );
}
