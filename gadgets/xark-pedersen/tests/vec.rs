//! Solve-and-check the Grumpkin Pedersen example against an independent Python
//! reference (scratchpad `pedersen_ref.py`) computed with the SAME illustrative
//! generators. Confirms: (1) the emitted R1CS is satisfiable on the reference
//! vector, (2) it is analyzer-clean (soundness smoke test), and (3) a wrong
//! claimed output is rejected.
//!
//! The example is compiled on demand via the shared `xark-test-harness` crate.

use std::collections::BTreeMap;
use xark_ir::{primitive, solver};

fn load_program() -> primitive::PrimitiveProgram {
    let src =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/pedersen/src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "pedersen", "bn254");
    assert!(
        c.status_success,
        "compiling examples/pedersen failed: {}",
        c.stderr
    );
    c.program()
}

// Reference vector `H = M0·G0 + M1·G1` over the nothing-up-my-sleeve hash-to-curve
// generators (see `generators()`), computed with `ark-grumpkin`. The live
// derivation-and-check against `ark-grumpkin` lives in `examples/pedersen`'s test.
const M0: &str = "1512366075204170929049582354406559215";
const M1: &str = "338770000845734292534325025077361652240";
const HX: &str = "56611582869820574239993287487223071380142614942819473392064448158736499405";
const HY: &str = "14972036576598595980490710075994278492926559370076661242801210938371392582550";

#[test]
fn pedersen_matches_reference_vector() {
    let program = load_program();
    let id = |name: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == name)
            .unwrap_or_else(|| panic!("missing circuit var `{name}`"))
            .id
    };

    let mut inputs = BTreeMap::new();
    inputs.insert(id("m0"), M0.to_string());
    inputs.insert(id("m1"), M1.to_string());
    inputs.insert(id("hx"), HX.to_string());
    inputs.insert(id("hy"), HY.to_string());

    // (1) satisfiable on the honest vector.
    let assign = solver::solve_and_check(&program, &inputs)
        .expect("Pedersen circuit must verify on the reference vector");

    // (2) analyzer-clean: no under-constrained (forgeable) derived variables.
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "Pedersen under-constrained: {holes:?}");

    // (3) a wrong claimed output is rejected.
    inputs.insert(id("hx"), "123".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "wrong output x must be rejected"
    );
}
