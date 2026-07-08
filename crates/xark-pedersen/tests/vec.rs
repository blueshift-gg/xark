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

// Python reference vector (pedersen_ref.py), same generators G0(x=1), G1(x=2),
// offset O(x=5), N_BITS = 128.
const M0: &str = "1512366075204170929049582354406559215";
const M1: &str = "338770000845734292534325025077361652240";
const HX: &str = "12247237786869595489850512927190383698331231276000700903834140832957657947403";
const HY: &str = "4919624278251879523047591843909313891382871438111885565699071497313999041142";

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
