//! Solve-and-check the Grumpkin `MultiScalarMul` example against an independent
//! Python reference (scratchpad `gref.py`) computed with textbook Grumpkin EC
//! arithmetic (`y² = x³ - 17`, proper `∞` handling). Confirms: (1) the emitted
//! R1CS is satisfiable on the reference vector, (2) it is analyzer-clean
//! (soundness smoke test), and (3) a wrong claimed output is rejected.
//!
//! The example is compiled on demand via the shared `xark-test-harness` crate.

use std::collections::BTreeMap;
use xark_ir::{primitive, solver};

fn load_program() -> primitive::PrimitiveProgram {
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/grumpkin/src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "grumpkin", "bn254");
    assert!(c.status_success, "compiling examples/grumpkin failed: {}", c.stderr);
    c.program()
}

// Python reference vector (gref.py): R = s0·Q0 + s1·Q1 over Grumpkin, N_BITS=128.
const S0: &str = "1512366075204170929049582354406559215";
const S1: &str = "338770000845734292534325025077361652240";
// Q0 = (8, ...)
const P0X: &str = "8";
const P0Y: &str = "17211924001480414201552586258339381047922154443519291062668150353239757288029";
// Q1 = (10, ...)
const P1X: &str = "10";
const P1Y: &str = "3764497608137669826449761938357951019955713832105137848030504861970310222496";
// R = s0·Q0 + s1·Q1
const RX: &str = "18795281547672131371183968279919782939389077073414573264326681878560793134719";
const RY: &str = "2414680004978840508961516437196481407162521166594374623807266823818455121132";

#[test]
fn msm_matches_reference_vector() {
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
    inputs.insert(id("scalars[0]"), S0.to_string());
    inputs.insert(id("scalars[1]"), S1.to_string());
    inputs.insert(id("points[0][0]"), P0X.to_string());
    inputs.insert(id("points[0][1]"), P0Y.to_string());
    inputs.insert(id("points[1][0]"), P1X.to_string());
    inputs.insert(id("points[1][1]"), P1Y.to_string());
    inputs.insert(id("r[0]"), RX.to_string());
    inputs.insert(id("r[1]"), RY.to_string());

    // (1) satisfiable on the honest vector.
    let assign = solver::solve_and_check(&program, &inputs)
        .expect("Grumpkin MSM circuit must verify on the reference vector");

    // (2) analyzer-clean: no under-constrained (forgeable) derived variables.
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "MSM under-constrained: {holes:?}");

    // (3) a wrong claimed output is rejected.
    inputs.insert(id("r[0]"), "123".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "wrong output x must be rejected"
    );
}
