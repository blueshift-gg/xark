//! Known-answer test for the real MiMC-BN254 hash (a port of
//! [`noir-lang/mimc`](https://github.com/noir-lang/mimc): MiMC-p/p, S-box
//! exponent 7, 91 rounds, `C[0] = 0`, circomlib round constants).
//!
//! Noir's own KAT:
//!
//!   mimc_bn254([12, 45, 78, 41])
//!     = 18226366069841799622585958305961373004333097209608110160936134895615261821931
//!
//! An all-constant-input circuit constrains the public output to
//! `mimc_bn254([12, 45, 78, 41])`. Solving the circuit with the Noir KAT value
//! must succeed (our MiMC == Noir's, bit-for-bit); solving with any other value
//! must be rejected. This is the proof that our gadget matches the reference.

use std::collections::BTreeMap;
use xark_ir::{primitive, solver};

/// The `noir-lang/mimc` known-answer for `mimc_bn254([12, 45, 78, 41])`.
const KAT: &str = "18226366069841799622585958305961373004333097209608110160936134895615261821931";

/// Compile an inline all-constant-input MiMC-BN254 circuit to R1CS via the shared
/// test harness (bn254). Kept inline (not an `examples/` crate) so the KAT lives
/// next to the gadget it validates.
fn compile() -> primitive::PrimitiveProgram {
    let src = "#![no_std]\n\
        use xark_mimc::prelude::*;\n\
        pub fn circuit(out: Public<Field>) {\n\
        require_eq(\n\
        mimc_bn254([Field::from(12u8), Field::from(45u8), Field::from(78u8), Field::from(41u8)]),\n\
        out,\n\
        );\n\
        }\n";
    let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("mimc_kat.rs");
    std::fs::write(&path, src).expect("write inline mimc_kat source");
    let c = xark_test_harness::compile_file(&path, "mimc_kat", "bn254");
    assert!(
        c.status_success,
        "compiling inline mimc_kat failed: {}",
        c.stderr
    );
    c.program()
}

#[test]
fn mimc_bn254_matches_noir_kat() {
    let program = compile();
    let out = program
        .vars
        .iter()
        .find(|v| v.name == "out")
        .expect("missing var `out`")
        .id;

    // Honest witness: the public output equals the Noir KAT value → solves and
    // satisfies every constraint. This proves our MiMC == Noir's, bit-for-bit.
    let mut inputs = BTreeMap::new();
    inputs.insert(out, KAT.to_string());
    let assign = solver::solve_and_check(&program, &inputs).expect("MiMC-BN254 KAT must verify");

    // No derived variable is left under-constrained.
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "mimc under-constrained: {holes:?}");

    // A wrong claimed output must be rejected (KAT - 1).
    let mut bad = inputs.clone();
    bad.insert(
        out,
        "18226366069841799622585958305961373004333097209608110160936134895615261821930".to_string(),
    );
    assert!(
        solver::solve_and_check(&program, &bad).is_err(),
        "a wrong MiMC output must be rejected"
    );
}
