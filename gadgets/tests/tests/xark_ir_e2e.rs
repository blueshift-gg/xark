//! End-to-end: a real xark circuit → xark-IR → R1CS → xark's Groth16
//! backend → a *verified* proof, end to end within xark's own pipeline.
//!
//! The circuit (`cube`: prove knowledge of `a` with `a^3 = c`) was written in
//! the Rust subset, compiled through rustc-MIR → xark-IR → R1CS by the xark
//! compiler, and committed as a fixture. Here we:
//!   1. load the IR (`R1csProgram` + witness-gen `PrimitiveProgram`),
//!   2. **solve the witness with xark's own solver**,
//!   3. run xark's *real* production backend: `setup_from_ptau` (generic over
//!      any `ConstraintSynthesizer`) → `Groth16::prove` → `xark_backend::verify`.
//!
//! A green test is the whole thesis: gadgets live in the frontend, the backend
//! is lean, and it proves our IR directly.

mod common;

use std::collections::BTreeMap;

use ark_bn254::{Bn254, Fr};
use ark_groth16::Groth16;
use ark_snark::SNARK;

use xark_backend::ptau::{parse_ptau, setup_from_ptau, Phase2Error};
use xark_backend::Groth16Keys;
use xark_ir::{primitive, solver, R1csProgram, VarId};
use xark_prover::{fr_from_decimal, XarkCircuit};

use common::build_valid_ptau;

fn fixture(name: &str) -> String {
    let p = format!(
        "{}/tests/fixtures/xark_ir/{name}",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {p}: {e}"))
}

fn load() -> (R1csProgram, primitive::PrimitiveProgram) {
    let r1cs = xark_ir::json::from_json(&fixture("cube_r1cs.json")).expect("r1cs.json");
    let prim = primitive::from_json(&fixture("cube_circuit.json")).expect("circuit.json");
    (r1cs, prim)
}

/// xark's real phase-2 setup from a synthetic ptau, growing the power on demand.
fn setup(r1cs: &R1csProgram, seed: &[u8; 32]) -> Groth16Keys {
    let mut power = 8u32;
    loop {
        let ptau = parse_ptau(&build_valid_ptau(power)).expect("synthetic ptau parses");
        match setup_from_ptau(XarkCircuit::for_setup(r1cs.clone()), &ptau, seed) {
            Ok(keys) => return keys,
            Err(Phase2Error::PtauTooSmall {
                required_domain_size,
                ..
            }) => power = required_domain_size.trailing_zeros(),
            Err(e) => panic!("setup_from_ptau failed: {e}"),
        }
    }
}

#[test]
fn cube_proves_and_verifies_through_xark_backend_no_acir() {
    let (r1cs, prim) = load();

    // cube: a^3 = c. Prove knowledge of a = 3 binding the public c = 27.
    let id = |name: &str| {
        prim.vars
            .iter()
            .find(|v| v.name == name)
            .unwrap_or_else(|| panic!("var {name}"))
            .id
    };
    let mut inputs: BTreeMap<VarId, String> = BTreeMap::new();
    inputs.insert(id("secret"), "3".to_string());
    inputs.insert(id("result"), "27".to_string());

    // Witness produced by OUR solver, then mapped into the field.
    let assign_fp = solver::solve(&prim, &inputs).expect("solve witness");
    let assign: BTreeMap<VarId, Fr> = assign_fp
        .iter()
        .map(|(k, v)| (*k, fr_from_decimal(&v.to_decimal())))
        .collect();

    // xark's real backend: setup → prove → verify.
    let seed = [7u8; 32];
    let keys = setup(&r1cs, &seed);

    let circ = XarkCircuit::for_proving(r1cs.clone(), assign);
    let pi = circ.public_inputs();
    assert_eq!(pi.len(), 1, "cube has one public input (c)");

    let mut rng = xark_backend::test_rng();
    let proof =
        Groth16::<Bn254>::prove(&keys.proving_key, circ, &mut rng).expect("prove via xark keys");

    assert!(
        xark_backend::verify(&keys.verifying_key, &proof, &pi).expect("verify"),
        "our xark-IR circuit must verify through xark's backend"
    );

    // Soundness smoke test: the public input is bound — tampering it fails.
    let mut bad = pi.clone();
    bad[0] += Fr::from(1u64);
    assert!(
        !xark_backend::verify(&keys.verifying_key, &proof, &bad).expect("verify tampered"),
        "tampering the public input must invalidate the proof"
    );
}
