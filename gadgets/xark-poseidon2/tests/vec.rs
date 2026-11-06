//! End-to-end validation of the Poseidon2 gadget (BN254, t=3, α=5, R_F=8,
//! R_P=56) against its reference permutation.
//!
//! The circuit source is compiled to the primitive IR via
//! the shared `xark-test-harness` crate, then the reference solver runs a known test
//! vector produced by `poseidon2_ref.py` (which uses the *identical* Horizen
//! Labs constants + matrices as the gadget). We check that it (a) solves and
//! satisfies every constraint, (b) is analyzer-clean (no under-constrained
//! variables), and (c) a wrong public output is rejected.
//!
//! The reference vectors below are the output of `poseidon2_ref.py` — see that
//! file for the canonical constants and the matrix-shortcut cross-checks.

use std::collections::BTreeMap;

use xark_ir::primitive::PrimitiveProgram;
use xark_ir::solver;

/// Compile a circuit source string to its primitive program via the shared
/// test harness (see `xark-test-harness`).
fn compile(name: &str, src: &str) -> PrimitiveProgram {
    let c = xark_test_harness::compile_source(name, src, "bn254");
    assert!(c.status_success, "compile failed for {name}: {}", c.stderr);
    c.program()
}

fn id_of(p: &PrimitiveProgram, name: &str) -> u32 {
    p.vars
        .iter()
        .find(|v| v.name == name)
        .map(|v| v.id)
        .unwrap()
}

/// The full permutation circuit: `poseidon2_perm([in0,in1,in2]) == [out0,out1,out2]`.
const PERM_SRC: &str = "#![no_std]\n\
    use xark::{require_eq, Field, Private, Public};\n\
    use xark_poseidon2::poseidon2_perm;\n\
    pub fn circuit(\n\
      in0: Private<Field>, in1: Private<Field>, in2: Private<Field>,\n\
      out0: Public<Field>, out1: Public<Field>, out2: Public<Field>) {\n\
      let o = poseidon2_perm([in0, in1, in2]);\n\
      require_eq(o[0], out0);\n\
      require_eq(o[1], out1);\n\
      require_eq(o[2], out2);\n\
    }\n";

/// Reference vector from `poseidon2_ref.py`: `poseidon2_perm([1,2,3])`.
///   (identical constants/matrices as the gadget; matches Horizen Labs bn256.)
const IN_123: [&str; 3] = ["1", "2", "3"];
const OUT_123: [&str; 3] = [
    "4737982494702600552753609419126955242994596445692557044681458296415162795880",
    "9698155156890762076414037574068404457164720954413259397447872502075783415658",
    "18259628997120261506554896720810362547891614655348127750921457211768261324825",
];

#[test]
fn poseidon2_perm_matches_reference_vector() {
    let p = compile("perm", PERM_SRC);
    eprintln!(
        "Poseidon2 circuit: {} vars, {} constraints",
        p.vars.len(),
        p.constraints.len()
    );

    let mut inputs = BTreeMap::new();
    for i in 0..3 {
        inputs.insert(id_of(&p, &format!("in{i}")), IN_123[i].to_string());
        inputs.insert(id_of(&p, &format!("out{i}")), OUT_123[i].to_string());
    }

    let assign = solver::solve_and_check(&p, &inputs)
        .expect("Poseidon2([1,2,3]) reference vector must verify");

    let holes = solver::analyze_underconstrained(&p, &assign);
    assert!(holes.is_empty(), "Poseidon2 under-constrained: {holes:?}");

    // A wrong public output must be rejected.
    inputs.insert(id_of(&p, "out0"), "0".to_string());
    assert!(
        solver::solve_and_check(&p, &inputs).is_err(),
        "wrong Poseidon2 output accepted"
    );
}

/// Second independent vector: `poseidon2_perm([0,0,0])` from `poseidon2_ref.py`.
const OUT_000: [&str; 3] = [
    "21177166670744647784289648293577786481357446166129397094207318338605633126018",
    "13629302801197998987814902320299027581009939610751955228105166233386644439248",
    "20016279581229773656890104823225294246488953781156758873918627636762146545760",
];

#[test]
fn poseidon2_perm_zero_input() {
    let p = compile("perm", PERM_SRC);
    let mut inputs = BTreeMap::new();
    for (i, out) in OUT_000.iter().enumerate() {
        inputs.insert(id_of(&p, &format!("in{i}")), "0".to_string());
        inputs.insert(id_of(&p, &format!("out{i}")), out.to_string());
    }
    let assign = solver::solve_and_check(&p, &inputs)
        .expect("Poseidon2([0,0,0]) reference vector must verify");
    assert!(
        solver::analyze_underconstrained(&p, &assign).is_empty(),
        "Poseidon2 under-constrained"
    );
}

/// `native` (host, `ark_bn254::Fr`) computes the same reference vectors.
#[test]
fn native_perm_matches_reference_vectors() {
    use ark_ff::PrimeField;
    use xark_poseidon2::native::{Fr, poseidon2_perm};
    let dec = |s: [Fr; 3]| s.map(|x| x.into_bigint().to_string());
    let out = poseidon2_perm([Fr::from(1u64), Fr::from(2u64), Fr::from(3u64)]);
    assert_eq!(dec(out), OUT_123.map(String::from));
    let out = poseidon2_perm([Fr::from(0u64); 3]);
    assert_eq!(dec(out), OUT_000.map(String::from));
}

/// The circuit and `native` agree: the circuit accepts exactly the digest
/// `native` computes, for `hash2` and an odd-length `hash` (a padded block).
#[test]
fn native_matches_the_circuit() {
    use ark_ff::PrimeField;
    use xark_poseidon2::native::{self, Fr};
    let p = compile(
        "native_agree",
        "#![no_std]\n\
         use xark::{require_eq, Field, Private, Public};\n\
         use xark_poseidon2::{hash, hash2};\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>, c: Private<Field>,\n\
           h2: Public<Field>, h3: Public<Field>) {\n\
           require_eq(hash2(a, b), h2);\n\
           require_eq(hash([a, b, c]), h3);\n\
         }\n",
    );
    let (a, b, c) = (Fr::from(7u64), Fr::from(11u64), -Fr::from(1u64));
    let dec = |x: Fr| x.into_bigint().to_string();
    let h2 = native::hash2(a, b);
    let h3 = native::hash([a, b, c]);
    let mut inputs = BTreeMap::new();
    for (name, v) in [("a", a), ("b", b), ("c", c), ("h2", h2), ("h3", h3)] {
        inputs.insert(id_of(&p, name), dec(v));
    }
    solver::solve_and_check(&p, &inputs).expect("the circuit accepts native's digests");
    inputs.insert(id_of(&p, "h3"), dec(h3 + Fr::from(1u64)));
    assert!(solver::solve_and_check(&p, &inputs).is_err());
}
