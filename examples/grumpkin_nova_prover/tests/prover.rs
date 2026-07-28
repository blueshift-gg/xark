//! Nova prover checks on a real Xark-extracted R1CS.
//!
//! `nova_fold_relaxed_r1cs_is_satisfied` — the prover's core job: extract
//! `(A,B,C)` from `tiny` + two satisfying witnesses, fold the two relaxed
//! instances, and confirm the folded instance **satisfies the relaxed R1CS**
//! `Az∘Bz = u·Cz + E` (all `Fr` arithmetic).
//!
//! `grumpkin_pedersen_is_homomorphic_over_fq` — the commitment fold that
//! `grumpkin_nova_fold` verifies in-circuit is homomorphic over `Fq` (Grumpkin's
//! scalar field). The primary witness lives in `Fr ≠ Fq`, so its commitment is
//! the companion curve's job (CycleFold) — see `commit_fq`'s note.

use ark_bn254::{Fq, Fr};
use std::collections::BTreeMap;
use std::path::Path;
use xark_ir::linear_combination::VarId;
use xark_ir::r1cs::R1csProgram;
use xark_ir::{function_decode, solver};

use grumpkin_nova_prover::{Relaxed, add, commit_fq, fold, is_satisfied, run_ivc, scale};
use xark_ir::primitive::PrimitiveProgram;

/// Compile `tiny`, solve with the given `(a,b,c,d)`, return its R1CS + witness map.
fn extract(a: u64, b: u64, c: u64, d: u64) -> (R1csProgram, BTreeMap<VarId, Fr>) {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/tiny.rs");
    let comp = xark_test_harness::compile_file(&src, "tiny_nova", "bn254");
    assert!(comp.status_success, "compile tiny failed:\n{}", comp.stderr);
    let xbc = std::fs::read(comp.out_dir.join("circuit.xbc")).expect("read xbc");
    let cp = function_decode::expand_function_blob(&xbc).expect("expand xbc");
    let r1cs = cp.to_r1cs();
    let prim = cp.to_primitive();

    let id = |name: &str| r1cs.variables.iter().find(|v| v.name == name).unwrap().id;
    let mut inputs = BTreeMap::new();
    for (n, v) in [("a", a), ("b", b), ("c", c), ("d", d)] {
        inputs.insert(id(n), v.to_string());
    }
    let assign = solver::solve_and_check(&prim, &inputs).expect("witness must satisfy tiny");
    let z: BTreeMap<VarId, Fr> = assign
        .iter()
        .map(|(k, v)| (*k, v.as_bn254_fr().expect("bn254 fr")))
        .collect();
    (r1cs, z)
}

#[test]
fn nova_fold_relaxed_r1cs_is_satisfied() {
    // two satisfying instances of `tiny`: a*b=c, c+a=d.
    let (r1cs, z1) = extract(3, 4, 12, 15);
    let (_r2, z2) = extract(5, 6, 30, 35);

    let i1 = Relaxed::fresh(&r1cs, z1);
    let i2 = Relaxed::fresh(&r1cs, z2);
    assert!(
        is_satisfied(&r1cs, &i1),
        "instance 1 must satisfy the extracted R1CS"
    );
    assert!(
        is_satisfied(&r1cs, &i2),
        "instance 2 must satisfy the extracted R1CS"
    );

    let r = Fr::from(0x9e3779b97f4a7c15u64);
    let (folded, _t) = fold(&r1cs, &i1, &i2, r);

    // THE Nova prover correctness anchor: the folded RELAXED instance is satisfied.
    assert!(
        is_satisfied(&r1cs, &folded),
        "folded relaxed instance must satisfy Az∘Bz = u·Cz + E"
    );

    // a corrupted witness breaks relaxed satisfaction.
    let mut bad = folded.clone();
    if let Some((_, v)) = bad.z.iter_mut().next() {
        *v += Fr::from(1u64);
    }
    assert!(
        !is_satisfied(&r1cs, &bad),
        "a corrupted witness must not satisfy"
    );
}

/// Compile `tiny` once; return its R1CS + primitive program for repeated solving.
fn compile_tiny() -> (R1csProgram, PrimitiveProgram) {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/tiny.rs");
    let comp = xark_test_harness::compile_file(&src, "tiny_nova", "bn254");
    assert!(comp.status_success, "compile tiny failed:\n{}", comp.stderr);
    let xbc = std::fs::read(comp.out_dir.join("circuit.xbc")).expect("read xbc");
    let cp = function_decode::expand_function_blob(&xbc).expect("expand xbc");
    (cp.to_r1cs(), cp.to_primitive())
}

fn solve_tiny(
    r1cs: &R1csProgram,
    prim: &PrimitiveProgram,
    w: (u64, u64, u64, u64),
) -> BTreeMap<VarId, Fr> {
    let id = |name: &str| r1cs.variables.iter().find(|v| v.name == name).unwrap().id;
    let mut inputs = BTreeMap::new();
    for (n, v) in [("a", w.0), ("b", w.1), ("c", w.2), ("d", w.3)] {
        inputs.insert(id(n), v.to_string());
    }
    solver::solve_and_check(prim, &inputs)
        .expect("witness must satisfy tiny")
        .iter()
        .map(|(k, v)| (*k, v.as_bn254_fr().unwrap()))
        .collect()
}

#[test]
fn ivc_stepping_loop_accumulates() {
    let (r1cs, prim) = compile_tiny();
    // 4 satisfying steps of `tiny` (a*b=c, c+a=d).
    let steps: Vec<_> = [
        (3, 4, 12, 15),
        (5, 6, 30, 35),
        (2, 7, 14, 16),
        (8, 9, 72, 80),
    ]
    .into_iter()
    .map(|w| solve_tiny(&r1cs, &prim, w))
    .collect();
    let challenges = [Fr::from(11u64), Fr::from(13u64), Fr::from(17u64)];

    // fold all 4 into one running accumulator.
    let acc = run_ivc(&r1cs, &steps, &challenges);
    assert!(
        is_satisfied(&r1cs, &acc),
        "the 4-step IVC accumulator must satisfy the relaxed R1CS"
    );

    // a single corrupted step poisons the accumulator.
    let mut bad = steps.clone();
    if let Some((_, v)) = bad[2].iter_mut().next() {
        *v += Fr::from(1u64);
    }
    assert!(
        !is_satisfied(&r1cs, &run_ivc(&r1cs, &bad, &challenges)),
        "a corrupted step must break the accumulator"
    );
}

#[test]
fn grumpkin_pedersen_is_homomorphic_over_fq() {
    // The commitment fold `grumpkin_nova_fold` verifies in-circuit:
    // commit(a + r·b) == commit(a) + r·commit(b), over Fq (Grumpkin's scalar field).
    let a: Vec<Fq> = (0..6).map(|i| Fq::from(3 * i + 7)).collect();
    let b: Vec<Fq> = (0..6).map(|i| Fq::from(5 * i + 2)).collect();
    let r = Fq::from(0x9e3779b97f4a7c15u64);
    let folded: Vec<Fq> = a.iter().zip(&b).map(|(x, y)| *x + r * *y).collect();

    assert_eq!(
        commit_fq(&folded, 0),
        add(commit_fq(&a, 0), scale(commit_fq(&b, 0), r)),
        "Grumpkin Pedersen must be homomorphic over Fq"
    );
}

#[test]
fn stream_check_matches_solve_and_check() {
    // Compile `tiny`, then verify the streaming check agrees with the flat one:
    // accepts a valid witness and rejects a tampered public input.
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/tiny.rs");
    let comp = xark_test_harness::compile_file(&src, "tiny_stream", "bn254");
    assert!(comp.status_success, "compile tiny failed:\n{}", comp.stderr);
    let xbc = std::fs::read(comp.out_dir.join("circuit.xbc")).expect("read xbc");
    let cp = function_decode::expand_function_blob(&xbc).unwrap();
    let r1cs = cp.to_r1cs();
    let id = |n: &str| r1cs.variables.iter().find(|v| v.name == n).unwrap().id;

    // a*b=c, c+a=d : (3,4,12,15) is valid.
    let mut good: BTreeMap<u32, String> = BTreeMap::new();
    for (n, v) in [("a", "3"), ("b", "4"), ("c", "12"), ("d", "15")] {
        good.insert(id(n), v.to_string());
    }
    function_decode::stream_check(&xbc, &good)
        .expect("streaming check must accept a valid witness");

    // tamper c (3*4 != 13) -> the streamed a*b=c row must fail.
    let mut bad = good.clone();
    bad.insert(id("c"), "13".to_string());
    assert!(
        function_decode::stream_check(&xbc, &bad).is_err(),
        "streaming check must reject a tampered witness"
    );
}

#[test]
fn streaming_verify_accepts_faithful_and_rejects_mutated() {
    // The build-time `XARK_VERIFY` gate, streamed: `verify_blob_matches` must
    // accept an artifact that expands to its flat lowering, and reject any drift.
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/tiny.rs");
    let comp = xark_test_harness::compile_file(&src, "tiny_verify", "bn254");
    assert!(comp.status_success, "compile tiny failed:\n{}", comp.stderr);
    let xbc = std::fs::read(comp.out_dir.join("circuit.xbc")).expect("read xbc");
    let cp = function_decode::expand_function_blob(&xbc).unwrap();
    let r1cs = cp.to_r1cs();
    let prim = cp.to_primitive();

    // Faithful: the artifact expands byte-identically to (r1cs, prim).
    function_decode::verify_blob_matches(&xbc, &r1cs, &prim)
        .expect("faithful artifact must verify");

    // Mutated constraint: flip one row's `c` -> must be rejected.
    let mut bad_r1cs = r1cs.clone();
    bad_r1cs.constraints[0].c = xark_ir::linear_combination::LinearCombination::var(999);
    assert!(
        function_decode::verify_blob_matches(&xbc, &bad_r1cs, &prim).is_err(),
        "a mutated constraint must fail verification"
    );

    // Mutated constraint count: drop a row -> must be rejected.
    let mut short_r1cs = r1cs.clone();
    short_r1cs.constraints.pop();
    assert!(
        function_decode::verify_blob_matches(&xbc, &short_r1cs, &prim).is_err(),
        "a missing constraint must fail verification"
    );

    // Mutated witness program: an extra op the artifact doesn't have -> rejected.
    // (`tiny`'s own witness ops are pruned, so add one rather than drop.)
    let mut long_prim = prim.clone();
    long_prim
        .witness_gen
        .push(xark_ir::primitive::WitnessGen::Linear {
            out: 0,
            lc: xark_ir::linear_combination::LinearCombination::var(0),
        });
    assert!(
        function_decode::verify_blob_matches(&xbc, &r1cs, &long_prim).is_err(),
        "an extra witness op must fail verification"
    );
}

#[test]
fn stream_analyze_matches_flat_analyzer() {
    // Compile tiny, solve, and confirm the streaming analyzer gives byte-identical
    // results to the flat `analyze_underconstrained_cp`.
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/tiny.rs");
    let comp = xark_test_harness::compile_file(&src, "tiny_analyze", "bn254");
    assert!(comp.status_success, "compile tiny failed:\n{}", comp.stderr);
    let xbc = std::fs::read(comp.out_dir.join("circuit.xbc")).unwrap();
    let cp = function_decode::expand_function_blob(&xbc).unwrap();
    let id = |n: &str| cp.vars.iter().find(|v| v.name == n).unwrap().id;

    let mut inputs: BTreeMap<u32, String> = BTreeMap::new();
    for (n, v) in [("a", "3"), ("b", "4"), ("c", "12"), ("d", "15")] {
        inputs.insert(id(n), v.to_string());
    }
    let assign = solver::solve_and_check(&cp.to_primitive(), &inputs).unwrap();

    let key = |u: &solver::UnderConstrained| (u.var, u.reason.clone());
    let mut flat: Vec<_> = solver::analyze_underconstrained_cp(&cp, &assign)
        .iter()
        .map(key)
        .collect();
    let mut stream: Vec<_> = function_decode::stream_analyze(&xbc, &inputs)
        .unwrap()
        .iter()
        .map(key)
        .collect();
    flat.sort();
    stream.sort();
    assert_eq!(
        stream, flat,
        "streaming analyzer must match the flat analyzer exactly"
    );
}
