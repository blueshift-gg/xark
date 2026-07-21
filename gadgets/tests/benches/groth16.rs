//! End-to-end Groth16 benchmarks for xark's own pipeline: setup, prove, verify.
//!
//! This measures the *current* xark → xark-IR → R1CS → Groth16 path. Each
//! circuit is loaded from a committed fixture under
//! `gadgets/tests/tests/fixtures/xark_ir/` as an [`R1csProgram`] plus its
//! witness-gen [`primitive::PrimitiveProgram`]; the witness is solved once with
//! xark's own solver, then fed to xark's production backend circuit
//! [`XarkCircuit`].
//!
//! Covered circuit(s):
//!
//! * `cube` — prove knowledge of `a` with `a^3 = c`. Minimal floor case for
//!   setup/prove/verify cost.
//!
//! Each circuit measures three operations:
//! 1. `setup` (Groth16 circuit-specific parameter generation, dev mode).
//! 2. `prove` (assumes setup output is available).
//! 3. `verify` (assumes setup + prove outputs are available).
//!
//! The one-time work (fixture load, witness solve) happens outside the timed
//! closures so per-iteration cost is only the measured phase.
//!
//! Run with `cargo bench -p xark-tests`. Use
//! `cargo bench -p xark-tests -- --save-baseline before` and
//! `cargo bench -p xark-tests -- --baseline before` to compare across
//! optimisation PRs.

use std::collections::BTreeMap;

use ark_bn254::{Bn254, Fr};
use ark_groth16::{Groth16, Proof};
use ark_snark::SNARK;
use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

use xark_backend::setup::setup;
use xark_backend::{test_rng, verify, Groth16Keys};
use xark_ir::solver;
use xark_ir::{primitive, R1csProgram, VarId};
use xark_prover::{fr_from_decimal, XarkCircuit};

/// Read `gadgets/tests/tests/fixtures/xark_ir/<name>` (mirrors the e2e test).
fn fixture(name: &str) -> String {
    let p = format!(
        "{}/tests/fixtures/xark_ir/{name}",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {p}: {e}"))
}

/// Load an IR fixture (`<name>_r1cs.json` + `<name>_circuit.json`) and solve its
/// witness once, returning the R1CS program plus the field assignment.
///
/// `inputs` maps circuit variable *names* to decimal input values.
fn load_and_solve(name: &str, inputs: &[(&str, &str)]) -> (R1csProgram, BTreeMap<VarId, Fr>) {
    let r1cs =
        xark_ir::json::from_json(&fixture(&format!("{name}_r1cs.json"))).expect("parse r1cs.json");
    let prim = primitive::from_json(&fixture(&format!("{name}_circuit.json")))
        .expect("parse circuit.json");

    let id = |name: &str| {
        prim.vars
            .iter()
            .find(|v| v.name == name)
            .unwrap_or_else(|| panic!("var {name}"))
            .id
    };
    let mut named: BTreeMap<VarId, String> = BTreeMap::new();
    for (k, v) in inputs {
        named.insert(id(k), (*v).to_string());
    }

    let assign_fp = solver::solve(&prim, &named).expect("solve witness");
    let assign: BTreeMap<VarId, Fr> = assign_fp
        .iter()
        .map(|(k, v)| (*k, fr_from_decimal(&v.to_decimal())))
        .collect();

    (r1cs, assign)
}

fn bench_circuit(c: &mut Criterion, name: &str, inputs: &[(&str, &str)]) {
    let (r1cs, assign) = load_and_solve(name, inputs);

    let mut group = c.benchmark_group(name);

    // Setup ---------------------------------------------------------------
    group.bench_function("setup", |b| {
        b.iter_batched(
            || (XarkCircuit::for_setup(r1cs.clone()), test_rng()),
            |(circuit, mut rng)| {
                let keys = setup(circuit, &mut rng).expect("setup");
                criterion::black_box(keys);
            },
            BatchSize::SmallInput,
        );
    });

    // Cache setup output once for the prove / verify benches.
    let keys: Groth16Keys = {
        let mut rng = test_rng();
        setup(XarkCircuit::for_setup(r1cs.clone()), &mut rng).expect("setup")
    };
    let pk = keys.proving_key.clone();
    let vk = keys.verifying_key.clone();

    // Prove ---------------------------------------------------------------
    group.bench_function("prove", |b| {
        b.iter_batched(
            || {
                (
                    XarkCircuit::for_proving(r1cs.clone(), assign.clone()),
                    test_rng(),
                )
            },
            |(circuit, mut rng)| {
                let proof = Groth16::<Bn254>::prove(&pk, circuit, &mut rng).expect("prove");
                criterion::black_box(proof);
            },
            BatchSize::SmallInput,
        );
    });

    // Verify --------------------------------------------------------------
    let public_inputs: Vec<Fr> =
        XarkCircuit::for_proving(r1cs.clone(), assign.clone()).public_inputs();
    let proof: Proof<Bn254> = {
        let mut rng = test_rng();
        let circuit = XarkCircuit::for_proving(r1cs.clone(), assign.clone());
        Groth16::<Bn254>::prove(&pk, circuit, &mut rng).expect("prove")
    };
    group.bench_function("verify", |b| {
        b.iter(|| {
            let ok = verify(&vk, &proof, &public_inputs).expect("verify");
            assert!(ok, "proof must verify");
        });
    });

    group.finish();
}

fn bench_cube(c: &mut Criterion) {
    // cube: a^3 = c. Prove knowledge of a = 3 binding the public c = 27.
    bench_circuit(c, "cube", &[("secret", "3"), ("result", "27")]);
}

criterion_group!(benches, bench_cube);
criterion_main!(benches);
