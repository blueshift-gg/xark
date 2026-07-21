//! Ad-hoc solver microbenchmark (run with `--ignored --nocapture`).
//!
//! Builds a large BN254 witness-gen program dominated by the ops whose cost
//! differs most between the `num-bigint` and Montgomery `Fr` field backends —
//! multiplications, modular inverses, and bit-decomposition — then times
//! `solver::solve`. Used to A/B the field-arithmetic swap; not a correctness
//! test (that is covered by the gadget KAT `vec.rs` suites).

use std::collections::BTreeMap;
use std::time::Instant;

use xark_ir::linear_combination::LinearCombination as Lc;
use xark_ir::primitive::{FieldSpec, PrimitiveProgram, Var, VarRole, WitnessGen};

fn workload() -> PrimitiveProgram {
    // Tunable via env so the same binary drives both A and B runs.
    let muls: u32 = std::env::var("BENCH_MULS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(400_000);
    let invs: u32 = std::env::var("BENCH_INVS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(20_000);
    let bit_groups: u32 = std::env::var("BENCH_BITGROUPS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(20_000);

    let mut vars = vec![Var {
        id: 0,
        name: "seed".into(),
        role: VarRole::PrivateInput,
    }];
    let mut wg = Vec::new();
    let mut next: u32 = 1;

    // Square chain: out_i = prev * prev — a dense stream of field muls.
    let mut prev = 0u32;
    for _ in 0..muls {
        let out = next;
        next += 1;
        vars.push(Var {
            id: out,
            name: String::new(),
            role: VarRole::Derived,
        });
        wg.push(WitnessGen::Product {
            out,
            left: Lc::var(prev),
            right: Lc::var(prev),
        });
        prev = out;
    }

    // Inverses of the running value + 1 (nonzero): modpow on the generic path,
    // native inversion on BN254.
    for _ in 0..invs {
        let out = next;
        next += 1;
        vars.push(Var {
            id: out,
            name: String::new(),
            role: VarRole::Derived,
        });
        wg.push(WitnessGen::Inverse {
            out,
            input: Lc::var(prev) + Lc::constant("1"),
        });
        prev = out;
    }

    // Bit-decomposition of a value into 32 bits per group.
    for _ in 0..bit_groups {
        let outs: Vec<u32> = (0..32)
            .map(|_| {
                let id = next;
                next += 1;
                vars.push(Var {
                    id,
                    name: String::new(),
                    role: VarRole::Derived,
                });
                id
            })
            .collect();
        wg.push(WitnessGen::Bits {
            outs,
            input: Lc::var(prev),
        });
    }

    PrimitiveProgram {
        field: FieldSpec::bn254(),
        vars,
        constraints: Vec::new(),
        witness_gen: wg,
    }
}

/// The prove path turns every solved `Fp` into an ark `Fr`. Historically that
/// went `Fr → to_decimal() → parse` (a string round-trip per witness variable);
/// `as_bn254_fr()` hands back the inner `Fr` directly. Measure both over a full
/// witness.
#[test]
#[ignore = "microbenchmark; run explicitly with --ignored --nocapture"]
fn bench_witness_to_fr() {
    use ark_bn254::Fr;
    use std::str::FromStr;

    let program = workload();
    let mut inputs = BTreeMap::new();
    inputs.insert(0u32, "7".to_string());
    let assign = xark_ir::solver::solve(&program, &inputs).expect("solve");

    // Old path: format to decimal, reparse into Fr.
    let start = Instant::now();
    let mut acc = Fr::from(0u64);
    for v in assign.values() {
        acc += Fr::from_str(&v.to_decimal()).unwrap();
    }
    let old = start.elapsed();
    std::hint::black_box(acc);

    // New path: hand back the inner Fr.
    let start = Instant::now();
    let mut acc = Fr::from(0u64);
    for v in assign.values() {
        acc += v.as_bn254_fr().unwrap();
    }
    let new = start.elapsed();
    std::hint::black_box(acc);

    println!(
        "BENCH witness->Fr over {} vars: string round-trip {:?}  vs  as_bn254_fr {:?}  ({:.1}x)",
        assign.len(),
        old,
        new,
        old.as_secs_f64() / new.as_secs_f64(),
    );
}

#[test]
#[ignore = "microbenchmark; run explicitly with --ignored --nocapture"]
fn bench_bn254_solve() {
    let program = workload();
    let mut inputs = BTreeMap::new();
    inputs.insert(0u32, "7".to_string());

    // Warm + measured runs.
    let _ = xark_ir::solver::solve(&program, &inputs).expect("solve");
    let iters = 3;
    let start = Instant::now();
    for _ in 0..iters {
        let a = xark_ir::solver::solve(&program, &inputs).expect("solve");
        std::hint::black_box(&a);
    }
    let per = start.elapsed() / iters;
    println!(
        "BENCH bn254 solve: {:?}/iter  ({} muls, {} invs, {} bit-groups, {} vars)",
        per,
        std::env::var("BENCH_MULS").unwrap_or_else(|_| "400000".into()),
        std::env::var("BENCH_INVS").unwrap_or_else(|_| "20000".into()),
        std::env::var("BENCH_BITGROUPS").unwrap_or_else(|_| "20000".into()),
        program.vars.len(),
    );
}
