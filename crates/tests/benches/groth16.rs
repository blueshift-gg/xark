//! End-to-end Groth16 benchmarks: setup, prove, verify.
//!
//! Covers three representative circuits committed under `crates/tests/fixtures/`:
//!
//! * `arithmetic_square` — minimal AssertZero-only circuit (one mul + one
//!   linear). Floor case for setup/prove cost.
//! * `sha256_basic` — one SHA-256 compression call (~53k constraints).
//!   Representative hash-heavy workload.
//! * `ecdsa_basic` — one ECDSA secp256k1 verify (~3.6M constraints).
//!   Representative crypto-heavy workload.
//!
//! Each circuit measures three operations:
//! 1. `setup` (parameter generation, insecure dev mode).
//! 2. `prove` (assumes setup output is available).
//! 3. `verify` (assumes setup + prove outputs are available).
//!
//! Run with `cargo bench -p xark-tests`. Use
//! `cargo bench -p xark-tests -- --save-baseline before` and
//! `cargo bench -p xark-tests -- --baseline before` to compare across
//! optimisation PRs.

use std::path::{Path, PathBuf};
use std::time::Duration;

use ark_bn254::{Bn254, Fr};
use ark_groth16::{Groth16, Proof, ProvingKey, VerifyingKey};
use ark_snark::SNARK;
use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use xark_acir_r1cs::artifact::{NoirArtifact, parse_artifact_file};
use xark_acir_r1cs::lower::LoweredAcirCircuit;
use xark_acir_r1cs::witness::parse_witness_file;
use xark_backend::{circuit::NoirGroth16Circuit, setup::setup, verify::verify};

/// Resolve `crates/tests/fixtures/<name>.{json,gz}` under the crate.
/// Criterion runs benches from the crate's `Cargo.toml` directory, so we
/// walk up to find the workspace fixtures.
fn fixture_dir() -> PathBuf {
    let mut here: PathBuf = std::env::current_dir().expect("cwd");
    loop {
        let candidate = here.join("crates").join("tests").join("fixtures");
        if candidate.is_dir() {
            return candidate;
        }
        if !here.pop() {
            panic!(
                "could not locate crates/tests/fixtures/ relative to {:?}",
                std::env::current_dir()
            );
        }
    }
}

/// Load + lower a fixture, returning the artifact, witness, and lowered
/// circuit. Done once per benchmark group so the per-iteration cost is
/// only the operation we're measuring.
fn load_fixture(
    name: &str,
) -> (
    NoirArtifact,
    xark_acir_r1cs::witness::WitnessMap<Fr>,
    LoweredAcirCircuit,
) {
    let dir = fixture_dir();
    let artifact_path = dir.join(format!("{name}.json"));
    let witness_path = dir.join(format!("{name}.gz"));
    let artifact = parse_artifact_file(&artifact_path).expect("parse artifact");
    let witness = parse_witness_file(&witness_path).expect("parse witness");
    let lowered = LoweredAcirCircuit::new(artifact.clone()).expect("lower");
    (artifact, witness, lowered)
}

fn bench_circuit(c: &mut Criterion, name: &str) {
    let (_artifact, witness, lowered) = load_fixture(name);

    let mut group = c.benchmark_group(name);
    // The full ECDSA prove can take >10 seconds; relax criterion defaults.
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(20));

    // Setup ---------------------------------------------------------------
    group.bench_function("setup", |b| {
        b.iter_batched(
            || {
                (
                    NoirGroth16Circuit::for_setup(lowered.clone()),
                    ChaCha20Rng::seed_from_u64(0xAA55_CAFE),
                )
            },
            |(circuit, mut rng)| {
                let keys = setup(circuit, &mut rng).expect("setup");
                criterion::black_box(keys);
            },
            BatchSize::SmallInput,
        );
    });

    // Cache setup output once for prove / verify benches.
    let keys = {
        let mut rng = ChaCha20Rng::seed_from_u64(0xAA55_CAFE);
        let circuit = NoirGroth16Circuit::for_setup(lowered.clone());
        setup(circuit, &mut rng).expect("setup")
    };
    let pk: ProvingKey<Bn254> = keys.proving_key.clone();
    let vk: VerifyingKey<Bn254> = keys.verifying_key.clone();

    // Public input vector for the verifier.
    let public_inputs: Vec<Fr> = lowered
        .artifact
        .public_inputs
        .iter()
        .map(|idx| *witness.get(idx).expect("public input not found in witness"))
        .collect();

    // Prove ---------------------------------------------------------------
    group.bench_function("prove", |b| {
        b.iter_batched(
            || {
                (
                    NoirGroth16Circuit::for_proving(lowered.clone(), witness.clone()),
                    ChaCha20Rng::seed_from_u64(0x9B7E_CAFE),
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
    let proof: Proof<Bn254> = {
        let mut rng = ChaCha20Rng::seed_from_u64(0x9B7E_CAFE);
        let circuit = NoirGroth16Circuit::for_proving(lowered.clone(), witness.clone());
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

fn bench_arithmetic_square(c: &mut Criterion) {
    bench_circuit(c, "arithmetic_square");
}

fn bench_sha256_basic(c: &mut Criterion) {
    bench_circuit(c, "sha256_basic");
}

fn bench_ecdsa_basic(c: &mut Criterion) {
    bench_circuit(c, "ecdsa_basic");
}

criterion_group!(
    benches,
    bench_arithmetic_square,
    bench_sha256_basic,
    bench_ecdsa_basic,
);
criterion_main!(benches);

// Local helper to suppress unused-path warnings on the import.
#[allow(dead_code)]
fn _silence(p: &Path) {
    let _ = p;
}
