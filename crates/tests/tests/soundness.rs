//! Completeness check + structural report for the ACIR→R1CS lowering.
//!
//! The on-chain `#[svm_test]`s prove the *correct* statement verifies. This
//! test adds two things they can't:
//!
//! 1. **Completeness, asserted directly**: for every fixture, the nargo
//!    reference witness *satisfies* the lowered R1CS (`cs.is_satisfied()`).
//!    That's the property the on-chain proofs imply, checked here without
//!    proving — fast, and it pins lowering regressions.
//! 2. **A structural report** of where each variable's value is (or isn't)
//!    determined, via a single-variable perturbation probe.
//!
//! ## Why the probe only *reports*
//!
//! The probe perturbs each `z[v]` by four *distinct* deltas and checks the
//! constraints touching `v`. Each touched row's sensitivity to `v` is a
//! degree-≤2 polynomial in the delta, so surviving 4 distinct deltas proves
//! the row is *identically* insensitive — a real "free at this witness", not a
//! lucky delta. But "free in the constraint matrices" does **not** mean
//! "under-constrained / forgeable" under Groth16, for two reasons we verified
//! empirically:
//!
//! * **Public inputs are bound by the IC, not by constraints.** `large_pi`
//!   has 14 public inputs that appear in *no* constraint, yet tampering any
//!   of them makes verification fail — arkworks gives every public input a
//!   non-trivial `gamma_abc` element regardless. So a "free public column"
//!   here is not a bug. (The real binding check is `tests/binding.rs` in
//!   `xark-verifier`, which tampers each public input end-to-end.)
//! * **Internal free witnesses are inert.** `curve_basic` has 512 free
//!   witness vars; each sits only in products zeroed at this witness
//!   (`A·B=C` with `A·z=0`) — conditionally-constrained scratch on an
//!   unselected branch. It can't influence any live constraint or public
//!   output, so it's sound.
//!
//! So this file asserts only completeness, and prints the structure for
//! documentation / regression-watching. Full under-constraint soundness is
//! undecidable in general and out of scope; the meaningful, false-positive-
//! free soundness gate is the public-input binding sweep.
//!
//! Run with `--release` (debug synthesis of the hash/aes circuits is slow).

use ark_bn254::Fr;
use ark_ff::Zero;
use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystem, R1CS_PREDICATE_LABEL};
use std::collections::BTreeMap;

use xark_acir_r1cs::artifact::parse_artifact_file;
use xark_acir_r1cs::lower::LoweredAcirCircuit;
use xark_acir_r1cs::witness::parse_witness_file;
use xark_backend::circuit::NoirGroth16Circuit;

mod common;
use common::fixture_dir;

/// One sparse-row dot product `row · z`.
fn dot(row: &[(Fr, usize)], z: &[Fr]) -> Fr {
    row.iter().fold(Fr::zero(), |acc, (c, i)| acc + *c * z[*i])
}

struct Report {
    num_instance: usize,
    num_vars: usize,
    num_constraints: usize,
    /// Variables touching no constraint at all, split public vs witness.
    dead_public: usize,
    dead_witness: usize,
    /// Internal witness vars provably free (but inert) at this witness.
    free_witness: usize,
}

/// Synthesize the fixture's reference witness, assert it satisfies the R1CS
/// (completeness), then run the single-variable structural probe.
fn analyze(name: &str) -> Report {
    let dir = fixture_dir();
    let artifact = parse_artifact_file(&dir.join(format!("{name}.json"))).expect("parse artifact");
    let witness = parse_witness_file(&dir.join(format!("{name}.gz"))).expect("parse witness");
    let lowered = LoweredAcirCircuit::new(artifact).expect("lower");

    let cs = ConstraintSystem::<Fr>::new_ref();
    let circuit = NoirGroth16Circuit::for_proving(lowered, witness);
    ConstraintSynthesizer::generate_constraints(circuit, cs.clone()).expect("synthesize");
    cs.finalize();

    // Completeness: the reference witness MUST satisfy the lowered R1CS.
    assert!(
        cs.is_satisfied().expect("is_satisfied"),
        "{name}: nargo reference witness does NOT satisfy the lowered R1CS"
    );

    // arkworks 0.6: `to_matrices` returns a map keyed by predicate label; the
    // plain R1CS predicate's entry is `[A, B, C]`. Assignments are now methods.
    let matrices_map = cs.to_matrices().expect("matrices (cs is finalized)");
    let m = &matrices_map[R1CS_PREDICATE_LABEL];
    let (ma, mb, mc) = (&m[0], &m[1], &m[2]);
    let (z, num_instance) = {
        let inst = cs.instance_assignment().expect("instance assignment");
        let wit = cs.witness_assignment().expect("witness assignment");
        let num_instance = inst.len();
        let mut z = inst;
        z.extend(wit.iter().copied());
        (z, num_instance)
    };
    let num_vars = z.len();

    // Per-variable incidence in A/B/C.
    let mut inc_a = vec![Vec::new(); num_vars];
    let mut inc_b = vec![Vec::new(); num_vars];
    let mut inc_c = vec![Vec::new(); num_vars];
    for (r, row) in ma.iter().enumerate() {
        for (coeff, col) in row {
            inc_a[*col].push((r, *coeff));
        }
    }
    for (r, row) in mb.iter().enumerate() {
        for (coeff, col) in row {
            inc_b[*col].push((r, *coeff));
        }
    }
    for (r, row) in mc.iter().enumerate() {
        for (coeff, col) in row {
            inc_c[*col].push((r, *coeff));
        }
    }

    let nrows = ma.len();
    let mut az = vec![Fr::zero(); nrows];
    let mut bz = vec![Fr::zero(); nrows];
    let mut cz = vec![Fr::zero(); nrows];
    for r in 0..nrows {
        az[r] = dot(&ma[r], &z);
        bz[r] = dot(&mb[r], &z);
        cz[r] = dot(&mc[r], &z);
    }

    // Four distinct non-zero deltas; surviving all four proves (per touched
    // row, degree-≤2 in the delta) identical insensitivity.
    let deltas = [
        Fr::from(1u64),
        Fr::from(2u64),
        Fr::from(7u64),
        Fr::from(u64::MAX),
    ];

    let (mut dead_public, mut dead_witness, mut free_witness) = (0usize, 0usize, 0usize);
    for v in 1..num_vars {
        let mut rows: BTreeMap<usize, (Fr, Fr, Fr)> = BTreeMap::new();
        for (r, c) in &inc_a[v] {
            rows.entry(*r)
                .or_insert((Fr::zero(), Fr::zero(), Fr::zero()))
                .0 += *c;
        }
        for (r, c) in &inc_b[v] {
            rows.entry(*r)
                .or_insert((Fr::zero(), Fr::zero(), Fr::zero()))
                .1 += *c;
        }
        for (r, c) in &inc_c[v] {
            rows.entry(*r)
                .or_insert((Fr::zero(), Fr::zero(), Fr::zero()))
                .2 += *c;
        }

        if rows.is_empty() {
            if v < num_instance {
                dead_public += 1; // bound by the IC, not the matrices — sound
            } else {
                dead_witness += 1; // unused scratch — inert
            }
            continue;
        }

        let pinned = deltas.iter().any(|d| {
            rows.iter().any(|(r, (ca, cb, cc))| {
                (az[*r] + *ca * d) * (bz[*r] + *cb * d) != cz[*r] + *cc * d
            })
        });
        if !pinned && v >= num_instance {
            free_witness += 1;
        }
    }

    Report {
        num_instance,
        num_vars,
        num_constraints: nrows,
        dead_public,
        dead_witness,
        free_witness,
    }
}

fn report(name: &str) {
    let r = analyze(name);
    eprintln!(
        "{name}: witness satisfies R1CS — {} vars, {} constraints, {} public; \
 structure: {} free internal witnesses (inert), \
 {} unused public inputs (IC-bound), {} unused witnesses",
        r.num_vars,
        r.num_constraints,
        r.num_instance - 1,
        r.free_witness,
        r.dead_public,
        r.dead_witness,
    );
}

const CIRCUITS: &[&str] = &[
    "arithmetic_square",
    "arithmetic_public_inputs",
    "bitwise_basic",
    "curve_basic",
    "mixed_pi",
    "reorder_pi",
    "range_basic",
    "memory_const",
    "memory_var",
    "multi_function",
    "nested_calls",
    "return_values_only",
    "brillig_basic",
    "poseidon_basic",
    "large_pi",
    "sha256_basic",
    "keccak_basic",
    "aes128_basic",
    "blake2s_basic",
    "blake3_basic",
];

/// Reference witnesses satisfy the lowered R1CS for every circuit
/// (completeness), with a structural report printed for each.
#[test]
fn lowering_is_complete_over_fixtures() {
    for name in CIRCUITS {
        report(name);
    }
}

#[test]
#[ignore = "ECDSA circuits are very large; run explicitly with --release"]
fn lowering_is_complete_ecdsa() {
    report("ecdsa_basic");
    report("ecdsa_r1_basic");
}

/// The prove-path guard fires: corrupting a witness value so the assignment no
/// longer satisfies the R1CS makes `prove` return `Unsatisfiable` instead of
/// emitting a silently-invalid proof.
#[test]
fn prove_rejects_unsatisfying_witness() {
    use ark_relations::gr1cs::SynthesisError;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    let dir = fixture_dir();
    let artifact = parse_artifact_file(&dir.join("arithmetic_square.json")).expect("artifact");
    let mut witness = parse_witness_file(&dir.join("arithmetic_square.gz")).expect("witness");
    let lowered = LoweredAcirCircuit::new(artifact).expect("lower");

    let public_of = |w: &xark_acir_r1cs::witness::WitnessMap<Fr>| -> Vec<Fr> {
        lowered
            .artifact
            .public_inputs
            .iter()
            .map(|idx| *w.get(idx).expect("public input present in witness"))
            .collect()
    };

    let mut rng = ChaCha20Rng::seed_from_u64(1);
    let keys = xark_backend::setup(NoirGroth16Circuit::for_setup(lowered.clone()), &mut rng)
        .expect("setup");

    // Baseline: the untouched witness proves fine (and self-verifies).
    let pi = public_of(&witness);
    xark_backend::prove(
        &keys.proving_key,
        NoirGroth16Circuit::for_proving(lowered.clone(), witness.clone()),
        &pi,
        &mut rng,
    )
    .expect("valid witness should prove");

    // Corrupt one witness value → assignment no longer satisfies x·x = y, so
    // the fresh proof fails the post-prove self-check.
    let (_, v) = witness
        .values
        .iter_mut()
        .next()
        .expect("at least one witness");
    *v += Fr::from(1u64);
    let pi = public_of(&witness);

    // Rejection can surface two ways depending on build profile:
    // * release — our post-prove self-check returns `Unsatisfiable`;
    // * debug — arkworks' own `debug_assert!(cs.is_satisfied())` inside
    // `Groth16::prove` panics first.
    // Both mean "an unsatisfying witness does not yield a valid proof". Silence
    // the panic hook so the expected-panic path doesn't spam the test log.
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        xark_backend::prove(
            &keys.proving_key,
            NoirGroth16Circuit::for_proving(lowered, witness),
            &pi,
            &mut rng,
        )
    }));
    std::panic::set_hook(prev_hook);

    let rejected = match outcome {
        Err(_) => true,                                 // arkworks debug_assert panicked
        Ok(Err(SynthesisError::Unsatisfiable)) => true, // our self-check
        _ => false,
    };
    assert!(
        rejected,
        "unsatisfying witness was not rejected: {outcome:?}"
    );
}
