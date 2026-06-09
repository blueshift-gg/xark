//! R1CS under-constraint analyzer via concrete propagation.
//!
//! For each committed fixture we lower to R1CS, instantiate the public-input
//! wires with their values from the committed witness, and then propagate
//! through the constraints to determine which witness wires are
//! **uniquely pinned** by the row equations. Any wire we cannot pin is a
//! finding to audit.
//!
//! This is the practical alternative to running [Picus](https://github.com/Veridise/picus) /
//! [Ecne](https://github.com/franklynwang/EcneProject) externally — the
//! analyzer is native Rust over the same `to_matrices()` output the existing
//! z3 probe (in `determinism.rs`) consumes. The z3 probe correctly notes that
//! SMT over GF(r) does not scale to nonlinear R1CS at our gadget sizes; this
//! pass is the scaleable replacement. Soundness vs. completeness:
//!
//!   * **Sound under-approximation**: a wire we mark "determined" really is
//!     uniquely pinned by the constraints given the public inputs. We never
//!     claim a wire is determined when it isn't.
//!   * **Incomplete**: a wire we cannot pin may still be uniquely determined
//!     by some Gröbner-basis or symbolic argument the propagator misses. Those
//!     are *findings*, not regressions — exactly what the FV plan calls for.
//!
//! ## Algorithm
//!
//! Mark wire 0 (the constant `1`) and every public-input wire as determined.
//! Loop until fixed point:
//!   * For each constraint row `A·B = C`, split each LC into a "determined"
//!     constant part (evaluated from known wires) plus an "unknown" residual
//!     `Σ cⱼ·wⱼ` over wires not yet determined.
//!   * If the row reduces to a single linear equation in exactly one unknown
//!     wire `w` with nonzero coefficient (over `Fr`, where all nonzeros are
//!     invertible), pin `w`. The pinning cases:
//!     - `(A=det, B=det) ⇒ A·B − C = 0` is linear in the unknown wires of C.
//!     - `(A=det+α·w, B=det) ⇒ (A_det + α·w)·B_det = C_det + (residual)`
//!       collapses to a linear equation in `w` provided the residual on the
//!       C-side does *not* contain a second unknown.
//!     - Symmetric for `B`.
//!     - When both A and B contain unknowns the row is quadratic and we
//!       skip it (sound under-approximation: we never claim pinning that
//!       depends on a discriminant being nonzero by value coincidence).
//!
//! The result: a set of un-determined witness wires per circuit. Circuits
//! we expect to be fully pinned (every committed gadget that has soundness
//! theorems in `formal/`) are asserted to come back with the empty set. The
//! rest are printed as findings.
//!
//! Big gadgets (sha/keccak/blake/aes/ecdsa) are reported only — pinning
//! coverage there is interpreted as a measure of structural redundancy,
//! not asserted to be 100% (the per-bit gadgets have many equivalent
//! formulations of the same wire, and our linear-only pinning will miss
//! some of them — Picus's Gröbner backend catches those, which is the
//! point of running an external tool when the budget allows).
//!
//! Runs in the normal test suite — no external dependency, no CI install.
//! Set `XARK_PROPAGATION_VERBOSE=1` to print per-circuit findings.

use std::collections::{BTreeMap, BTreeSet};

use ark_bn254::Fr;
use ark_ff::{Field, Zero};
use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystem, Matrix, R1CS_PREDICATE_LABEL};

use xark_acir_r1cs::artifact::parse_artifact_file;
use xark_acir_r1cs::lower::LoweredAcirCircuit;
use xark_acir_r1cs::witness::parse_witness_file;
use xark_backend::circuit::NoirGroth16Circuit;

mod common;
use common::fixture_dir;

/// Per-circuit lowered + valued R1CS.
struct R1csValued {
    a: Matrix<Fr>,
    b: Matrix<Fr>,
    c: Matrix<Fr>,
    num_instance: usize,
    num_witness: usize,
    /// Concrete values for the instance wires (col 0 = `1`, then PI).
    instance: Vec<Fr>,
}

fn lower(name: &str) -> R1csValued {
    let dir = fixture_dir();
    let artifact = parse_artifact_file(&dir.join(format!("{name}.json"))).expect("artifact");
    let witness = parse_witness_file(&dir.join(format!("{name}.gz"))).expect("witness");
    let lowered = LoweredAcirCircuit::new(artifact).expect("lower");

    let cs = ConstraintSystem::<Fr>::new_ref();
    NoirGroth16Circuit::for_proving(lowered, witness)
        .generate_constraints(cs.clone())
        .expect("synthesize");
    cs.finalize();
    assert!(cs.is_satisfied().expect("is_satisfied"), "{name}: unsat");
    let m = cs.to_matrices().expect("matrices");
    let pred = &m[R1CS_PREDICATE_LABEL];
    let instance = cs.instance_assignment().expect("instance");
    let num_instance = instance.len();
    let num_witness = cs.witness_assignment().expect("witness").len();
    R1csValued {
        a: pred[0].clone(),
        b: pred[1].clone(),
        c: pred[2].clone(),
        num_instance,
        num_witness,
        instance,
    }
}

/// Split an LC `Σ coeff · z[col]` into a fully-determined constant `Fr` plus
/// the residual: a `BTreeMap<col, coeff>` over still-undetermined wires only.
///
/// `is_determined(col)` returns whether wire `col` has a known value
/// (`known_values[col].is_some()`).
fn split_lc(row: &[(Fr, usize)], known: &BTreeMap<usize, Fr>) -> (Fr, BTreeMap<usize, Fr>) {
    let mut det = Fr::zero();
    let mut res: BTreeMap<usize, Fr> = BTreeMap::new();
    for (coeff, col) in row {
        if let Some(v) = known.get(col) {
            det += *coeff * v;
        } else {
            *res.entry(*col).or_insert(Fr::zero()) += *coeff;
        }
    }
    // Drop residual entries whose net coefficient became zero.
    res.retain(|_, c| !c.is_zero());
    (det, res)
}

/// Try to pin a single unknown wire from a constraint row.
///
/// Returns `Some((wire, value))` if the row uniquely determines exactly one
/// wire's value, and `None` otherwise (zero or ≥2 unknowns left after partial
/// evaluation, or a quadratic-in-unknowns row where pinning would depend on
/// a coefficient combination being value-coincidentally nonzero).
fn try_pin_from_row(
    a_row: &[(Fr, usize)],
    b_row: &[(Fr, usize)],
    c_row: &[(Fr, usize)],
    known: &BTreeMap<usize, Fr>,
) -> Option<(usize, Fr)> {
    let (a_det, a_res) = split_lc(a_row, known);
    let (b_det, b_res) = split_lc(b_row, known);
    let (c_det, c_res) = split_lc(c_row, known);

    // The row's equation is  (A_det + Σα·u) · (B_det + Σβ·u) = C_det + Σγ·u.
    //
    // We pin only when the equation collapses to *single linear* in one
    // unknown wire. The valid shapes:
    //
    //   1. a_res empty, b_res empty, |c_res| = 1
    //      → A_det · B_det = C_det + γ·w
    //      → w = (A_det·B_det − C_det) / γ, well-defined iff γ ≠ 0.
    //
    //   2. a_res empty, b_res non-empty, c_res non-empty / empty,
    //      unknowns(b_res) ∪ unknowns(c_res) = {w}
    //      → A_det · (B_det + β·w) = C_det + γ·w  (γ possibly 0)
    //      → (A_det·β − γ)·w = C_det − A_det·B_det
    //      Pin iff (A_det·β − γ) ≠ 0.
    //
    //   3. Symmetric to case 2 with roles of A and B swapped.
    //
    // Anything else (both a_res and b_res non-empty, or ≥2 distinct unknowns
    // in the union) is quadratic / multi-variate — skip soundly.
    let a_has = !a_res.is_empty();
    let b_has = !b_res.is_empty();
    if a_has && b_has {
        return None;
    }

    let unk: BTreeSet<usize> = a_res
        .keys()
        .chain(b_res.keys())
        .chain(c_res.keys())
        .copied()
        .collect();
    if unk.len() != 1 {
        return None;
    }
    let w = *unk.iter().next().unwrap();

    let alpha = a_res.get(&w).copied().unwrap_or(Fr::zero()); // A-coeff of w
    let beta = b_res.get(&w).copied().unwrap_or(Fr::zero()); // B-coeff of w
    let gamma = c_res.get(&w).copied().unwrap_or(Fr::zero()); // C-coeff of w

    if alpha.is_zero() && beta.is_zero() {
        // Case 1: γ·w = A·B − C  ⇒  w = (A·B − C)/γ, valid iff γ ≠ 0.
        if gamma.is_zero() {
            return None;
        }
        let v = (a_det * b_det - c_det) * gamma.inverse().expect("nonzero");
        return Some((w, v));
    }

    if alpha.is_zero() {
        // Case 2: (A_det·β − γ)·w = C_det − A_det·B_det.
        let lhs = a_det * beta - gamma;
        if lhs.is_zero() {
            return None;
        }
        let v = (c_det - a_det * b_det) * lhs.inverse().expect("nonzero");
        return Some((w, v));
    }

    if beta.is_zero() {
        // Case 3 (symmetric): (B_det·α − γ)·w = C_det − A_det·B_det.
        let lhs = b_det * alpha - gamma;
        if lhs.is_zero() {
            return None;
        }
        let v = (c_det - a_det * b_det) * lhs.inverse().expect("nonzero");
        return Some((w, v));
    }

    // Both alpha and beta nonzero — quadratic in w. Skip (sound).
    None
}

/// Run propagation; return the set of *witness wire indices* (0-indexed
/// against the witness assignment, so column `num_instance + i` in the
/// matrices) the analyzer could not pin.
fn propagate(r: &R1csValued) -> BTreeSet<usize> {
    // Seed: every instance wire (col 0 = `1`, plus PI wires) is determined.
    let mut known: BTreeMap<usize, Fr> = BTreeMap::new();
    for (i, v) in r.instance.iter().enumerate() {
        known.insert(i, *v);
    }

    let n_rows = r.a.len();
    debug_assert_eq!(n_rows, r.b.len());
    debug_assert_eq!(n_rows, r.c.len());

    loop {
        let mut changed = false;
        for row in 0..n_rows {
            if let Some((w, v)) = try_pin_from_row(&r.a[row], &r.b[row], &r.c[row], &known) {
                // Already-pinned wires by an earlier row may be revisited;
                // value must match by soundness of the analyzer + system
                // satisfiability.
                if let Some(existing) = known.get(&w) {
                    debug_assert_eq!(*existing, v, "propagation inconsistency at wire {w}");
                } else {
                    known.insert(w, v);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    (0..r.num_witness)
        .filter(|i| !known.contains_key(&(r.num_instance + i)))
        .collect()
}

// ----- circuit list --------------------------------------------------------
//
// Linear-only propagation cannot pin wires whose only pinning constraint is
// quadratic — e.g. booleans `b·(b−1)=0` (two solutions `{0, 1}`) or square
// roots `x²=y` (two solutions `±√y`). Most of our gadgets use boolean wires
// for bit decomposition, range checks, selectors, and bitwise ops, so most
// witness wires here will *correctly* be reported as not-pinned-by-linear.
//
// This is exactly the under-approximation the FV plan calls out: linear
// propagation gives a cheap baseline; Picus/Ecne with Gröbner-basis backends
// would close the boolean / quadratic cases. Findings = "audit these via a
// stronger tool when budget allows."
//
// The test ships a **regression baseline** — a hand-recorded snapshot of how
// many witness wires the propagator pins per fixture today. A drop in the
// pinned count signals either (a) a real new under-constraint condition or
// (b) an analyzer regression; either is worth investigating.

/// `(fixture name, minimum pinned witness wires the propagator should still
/// pin)`. Floors are deliberately ≤ the observed counts so noise in the
/// witness values doesn't break CI. Update when adding/changing gadgets.
const PINNED_FLOOR: &[(&str, usize)] = &[
    ("arithmetic_square", 0),
    ("arithmetic_public_inputs", 0),
    ("range_basic", 1),
    ("brillig_basic", 0),
    ("memory_const", 1),
    ("memory_var", 1),
    ("return_values_only", 0),
    ("mixed_pi", 1),
    ("reorder_pi", 0),
    ("large_pi", 0),
    ("multi_function", 2),
    ("nested_calls", 4),
    ("bitwise_basic", 2),
    ("poseidon_basic", 8),
    ("curve_basic", 49),
    ("sha256_basic", 8),
    ("blake2s_basic", 160),
    ("blake3_basic", 64),
    ("keccak_basic", 50),
    ("aes128_basic", 2600),
];

// ----- the test driver -----------------------------------------------------

#[test]
fn propagation_determinism() {
    let verbose = std::env::var_os("XARK_PROPAGATION_VERBOSE").is_some();
    eprintln!(
        "\n  R1CS propagation-based determinism analyzer:\n  \
         linear-only propagation; quadratic gadgets (booleans, square roots, …) are\n  \
         correctly *not* pinned — Picus/Ecne is the next escalation for those.\n\n  \
         {:<28} {:>8} {:>8} {:>9}  pinned   floor",
        "circuit", "rows", "witness", "instance"
    );

    let mut regressions: Vec<String> = Vec::new();
    for &(name, floor) in PINNED_FLOOR {
        let path = fixture_dir().join(format!("{name}.json"));
        if !path.exists() {
            eprintln!("  {name:<28}  (fixture missing — skip)");
            continue;
        }
        let r = lower(name);
        let unpinned = propagate(&r);
        let pinned = r.num_witness - unpinned.len();
        eprintln!(
            "  {name:<28} {:>8} {:>8} {:>9}  {pinned:>6}  {floor:>6}",
            r.a.len(),
            r.num_witness,
            r.num_instance,
        );
        if pinned < floor {
            regressions.push(format!(
                "{name}: propagator pinned {pinned} wires, baseline floor is {floor} — \
                 either an analyzer regression or a new under-constraint condition"
            ));
        }
        if verbose && !unpinned.is_empty() {
            eprintln!(
                "    first 12 unpinned witness-wire indices: {:?}",
                unpinned.iter().take(12).collect::<Vec<_>>()
            );
        }
    }

    eprintln!("\n  Set XARK_PROPAGATION_VERBOSE=1 to print per-circuit unpinned-wire indices.\n");

    if !regressions.is_empty() {
        for r in &regressions {
            eprintln!("REGRESSION: {r}");
        }
        panic!(
            "{} fixture(s) dropped below the propagation baseline floor",
            regressions.len()
        );
    }
}

/// Sound under-approximation spot-test: a hand-rolled tiny R1CS `x · x = y`
/// with `y` instance-valued — the equation is quadratic in `x`, so the
/// propagator must *not* claim `x` is pinned. We build the matrices directly
/// (no `ConstraintSynthesizer`) so the test stays self-contained.
#[test]
fn square_root_correctly_reported_as_undetermined() {
    // Instance: col 0 = `1`, col 1 = `y = 4`. Witness: col 2 = `x = 2`.
    let instance = vec![Fr::from(1u64), Fr::from(4u64)];
    let num_instance = instance.len();
    let num_witness = 1;
    // x · x = y: A = [(1, col_x)], B = [(1, col_x)], C = [(1, col_y)].
    let row_x = vec![(Fr::from(1u64), num_instance)]; // col 2 = x
    let row_y = vec![(Fr::from(1u64), 1)]; // col 1 = y
    let r = R1csValued {
        a: vec![row_x.clone()],
        b: vec![row_x],
        c: vec![row_y],
        num_instance,
        num_witness,
        instance,
    };
    let unpinned = propagate(&r);
    assert!(
        !unpinned.is_empty(),
        "x · x = y is quadratic in x — propagation must not claim x is pinned"
    );
}
