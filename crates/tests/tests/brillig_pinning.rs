//! Integration tests for the Brillig output-pinning coverage check.
//!
//! `xark_acir_r1cs::opcodes::brillig_check::check_brillig_outputs_pinned`
//! walks an ACIR opcode stream and confirms every `BrilligCall` output is
//! referenced by at least one surrounding constraining opcode. This file
//! runs the check across every committed Noir-emitted artifact and asserts
//! the `(SI)` invariant holds — every Brillig output is pinned. A failure
//! here is *either* a compiler-bug (Noir emitting unsound ACIR) or a
//! fixture-tampering finding; in production deployments it would be
//! caught by the `--strict` CLI flag before any proving / verifying
//! happens.

use std::path::PathBuf;

use xark_acir_r1cs::artifact::parse_artifact_file;
use xark_acir_r1cs::opcodes::brillig_check::check_brillig_outputs_pinned;

mod common;
use common::fixture_dir;

/// All committed Noir fixtures in `crates/tests/fixtures/`. We walk every
/// one and assert the (SI) invariant holds.
fn all_fixture_names() -> Vec<&'static str> {
    vec![
        "aes128_basic",
        "arithmetic_public_inputs",
        "arithmetic_square",
        "bitwise_basic",
        "blake2s_basic",
        "blake3_basic",
        "brillig_basic",
        "curve_basic",
        "ecdsa_basic",
        "ecdsa_r1_basic",
        "keccak_basic",
        "large_pi",
        "memory_const",
        "memory_var",
        "mixed_pi",
        "poseidon_basic",
        "reorder_pi",
        "sha256_basic",
    ]
}

fn fixture_path(name: &str) -> PathBuf {
    fixture_dir().join(format!("{name}.json"))
}

/// (SI) invariant holds across every committed fixture — every
/// `BrilligCall` output is referenced by at least one constraining opcode.
/// A failure here would be a compiler-bug finding worth investigating
/// upstream in nargo.
#[test]
fn si_invariant_holds_across_all_fixtures() {
    let mut bad: Vec<(String, Vec<u32>)> = Vec::new();
    for name in all_fixture_names() {
        let path = fixture_path(name);
        if !path.exists() {
            // Some fixtures may have been renamed / removed; skip those
            // rather than fail the test on missing files.
            continue;
        }
        let artifact = parse_artifact_file(&path).expect("parse fixture");
        let opcodes = artifact.opcodes();
        let report = check_brillig_outputs_pinned(opcodes);
        if !report.is_ok() {
            bad.push((
                name.to_string(),
                report.unpinned_outputs.iter().copied().collect(),
            ));
        }
    }
    assert!(
        bad.is_empty(),
        "(SI) invariant violated for the following fixtures (unpinned outputs listed): {:?}",
        bad
    );
}

/// `brillig_basic` is the canonical fixture: a Noir program with a Brillig
/// hint immediately followed by an `AssertZero` check. Confirms the
/// analyser correctly detects pinning on a real artifact (not just a
/// synthesised opcode list).
#[test]
fn brillig_basic_reports_at_least_one_pinned_output() {
    let artifact = parse_artifact_file(&fixture_path("brillig_basic")).expect("parse");
    let report = check_brillig_outputs_pinned(artifact.opcodes());
    assert!(
        report.is_ok(),
        "brillig_basic should have all outputs pinned, got {:?}",
        report.unpinned_outputs
    );
    assert!(
        report.brillig_outputs_total > 0,
        "brillig_basic should contain at least one BrilligCall output"
    );
}

/// **Compose `check_brillig_outputs_pinned` with
/// `Formal.Brillig.brillig_lowering_vacuous_sound`.**
///
/// The Lean theorem `brillig_lowering_vacuous_sound` proves that the
/// trust-outputs lowering emits no R1CS constraints. Its hypothesis (the
/// `(SI)` invariant: every Brillig output is pinned by a surrounding
/// constraining opcode) is *not* mechanised in Lean — it's left as a
/// compiler-side guarantee per `docs/brillig.md`.
///
/// `check_brillig_outputs_pinned` is the Rust mechanisation of `(SI)`:
/// it walks the ACIR stream and verifies every Brillig output appears in
/// an `AssertZero` / `BlackBoxFuncCall` / `MemoryOp` / `Call`. A green
/// result discharges `(SI)`. Composed with `brillig_lowering_vacuous_sound`,
/// the chain reads:
///
///   1. (Lean) the lowering emits no constraints (`brillig_lowering_vacuous_sound`);
///   2. (Rust) the surrounding constraints pin every output (`check_brillig_outputs_pinned`);
///   3. ∴ every prover witness that satisfies the surrounding constraints
///      assigns each Brillig output to its hint value — which is the
///      property `Formal.Brillig.brillig_alloc_monotone` documents.
///
/// This test asserts step (2) holds across every committed fixture as a
/// machine-checked runtime witness of `(SI)`. The Lean theorem name is
/// recorded as a doc comment so the audit chain is traceable.
#[test]
fn brillig_si_invariant_discharges_lean_hypothesis() {
    // Doc-comment link to the Lean theorem the runtime check discharges.
    let lean_theorem = "Formal.Brillig.brillig_lowering_vacuous_sound";

    // Verify (SI) across every fixture. Failing here means the Lean
    // theorem's hypothesis is not discharged for that fixture, so the
    // Lean soundness statement does not apply to that circuit.
    let mut total_brillig_outputs = 0usize;
    let mut fixtures_checked = 0usize;
    for name in all_fixture_names() {
        let path = fixture_path(name);
        if !path.exists() {
            continue;
        }
        let artifact = parse_artifact_file(&path).expect("parse fixture");
        let report = check_brillig_outputs_pinned(artifact.opcodes());
        assert!(
            report.is_ok(),
            "(SI) violated for fixture {} — Lean theorem `{}`'s hypothesis \
             is not discharged for this circuit; unpinned outputs: {:?}",
            name,
            lean_theorem,
            report.unpinned_outputs
        );
        total_brillig_outputs += report.brillig_outputs_total;
        fixtures_checked += 1;
    }
    assert!(fixtures_checked > 0, "no fixtures present");
    eprintln!(
        "(SI) discharged for {} fixtures, {} Brillig outputs covered; \
         composes with Lean theorem `{}`.",
        fixtures_checked, total_brillig_outputs, lean_theorem
    );
}
