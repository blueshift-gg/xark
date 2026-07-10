//! End-to-end integration tests driving the `xark` CLI (`build` + `prove`)
//! against the purpose-built circuit crates under `examples/`.
//!
//! `xark build <crate> --out <dir>` compiles a circuit crate (rustc-MIR →
//! xark-IR → R1CS) to `<dir>/{circuit,r1cs}.json`; `xark prove <dir> --inputs
//! k=v` solves the witness and produces + verifies a Groth16 proof in one shot.

mod common;
use common::{tempdir, xark_build, xark_check_input, xark_prove, xark_setup};

#[test]
fn arithmetic_square_build_prove_verify() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");

    let (ok, err) = xark_build("arithmetic_square", &out, &target);
    assert!(ok, "build failed: {err}");
    assert!(
        out.join("r1cs.json").exists() && out.join("circuit.json").exists(),
        "build produced no JSON"
    );

    let (ok, err) = xark_setup(&out);
    assert!(ok, "setup failed: {err}");

    // x = 3, y = 9 satisfies `x * x == y`.
    let (ok, err) = xark_prove(&out, &[("x", "3"), ("y", "9")]);
    assert!(ok, "prove/verify failed: {err}");
    assert!(
        err.contains("Proof produced and self-checked"),
        "unexpected prove output: {err}"
    );
}

#[test]
fn wrong_public_output_fails_to_verify() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");
    assert!(
        xark_build("arithmetic_square", &out, &target).0,
        "build failed"
    );

    let (ok, err) = xark_setup(&out);
    assert!(ok, "setup failed: {err}");

    // y = 10 does NOT equal x*x = 9: the witness fails `solve_and_check`, so
    // `xark prove` exits non-zero rather than emitting a bogus proof.
    let (ok, err) = xark_prove(&out, &[("x", "3"), ("y", "10")]);
    assert!(
        !ok,
        "prove unexpectedly succeeded on an unsatisfied witness: {err}"
    );
}

#[test]
fn range_basic_build_prove_verify() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");
    let (ok, err) = xark_build("range_basic", &out, &target);
    assert!(ok, "build failed: {err}");

    let (ok, err) = xark_setup(&out);
    assert!(ok, "setup failed: {err}");

    // x = 200 is an in-range u8; out = 200.
    let (ok, err) = xark_prove(&out, &[("x", "200"), ("out", "200")]);
    assert!(ok, "prove/verify failed: {err}");
    assert!(
        err.contains("Proof produced and self-checked"),
        "unexpected prove output: {err}"
    );
}

/// **Under-constrained soundness gate.** `examples/underconstrained_bit` builds
/// and *solves* fine, but its hint `b` is pinned only boolean (`b*b == b`) — a
/// two-valued variable the witness-based `solver::analyze_underconstrained`
/// flags. `xark prove` must refuse to prove it (a proof would be unsound),
/// emitting the under-constraint error rather than a bogus proof.
#[test]
fn underconstrained_circuit_is_rejected_by_prove() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");

    // The circuit is well-formed Rust and passes the structural build-time pin
    // check (the booleanity constraint *references* `b`), so build succeeds.
    let (ok, err) = xark_build("underconstrained_bit", &out, &target);
    assert!(ok, "build failed: {err}");

    let (ok, err) = xark_setup(&out);
    assert!(ok, "setup failed: {err}");

    // x = 4 (even → bit 0 = 0), out = 4: the witness solves and satisfies every
    // constraint, so only the *witness-based* analyzer can catch the hole.
    let (ok, err) = xark_prove(&out, &[("x", "4"), ("out", "4")]);
    assert!(
        !ok,
        "prove unexpectedly succeeded on an under-constrained circuit: {err}"
    );
    assert!(
        err.contains("under-constrained"),
        "expected an under-constraint rejection, got: {err}"
    );

    // Properly-pinned sibling: `examples/inverse` pins its hint with `x*w == 1`,
    // so the analyzer is clean and it proves without complaint.
    let out2 = tmp.path().join("out-inverse");
    let target2 = tmp.path().join("target-inverse");
    let (ok, err) = xark_build("inverse", &out2, &target2);
    assert!(ok, "build failed: {err}");
    let (ok, err) = xark_setup(&out2);
    assert!(ok, "setup failed: {err}");
    // x = 2, x_inv = 1/2 mod r = (r+1)/2.
    let half = "10944121435919637611123202872628637544274182200208017171849102093287904247809";
    let (ok, err) = xark_prove(&out2, &[("x", "2"), ("x_inv", half)]);
    assert!(ok, "pinned sibling failed to prove: {err}");
    assert!(
        err.contains("Proof produced and self-checked"),
        "unexpected prove output: {err}"
    );
}

/// **`xark check --inputs` opt-in soundness check — rejection.** The same
/// witness-based analyzer `prove` runs, but *without* the expensive
/// `setup`+`prove`: `check --inputs` on the two-valued `underconstrained_bit`
/// fixture must fail with the under-constraint diagnostic, and must NOT have
/// produced any proving key / proof (it never runs `setup`).
#[test]
fn check_input_rejects_underconstrained_circuit() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");

    let (ok, combined) = xark_check_input(
        "underconstrained_bit",
        &out,
        &target,
        &[("x", "4"), ("out", "4")],
    );
    assert!(
        !ok,
        "check --inputs unexpectedly succeeded on an under-constrained circuit: {combined}"
    );
    assert!(
        combined.contains("under-constrained"),
        "expected an under-constraint rejection, got: {combined}"
    );
    // `check` builds only — it never runs `setup`, so no proving key exists.
    assert!(
        !out.join("pk.bin").exists(),
        "check --inputs must not run setup, but pk.bin was produced"
    );
}

/// **`xark check --inputs` opt-in soundness check — success.** On a properly
/// constrained circuit (`cube`: `secret^3 == result`) `check --inputs` builds +
/// solves + analyzes and reports the circuit sound, again without running
/// `setup`/`prove` (no `pk.bin`).
#[test]
fn check_input_accepts_sound_circuit() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");

    // secret = 2, result = 8 satisfies `secret^3 == result`.
    let (ok, combined) =
        xark_check_input("cube", &out, &target, &[("secret", "2"), ("result", "8")]);
    assert!(ok, "check --inputs failed on a sound circuit: {combined}");
    assert!(
        combined.contains("circuit sound"),
        "expected the positive soundness line, got: {combined}"
    );
    // No proving key — `check` never runs `setup`.
    assert!(
        !out.join("pk.bin").exists(),
        "check --inputs must not run setup, but pk.bin was produced"
    );
}
