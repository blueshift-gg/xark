//! End-to-end integration tests driving the `xark` CLI (`build` + `prove`)
//! against the purpose-built circuit crates under `examples/`.
//!
//! `xark build <crate> --out <dir>` compiles a circuit crate (wasm32 →
//! xark-IR → R1CS) to the self-contained `<dir>/circuit.xbc`; `xark prove <dir>
//! --inputs '{...}'` solves the witness and produces + verifies a Groth16 proof
//! in one shot.

use crate::common::{
    run, tempdir, xark_build, xark_check_input, xark_prove, xark_setup, xark_setup_opts,
};

#[test]
fn arithmetic_square_build_prove_verify() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");

    let (ok, err) = xark_build("arithmetic_square", &out, &target);
    assert!(ok, "build failed: {err}");
    // A default build writes only the self-contained `circuit.xbc` (the R1CS +
    // witness-gen); `r1cs.json`/`circuit.json` are `--emit-json`-only now.
    assert!(
        out.join("circuit.xbc").exists(),
        "build produced no circuit.xbc"
    );
    assert!(
        !out.join("r1cs.json").exists(),
        "default build should not emit r1cs.json (it's --emit-json only)"
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

/// A **compressed** proving key (`xark setup`'s default; the other tests' keys are
/// uncompressed, for speed) must prove and verify — `xark prove` auto-detects the
/// key's compression from its header.
#[test]
fn compressed_key_proves_and_verifies() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");
    assert!(
        xark_build("arithmetic_square", &out, &target).0,
        "build failed"
    );
    let (ok, err) = xark_setup_opts(&out, false);
    assert!(ok, "compressed setup failed: {err}");

    let (ok, err) = xark_prove(&out, &[("x", "3"), ("y", "9")]);
    assert!(ok, "prove on compressed key failed: {err}");
    // A wrong output is still rejected.
    let (bad, _) = xark_prove(&out, &[("x", "3"), ("y", "10")]);
    assert!(!bad, "compressed key must reject a wrong witness");
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

/// A public input in no constraint, `bind`ed (a recipient only the verifier
/// supplies, as its two 16-byte halves): the proof verifies only with the address
/// it was made for.
#[test]
fn a_bound_public_input_binds_the_proof() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");
    let (ok, err) = xark_build("bound_recipient", &out, &target);
    assert!(ok, "build failed: {err}");
    let (ok, err) = xark_setup(&out);
    assert!(ok, "setup failed: {err}");
    // An address above p, so neither half may be reduced on the way in.
    let alice = r#"["0xf1e2d3c4b5a69788796a5b4c3d2e1f00", "0x00112233445566778899aabbccddeeff"]"#;
    let inputs = format!(r#"{{"x": "3", "y": "9", "recipient": {alice}}}"#);
    let (ok, stdout, stderr) = run(&["prove", out.to_str().unwrap(), "--inputs", &inputs]);
    assert!(ok, "prove failed: {stdout}{stderr}");
    let verify = |recipient: &str| {
        let inputs = format!(r#"{{"y": "9", "recipient": {recipient}}}"#);
        run(&["verify", out.to_str().unwrap(), "--inputs", &inputs])
    };
    let (ok, stdout, stderr) = verify(alice);
    assert!(ok, "{stdout}{stderr}");
    for other in [
        // One bit different.
        r#"["0xf1e2d3c4b5a69788796a5b4c3d2e1f00", "0x00112233445566778899aabbccddeefe"]"#,
        // The halves swapped.
        r#"["0x00112233445566778899aabbccddeeff", "0xf1e2d3c4b5a69788796a5b4c3d2e1f00"]"#,
    ] {
        let (ok, stdout, stderr) = verify(other);
        assert!(!ok, "recipient {other} verified: {stdout}{stderr}");
    }
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

/// **Soundness is checked by the circuit's tests, not by `xark prove`.**
/// `examples/underconstrained_bit` builds and *solves* fine, but its hint `b` is
/// pinned only boolean (`b*b == b`) — a two-valued variable the witness-based
/// `solver::analyze_underconstrained` flags. `Circuit::check` (what a circuit's
/// tests and its generated validator call) rejects it; `xark prove` only solves,
/// proves and self-verifies, so it proves it.
#[test]
fn soundness_is_checked_by_tests_not_prove() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");

    // The circuit is well-formed Rust and passes the structural build-time pin
    // check (the booleanity constraint *references* `b`), so build succeeds.
    let (ok, err) = xark_build("underconstrained_bit", &out, &target);
    assert!(ok, "build failed: {err}");

    // x = 4 (even → bit 0 = 0), out = 4: the witness solves and satisfies every
    // constraint, so only the *witness-based* analyzer can catch the hole.
    let inputs = || Named(vec![("x", 4), ("out", 4)]);
    let circuit = xark_prover::circuit_at(&out);
    let err = circuit
        .check(inputs())
        .expect_err("check passed an under-constrained circuit");
    assert!(err.to_string().contains("under-constrained"), "{err}");
    circuit
        .check_satisfied(inputs())
        .expect("the witness satisfies the circuit");

    let (ok, err) = xark_setup(&out);
    assert!(ok, "setup failed: {err}");
    let (ok, err) = xark_prove(&out, &[("x", "4"), ("out", "4")]);
    assert!(ok, "prove ran a soundness check: {err}");

    // Properly-pinned sibling: `examples/inverse` pins its hint with `x*w == 1`,
    // so `check` passes.
    let out2 = tmp.path().join("out-inverse");
    let target2 = tmp.path().join("target-inverse");
    let (ok, err) = xark_build("inverse", &out2, &target2);
    assert!(ok, "build failed: {err}");
    // x = 2, x_inv = 1/2 mod r = (r+1)/2.
    let half = "10944121435919637611123202872628637544274182200208017171849102093287904247809";
    let half = xark_prover::fr_from_decimal(half);
    xark_prover::circuit_at(&out2)
        .check(NamedFr(vec![("x", 2u64.into()), ("x_inv", half)]))
        .expect("a pinned circuit passes check");
}

struct Named(Vec<(&'static str, u64)>);

impl xark_prover::ProveInputs for Named {
    fn into_inputs(self) -> Vec<(String, xark_prover::Fr)> {
        self.0
            .into_iter()
            .map(|(n, v)| (n.into(), v.into()))
            .collect()
    }
}

struct NamedFr(Vec<(&'static str, xark_prover::Fr)>);

impl xark_prover::ProveInputs for NamedFr {
    fn into_inputs(self) -> Vec<(String, xark_prover::Fr)> {
        self.0.into_iter().map(|(n, v)| (n.into(), v)).collect()
    }
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
