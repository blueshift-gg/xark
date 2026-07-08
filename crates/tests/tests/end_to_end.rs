//! End-to-end integration tests driving the `xark` CLI (`build` + `prove`)
//! against the purpose-built circuit crates under `examples/`.
//!
//! `xark build <crate> --out <dir>` compiles a circuit crate (rustc-MIR →
//! xark-IR → R1CS) to `<dir>/{circuit,r1cs}.json`; `xark prove <dir> --input
//! k=v` solves the witness and produces + verifies a Groth16 proof in one shot.

mod common;
use common::{tempdir, xark_build, xark_prove, xark_setup};

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
