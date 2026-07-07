//! Integration tests for cross-function circuits (`multi_function` /
//! `nested_calls`), driven through the `xark` CLI (`build` + `prove`).
//!
//! The circuit crates use plain Rust helper functions (`#[inline(never)] fn
//! square`, `square_plus_one`); the xark compiler inlines their MIR across
//! function boundaries, so `main`'s constraints incorporate the helper bodies.
//! These tests confirm the whole build → solve → Groth16 prove/verify pipeline
//! works for multi-function circuits.

mod common;
use common::{tempdir, xark_build, xark_prove};

#[test]
fn multi_function_build_prove_verify() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");
    let (ok, err) = xark_build("multi_function", &out, &target);
    assert!(ok, "build failed: {err}");

    // square(x) == y  with x = 6, y = 36.
    let (ok, err) = xark_prove(&out, &[("x", "6"), ("y", "36")]);
    assert!(ok, "prove/verify failed: {err}");
    assert!(err.contains("proof verified"), "unexpected prove output: {err}");
}

#[test]
fn nested_calls_build_prove_verify() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");
    let (ok, err) = xark_build("nested_calls", &out, &target);
    assert!(ok, "build failed: {err}");

    // square_plus_one(x) = square(x) + 1 == y  with x = 6, y = 37.
    let (ok, err) = xark_prove(&out, &[("x", "6"), ("y", "37")]);
    assert!(ok, "prove/verify failed: {err}");
    assert!(err.contains("proof verified"), "unexpected prove output: {err}");
}
