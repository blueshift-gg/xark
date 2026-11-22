//! `--backend gnark`: a xark circuit set up, proved and verified by gnark, from
//! the rows and the witness xark exports for it. Ignored by default, since the
//! Go helper is built on first use (needs `go`, and the network for gnark's
//! modules); slow.yml runs it.

use crate::common::{run, tempdir, xark_build};
use std::path::Path;

/// `xark <command> <out> --backend gnark <rest>`: success, and its output.
fn gnark(command: &str, out: &Path, rest: &[&str]) -> (bool, String) {
    let mut args = vec![command, out.to_str().unwrap(), "--backend", "gnark"];
    args.extend(rest);
    let (ok, stdout, stderr) = run(&args);
    (ok, stdout + &stderr)
}

/// Build `examples/<name>` into a directory of its own.
fn built(name: &str, tmp: &Path) -> std::path::PathBuf {
    let out = tmp.join(name);
    let (ok, err) = xark_build(name, &out, &tmp.join("target"));
    assert!(ok, "build {name}: {err}");
    out
}

#[test]
#[ignore = "builds the Go helper: needs go and the network"]
fn gnark_proves_and_verifies_a_xark_circuit() {
    let tmp = tempdir();
    let out = built("cube", tmp.path());

    // The first proof makes the key, as `xark prove` does.
    let (ok, log) = gnark(
        "prove",
        &out,
        &["--inputs", r#"{"secret": 3, "result": 27}"#],
    );
    assert!(ok, "prove: {log}");
    for f in ["circuit.r1cs", "circuit.ccs", "pk.bin", "vk.bin"] {
        assert!(out.join("gnark").join(f).is_file(), "no gnark/{f}: {log}");
    }
    let (ok, log) = gnark("verify", &out, &[]);
    assert!(ok && log.contains("Proof verified"), "verify: {log}");

    // The same proof against other public inputs: poseidon2's, from its own run.
    let other = built("poseidon2", tmp.path());
    let inputs = r#"{"in0": 1, "in1": 2, "in2": 3,
        "out0": "4737982494702600552753609419126955242994596445692557044681458296415162795880",
        "out1": "9698155156890762076414037574068404457164720954413259397447872502075783415658",
        "out2": "18259628997120261506554896720810362547891614655348127750921457211768261324825"}"#;
    let (ok, log) = gnark("prove", &other, &["--inputs", inputs]);
    assert!(ok, "prove poseidon2: {log}");
    let wrong = other.join("gnark/public_witness.bin");
    let (ok, log) = gnark(
        "verify",
        &out,
        &["--public-inputs", wrong.to_str().unwrap()],
    );
    assert!(
        !ok,
        "a proof verified against another circuit's inputs: {log}"
    );

    // A witness that doesn't satisfy the circuit gets no proof, and the error
    // names the constraint in the source.
    let (ok, log) = gnark(
        "prove",
        &out,
        &["--inputs", r#"{"secret": 3, "result": 28}"#],
    );
    assert!(!ok, "proved 3^3 = 28: {log}");
    assert!(log.contains("lib.rs"), "no source line in: {log}");
}

#[test]
#[ignore = "builds the Go helper: needs go and the network"]
fn gnark_key_is_for_the_circuit_it_was_made_from() {
    let tmp = tempdir();
    let out = built("cube", tmp.path());
    let (ok, log) = gnark("setup", &out, &[]);
    assert!(ok, "setup: {log}");
    // Another circuit's build beside this key: refused, not proved wrongly.
    let other = built("poseidon2", tmp.path());
    std::fs::copy(other.join("circuit.xbc"), out.join("circuit.xbc")).unwrap();
    let (ok, log) = gnark(
        "prove",
        &out,
        &["--inputs", r#"{"secret": 3, "result": 27}"#],
    );
    assert!(!ok && log.contains("different circuit"), "prove: {log}");

    // xark's own setup flags are not gnark's.
    let (ok, log) = gnark("setup", &out, &["--deterministic-rng", "1"]);
    assert!(!ok && log.contains("--backend gnark"), "setup: {log}");
}
