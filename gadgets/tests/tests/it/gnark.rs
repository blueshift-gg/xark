//! `--backend gnark`: a xark circuit set up, proved and verified by gnark, from
//! the rows and the witness xark exports for it in iden3's formats.
//!
//! What xark does on its own runs with the rest of the suite: the two files
//! (`xark export --format iden3`), read back here and checked row by row, and
//! everything the backend decides before it needs its Go helper. The tests that
//! run gnark are ignored by default, since the helper is built on first use
//! (needs `go`, and the network for gnark's modules); slow.yml runs them.

use crate::common::{tempdir, xark_bin, xark_build};
use ark_bn254::Fr;
use ark_ff::{BigInteger, PrimeField};
use std::path::{Path, PathBuf};
use std::process::Command;
use xark_groth16::ConstraintSource;

/// `xark <args>` under `env` (a `None` unsets the variable): its exit code and
/// its output.
fn xark(args: &[&str], env: &[(&str, Option<&str>)]) -> (Option<i32>, String) {
    let mut cmd = Command::new(xark_bin());
    cmd.args(args);
    for (name, value) in env {
        match value {
            Some(v) => cmd.env(name, v),
            None => cmd.env_remove(name),
        };
    }
    let out = cmd.output().expect("invoke xark");
    (
        out.status.code(),
        String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr),
    )
}

/// `xark <command> <out> --backend gnark <rest>`: success, and its output.
fn gnark(command: &str, out: &Path, rest: &[&str]) -> (bool, String) {
    let (code, log) = gnark_code(command, out, rest);
    (code == Some(0), log)
}

fn gnark_code(command: &str, out: &Path, rest: &[&str]) -> (Option<i32>, String) {
    let mut args = vec![command, out.to_str().unwrap(), "--backend", "gnark"];
    args.extend(rest);
    xark(&args, &[])
}

/// Build `examples/<name>` into a directory of its own.
fn built(name: &str, tmp: &Path) -> PathBuf {
    let out = tmp.join(name);
    let (ok, err) = xark_build(name, &out, &tmp.join("target"));
    assert!(ok, "build {name}: {err}");
    out
}

/// A little-endian reader over one of iden3's files.
struct Bytes<'a>(&'a [u8]);

impl Bytes<'_> {
    fn take(&mut self, n: usize) -> &[u8] {
        let (head, rest) = self.0.split_at(n);
        self.0 = rest;
        head
    }
    fn u32(&mut self) -> u32 {
        u32::from_le_bytes(self.take(4).try_into().unwrap())
    }
    fn u64(&mut self) -> u64 {
        u64::from_le_bytes(self.take(8).try_into().unwrap())
    }
    fn fr(&mut self) -> Fr {
        let bytes = self.take(32);
        let v = Fr::from_le_bytes_mod_order(bytes);
        assert_eq!(v.into_bigint().to_bytes_le(), bytes, "a canonical element");
        v
    }
    /// A header's field: 32-byte elements of the BN254 scalar field.
    fn field(&mut self) {
        assert_eq!(self.u32(), 32, "field element size");
        assert_eq!(self.take(32), Fr::MODULUS.to_bytes_le(), "the prime");
    }
}

/// A row's three linear combinations, each as `(wire, coefficient)` terms.
type Row = [Vec<(u32, Fr)>; 3];

/// An iden3 `.r1cs` file as `xark` writes it, per the format's specification
/// (<https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md>):
/// `(wires, public inputs, rows)`. Every section must be as long as it says.
fn read_r1cs(path: &Path) -> (u32, u32, Vec<Row>) {
    let file = std::fs::read(path).unwrap();
    let mut r = Bytes(&file);
    assert_eq!(r.take(4), b"r1cs");
    assert_eq!((r.u32(), r.u32()), (1, 3), "version, sections");

    assert_eq!(
        (r.u32(), r.u64()),
        (1, 64),
        "the header section and its size"
    );
    r.field();
    let (wires, outputs, public, private) = (r.u32(), r.u32(), r.u32(), r.u32());
    assert_eq!((outputs, private), (0, 0));
    assert_eq!(r.u64(), u64::from(wires), "labels");
    let count = r.u32();

    assert_eq!(r.u32(), 2, "the constraint section");
    let size = r.u64() as usize;
    let after = r.0.len() - size;
    let rows = (0..count)
        .map(|_| {
            [(); 3].map(|()| {
                (0..r.u32())
                    .map(|_| {
                        let wire = r.u32();
                        assert!(wire < wires, "a term on wire {wire} of {wires}");
                        (wire, r.fr())
                    })
                    .collect()
            })
        })
        .collect();
    assert_eq!(r.0.len(), after, "the constraint section's size");

    assert_eq!(
        (r.u32(), r.u64()),
        (3, 8 * u64::from(wires)),
        "the label map"
    );
    for i in 0..u64::from(wires) {
        assert_eq!(r.u64(), i);
    }
    assert!(r.0.is_empty(), "bytes after the last section");
    (wires, public, rows)
}

/// An iden3 `.wtns` file as `xark` writes it: the value of every wire.
fn read_wtns(path: &Path) -> Vec<Fr> {
    let file = std::fs::read(path).unwrap();
    let mut r = Bytes(&file);
    assert_eq!(r.take(4), b"wtns");
    assert_eq!((r.u32(), r.u32()), (2, 2), "version, sections");
    assert_eq!(
        (r.u32(), r.u64()),
        (1, 40),
        "the header section and its size"
    );
    r.field();
    let n = r.u32();
    assert_eq!((r.u32(), r.u64()), (2, 32 * u64::from(n)), "the values");
    let z = (0..n).map(|_| r.fr()).collect();
    assert!(r.0.is_empty(), "bytes after the last section");
    z
}

/// The first row `z` doesn't satisfy: `(A·z)(B·z) = C·z` for each.
fn unsatisfied(rows: &[Row], z: &[Fr]) -> Option<usize> {
    let dot = |lc: &[(u32, Fr)]| lc.iter().map(|(w, c)| z[*w as usize] * c).sum::<Fr>();
    rows.iter().position(|[a, b, c]| dot(a) * dot(b) != dot(c))
}

#[test]
fn iden3_export_is_the_keyed_rows_and_a_witness_that_satisfies_them() {
    let tmp = tempdir();
    let out = built("cube", tmp.path());
    let inputs = r#"{"secret": 3, "result": 27}"#;
    let xbc = std::fs::read(out.join("circuit.xbc")).unwrap();
    let src = xark_groth16::BytecodeSource::new(&xbc).unwrap();

    // Both forms a key is made for: the template-reduced rows, which are the
    // bytecode's own, and the minimized ones (`auto`, for a circuit this small).
    for form in ["reduced", "auto"] {
        let dir = tmp.path().join(form);
        let (code, log) = xark(
            &[
                "export",
                out.to_str().unwrap(),
                "--format",
                "iden3",
                "--r1cs-form",
                form,
                "--inputs",
                inputs,
                "--out",
                dir.to_str().unwrap(),
            ],
            &[],
        );
        assert_eq!(code, Some(0), "export {form}: {log}");
        let (wires, public, rows) = read_r1cs(&dir.join("circuit.r1cs"));
        let z = read_wtns(&dir.join("witness.wtns"));
        assert_eq!(public, 1, "{form}: cube's one public input");
        if form == "reduced" {
            assert_eq!(wires as usize, src.layout().num_vars());
            assert_eq!(rows.len(), src.num_constraints());
        } else {
            assert!(rows.len() <= src.num_constraints() && !rows.is_empty());
        }

        // The witness is a value for every wire, the constant one first and the
        // public input after it, and it satisfies every row.
        assert_eq!(z.len(), wires as usize, "{form}");
        assert_eq!((z[0], z[1]), (Fr::from(1u64), Fr::from(27u64)), "{form}");
        assert_eq!(unsatisfied(&rows, &z), None, "{form}");
        // And the rows are a constraint on it: another public input fails one.
        let mut wrong = z.clone();
        wrong[1] += Fr::from(1u64);
        assert!(unsatisfied(&rows, &wrong).is_some(), "{form}: 3^3 = 28");

        // The witness holds the private input: its owner's alone.
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = std::fs::metadata(dir.join("witness.wtns")).unwrap();
            assert_eq!(mode.permissions().mode() & 0o777, 0o600, "{form}");
        }
    }

    // Without inputs there is no witness to write.
    let dir = tmp.path().join("rows");
    let (code, log) = xark(
        &[
            "export",
            out.to_str().unwrap(),
            "--format",
            "iden3",
            "--out",
            dir.to_str().unwrap(),
        ],
        &[],
    );
    assert_eq!(code, Some(0), "export: {log}");
    assert!(dir.join("circuit.r1cs").is_file() && !dir.join("witness.wtns").exists());
}

#[test]
fn gnark_backend_decides_what_it_can_without_its_helper() {
    let tmp = tempdir();
    let nowhere = tmp.path().join("nowhere");
    let nowhere = nowhere.to_str().unwrap();

    // The other backend's flags are refused before anything is read or built.
    for (args, names) in [
        (
            vec![
                "setup",
                nowhere,
                "--backend",
                "gnark",
                "--deterministic-rng",
                "1",
            ],
            "--backend gnark",
        ),
        (
            vec!["prove", nowhere, "--backend", "gnark", "--cache"],
            "--backend gnark",
        ),
        (
            vec!["verify", nowhere, "--backend", "gnark", "--inputs", "{}"],
            "--backend gnark",
        ),
        (vec!["prove", nowhere, "--keep-witness"], "--keep-witness"),
    ] {
        let (code, log) = xark(&args, &[]);
        assert!(code != Some(0) && log.contains(names), "{args:?}: {log}");
    }

    let out = built("cube", tmp.path());
    let dir = out.to_str().unwrap();

    // No cache directory to build the helper into: refused, not built in the
    // temporary directory, where another user could have put a program first.
    let (code, log) = xark(
        &["setup", dir, "--backend", "gnark"],
        &[
            ("XARK_GNARK", None),
            ("XDG_CACHE_HOME", None),
            ("HOME", None),
        ],
    );
    assert!(
        code != Some(0) && log.contains("XDG_CACHE_HOME"),
        "setup: {log}"
    );

    // A helper that can't run is an error (exit code 1), not a proof that failed
    // to verify (exit code 2).
    let files = ["vk.bin", "proof.bin", "public_witness.bin"].map(|f| {
        let path = tmp.path().join(f);
        std::fs::write(&path, b"").unwrap();
        path
    });
    let verify = [
        "verify",
        dir,
        "--backend",
        "gnark",
        "--verifying-key",
        files[0].to_str().unwrap(),
        "--proof",
        files[1].to_str().unwrap(),
        "--public-inputs",
        files[2].to_str().unwrap(),
    ];
    let missing = tmp.path().join("no-such-helper");
    let (code, log) = xark(&verify, &[("XARK_GNARK", missing.to_str())]);
    assert!(
        code == Some(1) && !log.contains("verification failed"),
        "verify: {code:?} {log}"
    );

    // Nor is a helper built from another version of xark believed, whatever it
    // exits with: it doesn't say this version's protocol.
    #[cfg(unix)]
    for exit in [0, 2] {
        use std::os::unix::fs::PermissionsExt;
        let old = tmp.path().join(format!("old-helper-{exit}"));
        std::fs::write(&old, format!("#!/bin/sh\nexit {exit}\n")).unwrap();
        std::fs::set_permissions(&old, std::fs::Permissions::from_mode(0o755)).unwrap();
        let (code, log) = xark(&verify, &[("XARK_GNARK", old.to_str())]);
        assert!(
            code == Some(1) && log.contains("not this xark's gnark helper"),
            "verify with a helper exiting {exit}: {code:?} {log}"
        );
    }
}

#[test]
#[ignore = "builds the Go helper: needs go and the network"]
fn gnark_proves_and_verifies_a_xark_circuit() {
    let tmp = tempdir();
    let out = built("cube", tmp.path());
    let inputs = r#"{"secret": 3, "result": 27}"#;

    // The first proof makes the key, as `xark prove` does.
    let (ok, log) = gnark("prove", &out, &["--inputs", inputs]);
    assert!(ok, "prove: {log}");
    for f in ["circuit.r1cs", "circuit.ccs", "pk.bin", "vk.bin"] {
        assert!(out.join("gnark").join(f).is_file(), "no gnark/{f}: {log}");
    }
    // The witness is gone once gnark has read it.
    assert!(!out.join("gnark/witness.wtns").exists(), "a witness left");
    let (ok, log) = gnark("verify", &out, &[]);
    assert!(ok && log.contains("Proof verified"), "verify: {log}");

    // Another statement of the same circuit, proved elsewhere: 2^3 = 8. Its
    // public inputs are not the first proof's, and gnark's verifier says so
    // (exit code 2, as the default backend's).
    let other = tmp.path().join("other");
    let (ok, log) = gnark(
        "prove",
        &out,
        &[
            "--inputs",
            r#"{"secret": 2, "result": 8}"#,
            "--out",
            other.to_str().unwrap(),
            "--keep-witness",
        ],
    );
    assert!(ok, "prove 2^3 = 8: {log}");
    // Kept on request, and its owner's alone.
    let kept = other.join("gnark/witness.wtns");
    assert!(kept.is_file(), "--keep-witness kept no witness: {log}");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = std::fs::metadata(&kept).unwrap().permissions().mode();
        assert_eq!(mode & 0o777, 0o600);
    }
    let wrong = other.join("gnark/public_witness.bin");
    let (code, log) = gnark_code(
        "verify",
        &out,
        &["--public-inputs", wrong.to_str().unwrap()],
    );
    assert!(
        code == Some(2) && log.contains("verification failed"),
        "3^3 = 27's proof against the public input 8: {code:?} {log}"
    );

    // A proof with a byte changed doesn't verify either (gnark may refuse to
    // read it at all, so only the outcome is asserted).
    let proof = out.join("gnark/proof.bin");
    let mut bytes = std::fs::read(&proof).unwrap();
    let tampered = tmp.path().join("tampered.bin");
    *bytes.last_mut().unwrap() ^= 1;
    std::fs::write(&tampered, &bytes).unwrap();
    let (ok, log) = gnark("verify", &out, &["--proof", tampered.to_str().unwrap()]);
    assert!(!ok, "a tampered proof verified: {log}");

    // A witness that doesn't satisfy the circuit gets no proof, the error names
    // the constraint in the source, and its witness isn't left behind.
    let (ok, log) = gnark(
        "prove",
        &out,
        &["--inputs", r#"{"secret": 3, "result": 28}"#],
    );
    assert!(!ok, "proved 3^3 = 28: {log}");
    assert!(log.contains("lib.rs"), "no source line in: {log}");
    assert!(!out.join("gnark/witness.wtns").exists(), "a witness left");
}

#[test]
#[ignore = "builds the Go helper: needs go and the network"]
fn gnark_key_is_for_the_circuit_it_was_made_from() {
    let tmp = tempdir();
    let out = built("cube", tmp.path());
    let inputs = r#"{"secret": 3, "result": 27}"#;

    // A key made elsewhere is named to `prove` and `verify`, as xark's own is.
    let keys = tmp.path().join("keys");
    let (ok, log) = gnark("setup", &out, &["--out", keys.to_str().unwrap()]);
    assert!(ok, "setup --out: {log}");
    let proofs = tmp.path().join("proofs");
    let (ok, log) = gnark(
        "prove",
        &out,
        &[
            "--inputs",
            inputs,
            "--proving-key",
            keys.join("gnark/pk.bin").to_str().unwrap(),
            "--out",
            proofs.to_str().unwrap(),
        ],
    );
    assert!(ok, "prove --proving-key: {log}");
    assert!(!out.join("gnark").exists(), "a second key was made: {log}");
    let (ok, log) = gnark(
        "verify",
        &out,
        &[
            "--verifying-key",
            keys.join("gnark/vk.bin").to_str().unwrap(),
            "--proof",
            proofs.join("gnark/proof.bin").to_str().unwrap(),
            "--public-inputs",
            proofs.join("gnark/public_witness.bin").to_str().unwrap(),
        ],
    );
    assert!(ok && log.contains("Proof verified"), "verify: {log}");

    let (ok, log) = gnark("setup", &out, &[]);
    assert!(ok, "setup: {log}");
    // Another circuit's build beside this key: refused, not proved wrongly.
    let other = built("poseidon2", tmp.path());
    std::fs::copy(other.join("circuit.xbc"), out.join("circuit.xbc")).unwrap();
    let (ok, log) = gnark("prove", &out, &["--inputs", inputs]);
    assert!(!ok && log.contains("different circuit"), "prove: {log}");
}
