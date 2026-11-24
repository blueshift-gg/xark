//! `xark export --format iden3`: a circuit's keyed rows and a solved witness in
//! iden3's two files, read back here by the format's specification and checked
//! row by row. Another prover taking them is `benches/gnark/run.sh`, which
//! slow.yml runs: gnark sets up, proves and verifies from these files.

use crate::common::{tempdir, xark_bin, xark_build};
use ark_bn254::Fr;
use ark_ff::{BigInteger, PrimeField};
use std::path::{Path, PathBuf};
use std::process::Command;
use xark_groth16::ConstraintSource;

/// `xark <args>`: its exit code and its output.
fn xark(args: &[&str]) -> (Option<i32>, String) {
    let out = Command::new(xark_bin())
        .args(args)
        .output()
        .expect("invoke xark");
    (
        out.status.code(),
        String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr),
    )
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
        let (code, log) = xark(&[
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
        ]);
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
    let (code, log) = xark(&[
        "export",
        out.to_str().unwrap(),
        "--format",
        "iden3",
        "--out",
        dir.to_str().unwrap(),
    ]);
    assert_eq!(code, Some(0), "export: {log}");
    assert!(dir.join("circuit.r1cs").is_file() && !dir.join("witness.wtns").exists());
}

#[test]
fn iden3_and_solana_exports_keep_their_own_flags() {
    let tmp = tempdir();
    let nowhere = tmp.path().join("nowhere");
    let nowhere = nowhere.to_str().unwrap();
    // Refused before anything is read or built.
    for (args, names) in [
        (vec!["export", nowhere, "--inputs", "{}"], "--format iden3"),
        (
            vec!["export", nowhere, "--r1cs-form", "reduced"],
            "--format iden3",
        ),
        (
            vec!["export", nowhere, "--format", "iden3", "--crate-name", "x"],
            "--crate-name",
        ),
    ] {
        let (code, log) = xark(&args);
        assert!(code != Some(0) && log.contains(names), "{args:?}: {log}");
    }
}
