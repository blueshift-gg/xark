//! Proving from Rust without the CLI: `xark_prover::circuit_at(dir).prove(inputs)`
//! with the key `xark setup` wrote returns the same bytes `xark prove` writes, and
//! `xark verify` accepts them.

mod common;

use std::process::Command;

use common::{tempdir, xark_bin, xark_build};

struct CubeInputs {
    secret: u64,
    result: u64,
}

impl xark_prover::ProveInputs for CubeInputs {
    fn into_inputs(self) -> Vec<(String, xark_prover::Fr)> {
        vec![
            ("secret".into(), self.secret.into()),
            ("result".into(), self.result.into()),
        ]
    }
}

#[test]
fn rust_prove_matches_the_cli() {
    let tmp = tempdir();
    let (out, target) = (tmp.path().join("cube"), tmp.path().join("target"));
    let (ok, log) = xark_build("cube", &out, &target);
    assert!(ok, "xark build: {log}");
    let o = Command::new(xark_bin())
        .args(["setup", out.to_str().unwrap(), "--insecure-dev-mode"])
        .output()
        .expect("spawn xark setup");
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));

    let circuit = xark_prover::circuit_at(&out);
    let proof = circuit
        .prove(CubeInputs {
            secret: 3,
            result: 27,
        })
        .expect("3³ = 27 proves");
    // `public_inputs.bin`: an 8-byte little-endian count, then 27 as 32 bytes LE.
    let mut want = vec![1, 0, 0, 0, 0, 0, 0, 0, 27];
    want.resize(8 + 32, 0);
    assert_eq!(proof.public_inputs, want);

    let (p, pi) = (
        tmp.path().join("proof.bin"),
        tmp.path().join("public_inputs.bin"),
    );
    std::fs::write(&p, &proof.proof).unwrap();
    std::fs::write(&pi, &proof.public_inputs).unwrap();
    let o = Command::new(xark_bin())
        .args(["verify", out.to_str().unwrap(), "--proof"])
        .arg(&p)
        .arg("--public-inputs")
        .arg(&pi)
        .output()
        .expect("spawn xark verify");
    let text = String::from_utf8_lossy(&o.stdout);
    assert!(o.status.success() && text.contains("verified"), "{text}");

    let err = circuit
        .prove(CubeInputs {
            secret: 3,
            result: 28,
        })
        .expect_err("3³ ≠ 28");
    assert!(!err.to_string().is_empty());
    let err = circuit
        .prove_with_key(
            tmp.path().join("missing.bin"),
            CubeInputs {
                secret: 3,
                result: 27,
            },
        )
        .expect_err("no key");
    assert!(err.to_string().contains("xark setup"), "{err}");
}
