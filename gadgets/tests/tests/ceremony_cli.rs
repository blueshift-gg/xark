//! The trusted-setup ceremony through the CLI, end to end: `xark build` →
//! `xark ceremony init` (from the build, over a synthetic Powers-of-Tau
//! transcript) → two `contribute`s → `verify` → `finalize`, then `xark prove` /
//! `xark verify` with the ceremony's keys, and a wrong public input rejected.
//! The library-level ceremony (chain links, Schnorr proofs, tampering) is tested
//! in `crates/backend/src/ceremony.rs`. The transcript's toxic waste is known
//! here, so this checks the pipeline is correct, not that a ceremony is secret.

mod common;

use std::path::Path;
use std::process::Command;

use common::{build_valid_ptau, tempdir, xark_bin, xark_build};

fn xark(args: &[&str], dir: &Path) -> (bool, String) {
    let o = Command::new(xark_bin())
        .args(args)
        .current_dir(dir)
        .output()
        .expect("spawn xark");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&o.stdout),
        String::from_utf8_lossy(&o.stderr)
    );
    (o.status.success(), text)
}

#[test]
fn ceremony_keys_prove_and_verify() {
    let tmp = tempdir();
    let (out, target) = (tmp.path().join("cube"), tmp.path().join("target"));
    let (ok, log) = xark_build("cube", &out, &target);
    assert!(ok, "xark build: {log}");
    let ptau = tmp.path().join("test.ptau");
    std::fs::write(&ptau, build_valid_ptau(12)).unwrap();
    let cer = tmp.path().join("ceremony");
    let (cer_s, ptau_s) = (cer.to_str().unwrap(), ptau.to_str().unwrap());

    let step = |args: &[&str]| {
        let (ok, log) = xark(args, &out);
        assert!(ok, "xark {}: {log}", args.join(" "));
        log
    };
    step(&["ceremony", "init", "--ptau-file", ptau_s, "--out", cer_s]);
    // A second init over it is refused, not a reset.
    let (ok, log) = xark(
        &["ceremony", "init", "--ptau-file", ptau_s, "--out", cer_s],
        &out,
    );
    assert!(
        !ok && log.contains("already holds a ceremony") && log.contains("--force"),
        "{log}"
    );
    step(&[
        "ceremony",
        "contribute",
        "--ceremony-dir",
        cer_s,
        "--label",
        "alice",
    ]);
    step(&[
        "ceremony",
        "contribute",
        "--ceremony-dir",
        cer_s,
        "--label",
        "bob",
    ]);
    let log = step(&["ceremony", "verify", "--ceremony-dir", cer_s]);
    assert!(log.contains("alice") && log.contains("bob"), "{log}");
    let log = step(&["ceremony", "finalize", "--ceremony-dir", cer_s]);
    // The final verifying key's sha256 (a client pins its verifier to it): printed
    // and recorded.
    {
        use sha2::{Digest, Sha256};
        let vk = std::fs::read(cer.join("verifying_key.bin")).unwrap();
        let sha = hex::encode(Sha256::digest(vk));
        assert!(
            log.contains(&format!("verifying key sha256: {sha}")),
            "{log}"
        );
        let meta = std::fs::read_to_string(cer.join("metadata.json")).unwrap();
        assert!(meta.contains(&sha), "{meta}");
    }
    // A finalized ceremony takes no more contributions …
    let (ok, log) = xark(
        &[
            "ceremony",
            "contribute",
            "--ceremony-dir",
            cer_s,
            "--label",
            "late",
        ],
        &out,
    );
    assert!(!ok && log.contains("finalized"), "{log}");
    // … and contributions leave no temporary files behind.
    let stray: Vec<_> = std::fs::read_dir(&cer)
        .unwrap()
        .flatten()
        .filter(|e| e.file_name().to_string_lossy().ends_with(".tmp"))
        .collect();
    assert!(stray.is_empty(), "{stray:?}");

    let (pk, vk) = (cer.join("proving_key.bin"), cer.join("verifying_key.bin"));
    let proof = tmp.path().join("proof").join("proof.bin");
    let log = step(&[
        "prove",
        "--inputs",
        r#"{"secret": "3", "result": "27"}"#,
        "--proving-key",
        pk.to_str().unwrap(),
        "--out",
        proof.parent().unwrap().to_str().unwrap(),
    ]);
    // Its next step verifies with the ceremony's verifying key, and this proof.
    assert!(
        log.contains(&format!("--verifying-key {}", vk.display()))
            && log.contains(&format!("--proof {}", proof.display())),
        "{log}"
    );
    let verify = |public: &str| {
        xark(
            &[
                "verify",
                "--verifying-key",
                vk.to_str().unwrap(),
                "--proof",
                proof.to_str().unwrap(),
                "--inputs",
                public,
            ],
            &out,
        )
    };
    let (ok, log) = verify(r#"{"result": "27"}"#);
    assert!(ok && log.contains("verified"), "{log}");
    let (ok, log) = verify(r#"{"result": "28"}"#);
    assert!(
        !ok || !log.contains("Proof verified"),
        "a wrong public input must fail: {log}"
    );

    // A finalized ceremony is production-safe: `xark export` takes its key
    // without `--allow-insecure`.
    let verifier = tmp.path().join("verifier");
    step(&[
        "export",
        "--verifying-key",
        vk.to_str().unwrap(),
        "--proof",
        proof.to_str().unwrap(),
        "--public-inputs",
        proof.with_file_name("public_inputs.bin").to_str().unwrap(),
        "--out",
        verifier.to_str().unwrap(),
    ]);
    assert!(verifier.join("Cargo.toml").is_file());

    // `--force` replaces the finalized ceremony with a fresh one: no
    // contributions, and no metadata.json left to call the new keys
    // production-safe.
    step(&[
        "ceremony",
        "init",
        "--ptau-file",
        ptau_s,
        "--out",
        cer_s,
        "--force",
    ]);
    assert!(
        !cer.join("metadata.json").exists(),
        "metadata.json survived --force"
    );
    assert!(!cer.join("contribution_0001.json").exists());
    assert_eq!(
        std::fs::read_to_string(cer.join("contribution_count"))
            .unwrap()
            .trim(),
        "0"
    );
    let log = step(&["ceremony", "verify", "--ceremony-dir", cer_s]);
    assert!(log.contains("Verified 0 contribution"), "{log}");
}

/// A `--ceremony-dir` that isn't one (a typo) says so, with how to start one; a
/// ceremony whose key is damaged names the file.
#[test]
fn a_wrong_or_damaged_ceremony_dir_says_so() {
    let tmp = tempdir();
    let (out, target) = (tmp.path().join("cube"), tmp.path().join("target"));
    let (ok, log) = xark_build("cube", &out, &target);
    assert!(ok, "xark build: {log}");
    let missing = tmp.path().join("no-such-ceremony");
    for cmd in ["contribute", "verify", "finalize"] {
        let (ok, log) = xark(
            &["ceremony", cmd, "--ceremony-dir", missing.to_str().unwrap()],
            &out,
        );
        assert!(
            !ok && log.contains("isn't a ceremony directory") && log.contains("ceremony init"),
            "ceremony {cmd}: {log}"
        );
    }

    let ptau = tmp.path().join("test.ptau");
    std::fs::write(&ptau, build_valid_ptau(12)).unwrap();
    let cer = tmp.path().join("ceremony");
    let cer_s = cer.to_str().unwrap();
    let (ok, log) = xark(
        &[
            "ceremony",
            "init",
            "--ptau-file",
            ptau.to_str().unwrap(),
            "--out",
            cer_s,
        ],
        &out,
    );
    assert!(ok, "init: {log}");
    let pk = cer.join("proving_key.bin");
    let bytes = std::fs::read(&pk).unwrap();
    std::fs::write(&pk, &bytes[..bytes.len() / 2]).unwrap();
    let (ok, log) = xark(&["ceremony", "contribute", "--ceremony-dir", cer_s], &out);
    assert!(
        !ok && log.contains("proving_key.bin isn't a proving key written by `xark ceremony`"),
        "{log}"
    );
}
