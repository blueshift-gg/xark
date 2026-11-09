//! The trusted-setup ceremony through the CLI, end to end: `xark build` →
//! `xark ceremony init` (from the build, over a synthetic Powers-of-Tau
//! transcript) → two `contribute`s → `verify` → `finalize`, then `xark prove` /
//! `xark verify` with the ceremony's keys, and a wrong public input rejected.
//! The library-level ceremony (chain links, Schnorr proofs, tampering) is tested
//! in `crates/backend/src/ceremony.rs`. The transcript's toxic waste is known
//! here, so this checks the pipeline is correct, not that a ceremony is secret.

use std::path::Path;
use std::process::Command;

use crate::common::{build_valid_ptau, tempdir, xark_bin, xark_build};

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
    // A seeded key, or a smooth domain, is a key made without a `.ptau`: setup
    // refuses either with one.
    let keys = tmp.path().join("keys");
    for extra in [&["--deterministic-rng", "1"][..], &["--domain", "smooth"]] {
        let mut args = vec!["setup", ".", "--ptau-file", ptau_s, "--out"];
        args.push(keys.to_str().unwrap());
        args.extend_from_slice(extra);
        let (ok, log) = xark(&args, &out);
        assert!(!ok && log.contains("a key made without a .ptau"), "{log}");
    }
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
    let log = step(&[
        "ceremony",
        "verify",
        "--ceremony-dir",
        cer_s,
        "--ptau-file",
        ptau_s,
    ]);
    assert!(log.contains("alice") && log.contains("bob"), "{log}");
    let log = step(&[
        "ceremony",
        "finalize",
        "--ceremony-dir",
        cer_s,
        "--ptau-file",
        ptau_s,
    ]);
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
        // What the keys were made from, as `xark setup` records it.
        let m: serde_json::Value = serde_json::from_str(&meta).unwrap();
        let rows = m["num_constraints"].as_u64().unwrap();
        let domain = m["qap_domain_size"].as_u64().unwrap();
        assert!(rows > 0, "{meta}");
        assert!(domain.is_power_of_two() && domain > rows, "{meta}");
        assert_eq!(m["ptau_source"], "test.ptau", "{meta}");
        assert_eq!(m["r1cs_form"], "minimized", "{meta}");
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

    // A finalized ceremony's verifier says so.
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
    let lib = std::fs::read_to_string(verifier.join("src/lib.rs")).unwrap();
    assert!(
        lib.contains(r#"pub const SETUP: &str = "ceremony";"#),
        "{lib}"
    );
    // A ceremony of one trusts one party, as a key from `xark setup` does.
    let meta = cer.join("metadata.json");
    let two = std::fs::read_to_string(&meta).unwrap();
    std::fs::write(
        &meta,
        two.replace("mpc[2 contributors]", "mpc[1 contributors]"),
    )
    .unwrap();
    let log = step(&[
        "export",
        "--verifying-key",
        vk.to_str().unwrap(),
        "--out",
        verifier.to_str().unwrap(),
    ]);
    assert!(log.contains("a ceremony with one contributor"), "{log}");
    let lib = std::fs::read_to_string(verifier.join("src/lib.rs")).unwrap();
    assert!(
        lib.contains(r#"pub const SETUP: &str = "single-party";"#),
        "{lib}"
    );
    std::fs::write(&meta, two).unwrap();

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
    let log = step(&[
        "ceremony",
        "verify",
        "--ceremony-dir",
        cer_s,
        "--ptau-file",
        ptau_s,
    ]);
    assert!(log.contains("Verified 0 contribution"), "{log}");
    // But it doesn't finalize: with no contribution, δ follows from the seed in
    // circuit_meta.json (#66).
    let (ok, log) = xark(
        &[
            "ceremony",
            "finalize",
            "--ceremony-dir",
            cer_s,
            "--ptau-file",
            ptau_s,
        ],
        &out,
    );
    assert!(
        !ok && log.contains("the ceremony has no contributions"),
        "{log}"
    );
    assert!(!cer.join("metadata.json").exists(), "finalized anyway");
}

/// `xark setup --ptau-file`: a file that isn't a `.ptau` is refused from its header,
/// before it's read whole (#70), and the recorded `phase2_seed_hash` is the SHA-256
/// of the seed's 32 bytes, whatever its text looks like (#71).
#[test]
fn setup_from_a_ptau_checks_the_file_and_hashes_the_seed() {
    use sha2::{Digest, Sha256};
    let tmp = tempdir();
    let (out, target) = (tmp.path().join("cube"), tmp.path().join("target"));
    let (ok, log) = xark_build("cube", &out, &target);
    assert!(ok, "xark build: {log}");
    let junk = tmp.path().join("junk.ptau");
    std::fs::write(&junk, b"not a transcript at all").unwrap();
    let (ok, log) = xark(&["setup", ".", "--ptau-file", junk.to_str().unwrap()], &out);
    assert!(!ok && log.contains("isn't a .ptau file"), "{log}");

    let ptau = tmp.path().join("test.ptau");
    std::fs::write(&ptau, build_valid_ptau(12)).unwrap();
    let want = hex::encode(Sha256::digest([0xab; 32]));
    for seed in [format!("0x{}", "ab".repeat(32)), "AB".repeat(32)] {
        let keys = tmp.path().join(format!("keys-{}", &seed[..2]));
        let (ok, log) = xark(
            &[
                "setup",
                ".",
                "--ptau-file",
                ptau.to_str().unwrap(),
                "--phase2-seed",
                &seed,
                "--out",
                keys.to_str().unwrap(),
            ],
            &out,
        );
        assert!(ok, "setup: {log}");
        let meta: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(keys.join("metadata.json")).unwrap())
                .unwrap();
        assert_eq!(meta["phase2_seed_hash"], want.as_str(), "seed {seed}");
    }
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
        let mut args = vec!["ceremony", cmd, "--ceremony-dir", missing.to_str().unwrap()];
        if cmd != "contribute" {
            args.extend(["--ptau-file", "test.ptau"]);
        }
        let (ok, log) = xark(&args, &out);
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

/// A coordinator ships keys with `γ = δ` behind an honest contribution chain (which
/// lets anyone prove anything): `verify` and `finalize` recompute the initial keys
/// from the circuit, the `.ptau` and the recorded seed, and refuse them. A ceremony
/// without a recorded seed (begun with an older xark) can't be checked, and says so.
#[test]
fn keys_changed_beyond_delta_are_refused() {
    use xark_backend::keys::Groth16Keys;
    let tmp = tempdir();
    let (out, target) = (tmp.path().join("cube"), tmp.path().join("target"));
    let (ok, log) = xark_build("cube", &out, &target);
    assert!(ok, "xark build: {log}");
    let ptau = tmp.path().join("test.ptau");
    std::fs::write(&ptau, build_valid_ptau(12)).unwrap();
    let cer = tmp.path().join("ceremony");
    let (cer_s, ptau_s) = (cer.to_str().unwrap(), ptau.to_str().unwrap());
    let run = |cmd: &str| {
        let mut args = vec!["ceremony", cmd, "--ceremony-dir", cer_s];
        if cmd != "contribute" {
            args.extend(["--ptau-file", ptau_s]);
        }
        xark(&args, &out)
    };
    let (ok, log) = xark(
        &["ceremony", "init", "--ptau-file", ptau_s, "--out", cer_s],
        &out,
    );
    assert!(ok, "init: {log}");
    let (ok, log) = run("contribute");
    assert!(ok, "contribute: {log}");
    let (ok, log) = run("verify");
    assert!(ok, "an honest ceremony verifies: {log}");

    let (pk_path, vk_path) = (cer.join("proving_key.bin"), cer.join("verifying_key.bin"));
    let honest_pk = std::fs::read(&pk_path).unwrap();
    let honest_vk = std::fs::read(&vk_path).unwrap();
    let mut keys = Groth16Keys {
        proving_key: Groth16Keys::read_proving_key(&pk_path).unwrap(),
        verifying_key: Groth16Keys::read_verifying_key(&vk_path).unwrap(),
    };
    keys.verifying_key.gamma_g2 = keys.verifying_key.delta_g2;
    keys.proving_key.vk = keys.verifying_key.clone();
    keys.write_proving_key(&pk_path).unwrap();
    keys.write_verifying_key(&vk_path).unwrap();
    for cmd in ["verify", "finalize"] {
        let (ok, log) = run(cmd);
        assert!(!ok && log.contains("γ"), "{cmd} took γ = δ: {log}");
    }
    assert!(!cer.join("metadata.json").exists());

    // The honest keys back, but no recorded seed.
    std::fs::write(&pk_path, honest_pk).unwrap();
    std::fs::write(&vk_path, honest_vk).unwrap();
    let meta_path = cer.join("circuit_meta.json");
    let mut meta: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&meta_path).unwrap()).unwrap();
    meta.as_object_mut().unwrap().remove("phase2_seed");
    std::fs::write(&meta_path, meta.to_string()).unwrap();
    let (ok, log) = run("verify");
    assert!(!ok && log.contains("older xark"), "{log}");
}
