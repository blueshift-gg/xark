//! The CLI's answers to common mistakes: a mistyped path, a name `cargo` would
//! refuse, a corrupt artifact. Each must stop with an error that names the
//! problem, never fall back to something else.

mod common;
use common::{run, tempdir, xark_bin, xark_build, xark_prove, xark_setup};
use std::process::Command;

/// `xark <args>` in `dir`, returning `(success, stdout + stderr)`.
fn run_in(dir: &std::path::Path, args: &[&str]) -> (bool, String) {
    let o = Command::new(xark_bin())
        .args(args)
        .current_dir(dir)
        .output()
        .expect("invoke xark");
    let out = String::from_utf8_lossy(&o.stdout).into_owned() + &String::from_utf8_lossy(&o.stderr);
    (o.status.success(), out)
}

#[test]
fn init_refuses_names_cargo_would() {
    let tmp = tempdir();
    for (name, why, suggest) in [
        ("type", "keyword", "type_circuit"),
        ("self", "keyword", "self_circuit"),
        ("1st", "starts with a digit", "circuit_1st"),
        ("a b", "only letters", "a_b"),
    ] {
        let (ok, out) = run_in(tmp.path(), &["init", name]);
        assert!(!ok, "`xark init {name}` succeeded:\n{out}");
        assert!(
            out.contains(why) && out.contains(&format!("xark init {suggest}")),
            "`xark init {name}`:\n{out}"
        );
        assert!(!tmp.path().join(name).exists(), "`{name}` was scaffolded");
    }
}

#[test]
fn missing_paths_are_reported() {
    let tmp = tempdir();
    let missing = tmp.path().join("nope");
    let missing = missing.to_str().unwrap();
    for cmd in ["prove", "setup", "inspect", "verify", "client", "export"] {
        let (ok, _, err) = run(&[cmd, missing]);
        assert!(
            !ok && err.contains("no such directory"),
            "`xark {cmd}` on a missing path:\n{err}"
        );
    }
    for cmd in ["build", "test", "profile"] {
        let (ok, out) = run_in(tmp.path(), &[cmd, "./nope"]);
        assert!(
            !ok && out.contains("no such directory: ./nope"),
            "`xark {cmd}` on a missing path:\n{out}"
        );
    }
    // A directory that isn't a crate.
    let (ok, out) = run_in(tmp.path(), &["build"]);
    assert!(!ok && out.contains("no Cargo.toml in ."), "{out}");
}

#[test]
fn build_names_the_package() {
    let tmp = tempdir();
    let dir = common::circuit_crate("arithmetic_square");
    let o = Command::new(xark_bin())
        .args(["build", "--out"])
        .arg(tmp.path().join("out"))
        .current_dir(&dir)
        .env("CARGO_TARGET_DIR", tmp.path().join("target"))
        .output()
        .expect("invoke xark");
    let err = String::from_utf8_lossy(&o.stderr);
    assert!(o.status.success(), "build failed:\n{err}");
    assert!(
        err.contains("building circuit `arithmetic_square`"),
        "build of `.` misnamed:\n{err}"
    );
}

#[test]
fn corrupt_public_inputs_get_no_prove_hint() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let (ok, err) = xark_build("arithmetic_square", &out, &tmp.path().join("target"));
    assert!(ok, "build failed: {err}");
    let (ok, err) = xark_setup(&out);
    assert!(ok, "setup failed: {err}");
    let (ok, err) = xark_prove(&out, &[("x", "3"), ("y", "9")]);
    assert!(ok, "prove failed: {err}");

    let out_s = out.to_str().unwrap();
    let pi = out.join("public_inputs.bin");
    std::fs::write(&pi, [1, 2, 3]).unwrap();
    let (ok, _, err) = run(&["verify", out_s]);
    assert!(!ok && !err.contains("run `xark prove` first"), "{err}");
    assert!(
        err.contains("isn't a public inputs file written by `xark prove`"),
        "{err}"
    );

    std::fs::remove_file(&pi).unwrap();
    let (ok, _, err) = run(&["verify", out_s]);
    assert!(!ok && err.contains("run `xark prove` first"), "{err}");

    // An empty proof says so, not the decoder's "failed to fill whole buffer".
    std::fs::write(out.join("proof.bin"), []).unwrap();
    let (ok, _, err) = run(&["verify", out_s]);
    assert!(
        !ok && err.contains("is empty: it isn't a proof written by `xark prove`"),
        "{err}"
    );
}

/// `xark clean` removes build output under the current directory only: never
/// through a symlink, which can lead anywhere.
#[cfg(unix)]
#[test]
fn clean_does_not_follow_symlinks() {
    let tmp = tempdir();
    let (inside, outside) = (tmp.path().join("in"), tmp.path().join("out"));
    let ours = ["xark", "xark-wasm", "xark-client"].map(|d| inside.join("a/target").join(d));
    for d in ours.iter().chain([&outside.join("b/target/xark")]) {
        std::fs::create_dir_all(d).unwrap();
    }
    std::os::unix::fs::symlink(&outside, inside.join("link")).unwrap();
    let (ok, out) = run_in(&inside, &["clean"]);
    assert!(ok, "{out}");
    for d in &ours {
        assert!(!d.exists(), "{} not cleaned:\n{out}", d.display());
    }
    assert!(
        outside.join("b/target/xark").exists(),
        "cleaned through a symlink:\n{out}"
    );
}

/// A proving key made for an earlier build is named as stale, not left to fail
/// the proof's self-verification.
#[test]
fn stale_proving_key_is_named() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let (ok, err) = xark_build("arithmetic_square", &out, &tmp.path().join("target"));
    assert!(ok, "build failed: {err}");
    let (ok, err) = xark_setup(&out);
    assert!(ok, "setup failed: {err}");
    let meta = out.join("metadata.json");
    let mut m: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&meta).unwrap()).unwrap();
    // As if another Rust had built the same circuit: another `circuit.xbc`, the
    // same R1CS digest. The key fits.
    let saved = m.clone();
    m["circuit_hash"] = "00".repeat(32).into();
    std::fs::write(&meta, m.to_string()).unwrap();
    let (ok, err) = xark_prove(&out, &[("x", "3"), ("y", "9")]);
    assert!(
        ok && err.contains("made from another build of this circuit"),
        "{err}"
    );
    // As if the circuit had been rebuilt with a change since setup: refused.
    m["digest"] = "00".repeat(16).into();
    std::fs::write(&meta, m.to_string()).unwrap();
    let (ok, err) = xark_prove(&out, &[("x", "3"), ("y", "9")]);
    assert!(
        !ok && err.contains("different build of the circuit"),
        "{err}"
    );
    // A key from before `digest` was recorded: the file's hash alone decides.
    let mut old = saved;
    old.as_object_mut().unwrap().remove("digest");
    old["circuit_hash"] = "00".repeat(32).into();
    std::fs::write(&meta, old.to_string()).unwrap();
    let (ok, err) = xark_prove(&out, &[("x", "3"), ("y", "9")]);
    assert!(
        !ok && err.contains("different build of the circuit"),
        "{err}"
    );
}

/// Like cargo, the commands find the crate from a directory inside it (`xark
/// build` from `src/`); a directory named explicitly is taken as given.
#[test]
fn commands_find_the_crate_from_a_subdirectory() {
    let tmp = tempdir();
    let src = common::circuit_crate("arithmetic_square").join("src");
    let out = tmp.path().join("out");
    let o = Command::new(xark_bin())
        .args(["build", "--out"])
        .arg(&out)
        .current_dir(&src)
        .env("CARGO_TARGET_DIR", tmp.path().join("target"))
        .output()
        .expect("invoke xark");
    let err = String::from_utf8_lossy(&o.stderr);
    assert!(o.status.success(), "build from src/ failed:\n{err}");
    assert!(
        err.contains("building circuit `arithmetic_square`"),
        "{err}"
    );
    let (ok, out_log) = run_in(&src, &["check"]);
    assert!(ok, "check from src/ failed:\n{out_log}");

    // Named, a non-crate directory is an error, not a walk up.
    let (ok, out_log) = run_in(&src.join(".."), &["build", "src"]);
    assert!(!ok && out_log.contains("no Cargo.toml in src"), "{out_log}");
}

/// `--field` takes `bn254` or a prime modulus; anything else stops before building.
#[test]
fn field_must_be_bn254_or_a_prime() {
    let tmp = tempdir();
    let dir = copy_example(tmp.path(), "arithmetic_square");
    for (field, why) in [("banana", "isn't a field xark knows"), ("9", "isn't prime")] {
        for cmd in ["build", "profile"] {
            let (ok, out) = run_in(&dir, &[cmd, ".", "--field", field]);
            assert!(
                !ok && out.contains(why),
                "`xark {cmd} --field {field}`:\n{out}"
            );
            assert!(!out.contains("building circuit"), "{out}");
        }
    }
}

/// A circuit built over another field is for counting constraints: its next step
/// is `xark profile`, `xark setup` rebuilds it for BN254 (keys are BN254's), and one
/// built elsewhere (`--out`) is refused rather than given meaningless keys.
#[test]
fn keys_are_for_bn254_builds() {
    let tmp = tempdir();
    let dir = copy_example(tmp.path(), "arithmetic_square");
    let (ok, out) = run_in(&dir, &["build", ".", "--field", "7"]);
    assert!(ok && out.contains("xark profile . --field 7"), "{out}");
    assert!(!out.contains("xark setup"), "{out}");
    let (ok, out) = run_in(&dir, &["setup", "--insecure-dev-mode"]);
    assert!(
        ok && out.contains("built for another field than bn254"),
        "{out}"
    );
    let (ok, out) = run_in(&dir, &["build", ".", "--field", "7", "--out", "other"]);
    assert!(ok, "{out}");
    let (ok, out) = run_in(&dir, &["setup", "other", "--insecure-dev-mode"]);
    assert!(
        !ok && out.contains("was built over another field (7)"),
        "{out}"
    );
    // `inspect` reads it as built.
    let (ok, out) = run_in(&dir, &["inspect", "other"]);
    assert!(ok && out.contains("custom"), "{out}");
}

/// A failed setup leaves the previous keys and metadata as they were (never a
/// new key beside old metadata), and no temporary files.
#[test]
fn failed_setup_keeps_the_previous_keys() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let (ok, err) = xark_build("arithmetic_square", &out, &tmp.path().join("target"));
    assert!(ok, "build failed: {err}");
    let (ok, err) = xark_setup(&out);
    assert!(ok, "setup failed: {err}");
    let read = |f: &str| std::fs::read(out.join(f)).unwrap();
    let before = (read("pk.bin"), read("vk.bin"), read("metadata.json"));

    // A transcript too small for any circuit: setup fails partway.
    let ptau = tmp.path().join("tiny.ptau");
    std::fs::write(&ptau, common::build_valid_ptau(1)).unwrap();
    let (ok, _, err) = run(&[
        "setup",
        out.to_str().unwrap(),
        "--ptau-file",
        ptau.to_str().unwrap(),
    ]);
    assert!(!ok, "setup with a 2-point transcript succeeded");
    assert_eq!(
        (read("pk.bin"), read("vk.bin"), read("metadata.json")),
        before,
        "a failed setup changed the keys: {err}"
    );
    let stray: Vec<_> = std::fs::read_dir(&out)
        .unwrap()
        .flatten()
        .filter(|e| e.file_name().to_string_lossy().ends_with(".tmp"))
        .collect();
    assert!(stray.is_empty(), "{stray:?}");
}

/// `xark setup --out` writes the keys to a directory of its own, warning when it
/// already holds something, and points `xark prove` at them.
#[test]
fn setup_out_warns_and_names_the_key() {
    let tmp = tempdir();
    let dir = copy_example(tmp.path(), "arithmetic_square");
    let setup = ["setup", "--insecure-dev-mode", "--out", "keys"];
    let (ok, out) = run_in(&dir, &setup);
    assert!(ok && !out.contains("isn't empty"), "{out}");
    assert!(out.contains("--proving-key keys/pk.bin"), "{out}");
    // It names the verifying key's sha256 (what a client pins its verifier to), and
    // records it.
    use sha2::{Digest, Sha256};
    let vk_sha = hex::encode(Sha256::digest(
        std::fs::read(dir.join("keys/vk.bin")).unwrap(),
    ));
    assert!(
        out.contains(&format!("verifying key sha256: {vk_sha}")),
        "{out}"
    );
    let meta = std::fs::read_to_string(dir.join("keys/metadata.json")).unwrap();
    assert!(
        meta.contains(&format!("\"verifying_key_sha256\": \"{vk_sha}\"")),
        "{meta}"
    );
    let (ok, out) = run_in(&dir, &setup);
    assert!(ok && out.contains("keys isn't empty"), "{out}");
    let (ok, out) = run_in(
        &dir,
        &[
            "prove",
            "--proving-key",
            "keys/pk.bin",
            "--inputs",
            r#"{"x": "3", "y": "9"}"#,
        ],
    );
    assert!(ok && !out.contains("no proving key found"), "{out}");
}

/// `xark prove --out` writes the proof and its public inputs to a directory of its
/// own, warning when it already holds something, and points `xark verify` at them.
#[test]
fn prove_out_is_a_directory() {
    let tmp = tempdir();
    let dir = copy_example(tmp.path(), "arithmetic_square");
    let prove = [
        "prove",
        "--inputs",
        r#"{"x": "3", "y": "9"}"#,
        "--out",
        "proofs",
    ];
    let (ok, out) = run_in(&dir, &prove);
    assert!(ok && !out.contains("isn't empty"), "{out}");
    assert!(dir.join("proofs/proof.bin").exists() && dir.join("proofs/public_inputs.bin").exists());
    let verify = "xark verify . --proof proofs/proof.bin --public-inputs proofs/public_inputs.bin";
    assert!(out.contains(verify), "{out}");
    let (ok, out) = run_in(&dir, &prove);
    assert!(ok && out.contains("proofs isn't empty"), "{out}");
    let args: Vec<&str> = verify.split(' ').skip(1).collect();
    let (ok, out) = run_in(&dir, &args);
    assert!(ok && out.contains("Proof verified"), "{out}");
}

/// A proof that fails against keys made after it (`xark setup` again, no new
/// `xark prove`) says so.
#[test]
fn verify_names_a_proof_older_than_the_key() {
    let tmp = tempdir();
    let dir = copy_example(tmp.path(), "arithmetic_square");
    let (ok, out) = run_in(&dir, &["prove", "--inputs", r#"{"x": "3", "y": "9"}"#]);
    assert!(ok, "{out}");
    let (ok, out) = run_in(&dir, &["verify"]);
    assert!(ok && !out.contains("hint:"), "{out}");
    std::thread::sleep(std::time::Duration::from_millis(1100)); // coarse file times
    let (ok, out) = run_in(&dir, &["setup", "--insecure-dev-mode"]);
    assert!(ok, "{out}");
    let (ok, out) = run_in(&dir, &["verify"]);
    assert!(!ok, "{out}");
    assert!(
        out.contains("is older than") && out.contains("run `xark prove` again"),
        "{out}"
    );
}

/// `xark client -o` writes the client where it's told, over whatever is there
/// (an older client, or a file from an earlier tool), with its schema beside it.
#[test]
fn client_overwrites_its_output() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let (ok, err) = xark_build("arithmetic_square", &out, &tmp.path().join("target"));
    assert!(ok, "build failed: {err}");
    let ts = tmp.path().join("client.ts");
    std::fs::write(&ts, "// from an older tool\n").unwrap();
    std::fs::write(tmp.path().join("client.schema.ts"), "export default {};\n").unwrap();
    for _ in 0..2 {
        let (ok, _, err) = run(&["client", out.to_str().unwrap(), "-o", ts.to_str().unwrap()]);
        assert!(ok, "client failed: {err}");
    }
    let text = std::fs::read_to_string(&ts).unwrap();
    assert!(text.starts_with("// Generated by `xark client`"), "{text}");
    let schema = std::fs::read_to_string(tmp.path().join("client.schema.ts")).unwrap();
    assert!(
        schema.contains("\"circuit\": \"arithmetic_square\""),
        "{schema}"
    );
}

/// `xark client -o` given a directory (an existing one, or a path ending in `/`)
/// writes the client and its schema in it, and nothing beside it.
#[test]
fn client_out_can_be_a_directory() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let (ok, err) = xark_build("arithmetic_square", &out, &tmp.path().join("target"));
    assert!(ok, "build failed: {err}");
    let existing = tmp.path().join("clients");
    std::fs::create_dir(&existing).unwrap();
    let fresh = format!("{}/", tmp.path().join("fresh").display());
    for dir in [existing.to_str().unwrap(), fresh.as_str()] {
        let (ok, _, err) = run(&["client", out.to_str().unwrap(), "-o", dir]);
        assert!(ok, "client -o {dir} failed: {err}");
        let dir = std::path::Path::new(dir);
        for f in ["arithmetic_square.ts", "arithmetic_square.schema.ts"] {
            assert!(dir.join(f).exists(), "no {f} in {}", dir.display());
        }
    }
    assert!(!tmp.path().join("clients.schema.ts").exists());
}

/// `xark prove` on a crate that was never built builds it, makes a dev key and
/// proves, in one command (the setup step used to be skipped after the build).
#[test]
fn first_prove_builds_and_sets_up() {
    let tmp = tempdir();
    let dir = copy_example(tmp.path(), "arithmetic_square");
    let (ok, out) = run_in(&dir, &["prove", "--inputs", r#"{"x": "3", "y": "9"}"#]);
    assert!(ok, "first `xark prove` failed:\n{out}");
    assert!(
        out.contains("no build found") && out.contains("no proving key found"),
        "{out}"
    );
}

/// A build that fails removes the previous build's circuit, so later commands
/// stop at "build first" instead of proving the old one.
#[test]
fn failed_build_removes_the_old_circuit() {
    let tmp = tempdir();
    let dir = copy_example(tmp.path(), "arithmetic_square");
    let (ok, out) = run_in(&dir, &["build"]);
    assert!(ok, "build failed:\n{out}");
    let built = dir.join("target/xark/arithmetic_square");
    assert!(built.join("circuit.xbc").is_file());

    let lib = dir.join("src/lib.rs");
    let source = std::fs::read_to_string(&lib).unwrap();
    std::fs::write(&lib, format!("{source}\nfn broken() -> u8 {{ \"\" }}\n")).unwrap();
    let (ok, out) = run_in(&dir, &["build"]);
    assert!(!ok, "a broken source built:\n{out}");
    for f in ["circuit.xbc", "schema.json", "digest"] {
        assert!(!built.join(f).exists(), "{f} survived a failed build");
    }
    let (ok, out) = run_in(&dir, &["setup", "--insecure-dev-mode"]);
    assert!(!ok && out.contains("xark build"), "{out}");
}

/// Copy `examples/<name>` into `dir`, its path dependencies made absolute.
fn copy_example(dir: &std::path::Path, name: &str) -> std::path::PathBuf {
    let src = common::circuit_crate(name);
    let dst = dir.join(name);
    std::fs::create_dir_all(dst.join("src")).unwrap();
    std::fs::copy(src.join("src/lib.rs"), dst.join("src/lib.rs")).unwrap();
    let root = src.join("../..").canonicalize().unwrap();
    let manifest = std::fs::read_to_string(src.join("Cargo.toml"))
        .unwrap()
        .replace("../../", &format!("{}/", root.display()));
    std::fs::write(dst.join("Cargo.toml"), manifest).unwrap();
    dst
}

/// `export` and `verify` refuse a key made for a different build of the circuit,
/// as `prove` does, and `export` refuses a proof its key doesn't verify (it
/// becomes the generated crate's self-test).
#[test]
fn export_and_verify_check_the_key() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let (ok, err) = xark_build("arithmetic_square", &out, &tmp.path().join("target"));
    assert!(ok, "build failed: {err}");
    let (ok, err) = xark_setup(&out);
    assert!(ok, "setup failed: {err}");
    let (ok, err) = xark_prove(&out, &[("x", "3"), ("y", "9")]);
    assert!(ok, "prove failed: {err}");
    let o = out.to_str().unwrap();

    // A new key: the old proof no longer verifies with it.
    let (ok, _, err) = run(&[
        "setup",
        o,
        "--insecure-dev-mode",
        "--deterministic-rng",
        "2",
    ]);
    assert!(ok, "second setup failed: {err}");
    let (ok, _, err) = run(&["export", o, "--allow-insecure"]);
    assert!(!ok && err.contains("doesn't verify"), "{err}");
    assert!(!out.join("verifier").exists(), "exported anyway");

    // As if the circuit had been rebuilt with a change since setup.
    let meta = out.join("metadata.json");
    let mut m: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&meta).unwrap()).unwrap();
    m["circuit_hash"] = "00".repeat(32).into();
    m["digest"] = "00".repeat(16).into();
    std::fs::write(&meta, m.to_string()).unwrap();
    for cmd in [&["export", o, "--allow-insecure"][..], &["verify", o]] {
        let (ok, stdout, err) = run(cmd);
        assert!(
            !ok && err.contains("different build of the circuit"),
            "`xark {}`:\n{stdout}{err}",
            cmd[0]
        );
    }
}

/// `--inputs` takes a gadget type in its natural encoding (`schema.json`'s
/// `encoding`): a SHA-256 `Hash` as its 32 bytes, rather than its two 128-bit halves.
#[test]
fn inputs_take_natural_encodings() {
    use sha2::{Digest, Sha256};
    let tmp = tempdir();
    let dir = copy_example(tmp.path(), "sha256");
    let digest = hex::encode(Sha256::digest(b"abc"));
    let inputs = |d: &str| format!(r#"{{"msg": "0x616263", "digest": "0x{d}"}}"#);
    let (ok, out) = run_in(&dir, &["check", "--inputs", &inputs(&digest)]);
    assert!(ok, "sha256(\"abc\") as 32 bytes:\n{out}");
    let mut wrong = digest.into_bytes();
    wrong[63] = if wrong[63] == b'0' { b'1' } else { b'0' };
    let (ok, _) = run_in(
        &dir,
        &[
            "check",
            "--inputs",
            &inputs(std::str::from_utf8(&wrong).unwrap()),
        ],
    );
    assert!(!ok, "a wrong digest was accepted");
    let (ok, out) = run_in(&dir, &["check", "--inputs", &inputs("00")]);
    assert!(!ok && out.contains("a Hash is 32 bytes"), "{out}");
}
