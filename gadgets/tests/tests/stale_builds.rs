//! Commands that build first reuse a build while no source of the circuit has
//! changed since, and a command that uses the build rebuilds once one has.

mod common;
use common::{tempdir, xark_bin};
use std::path::{Path, PathBuf};
use std::process::Command;

/// `xark <args>` in `dir`: success, and stderr.
fn xark(dir: &Path, args: &[&str]) -> (bool, String) {
    let o = Command::new(xark_bin())
        .args(args)
        .current_dir(dir)
        .output()
        .expect("invoke xark");
    (
        o.status.success(),
        String::from_utf8_lossy(&o.stderr).into_owned(),
    )
}

/// A copy of `examples/cube` in `tmp`.
fn cube(tmp: &Path) -> PathBuf {
    let dir = tmp.join("cube");
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/cube");
    let crates = src.join("../../crates").canonicalize().unwrap();
    for f in ["Cargo.toml", "src/lib.rs"] {
        let text = std::fs::read_to_string(src.join(f)).unwrap();
        std::fs::create_dir_all(dir.join(f).parent().unwrap()).unwrap();
        std::fs::write(
            dir.join(f),
            text.replace("../../crates", crates.to_str().unwrap()),
        )
        .unwrap();
    }
    dir
}

/// Rewrite `src/lib.rs`, newer than any build (file times can be a second coarse).
fn edit(dir: &Path, from: &str, to: &str) {
    std::thread::sleep(std::time::Duration::from_millis(1100));
    let lib = dir.join("src/lib.rs");
    let text = std::fs::read_to_string(&lib).unwrap();
    assert!(text.contains(from));
    std::fs::write(&lib, text.replace(from, to)).unwrap();
}

#[test]
fn profile_rebuilds_only_after_a_change() {
    let tmp = tempdir();
    let dir = cube(tmp.path());
    let (ok, err) = xark(&dir, &["profile"]);
    assert!(ok && err.contains("building circuit"), "{err}");
    let (ok, err) = xark(&dir, &["profile"]);
    assert!(
        ok && err.contains("not rebuilding") && !err.contains("building circuit"),
        "{err}"
    );
    edit(&dir, "pub fn cube", "// edited\npub fn cube");
    let (ok, err) = xark(&dir, &["profile"]);
    assert!(ok && err.contains("building circuit"), "{err}");
}

#[test]
fn check_reuses_a_current_build() {
    let tmp = tempdir();
    let dir = cube(tmp.path());
    let inputs = r#"{"secret": 3, "result": 27}"#;
    let (ok, err) = xark(&dir, &["check", ".", "--inputs", inputs]);
    assert!(ok && err.contains("building circuit"), "{err}");
    let (ok, err) = xark(&dir, &["check", ".", "--inputs", inputs]);
    assert!(ok && !err.contains("building circuit"), "{err}");
}

#[test]
fn a_build_clears_the_last_ones_debug_output() {
    let tmp = tempdir();
    let dir = cube(tmp.path());
    let out = dir.join("target/xark/cube");
    let (ok, err) = xark(&dir, &["build", ".", "--emit-json"]);
    assert!(ok && out.join("circuit.json").exists(), "{err}");
    let (ok, err) = xark(&dir, &["build", "."]);
    assert!(ok, "{err}");
    for f in ["circuit.json", "r1cs.json", "graph.dot"] {
        assert!(!out.join(f).exists(), "{f} is left from the last build");
    }
}

/// `deps` marks a build complete, so it's written last: a build stopped before it
/// reads as stale, never as current without (say) its `schema.json`.
#[test]
fn a_build_writes_deps_last() {
    let tmp = tempdir();
    let dir = cube(tmp.path());
    let (ok, err) = xark(&dir, &["build", "."]);
    assert!(ok, "{err}");
    let out = dir.join("target/xark/cube");
    let written = |f: &str| std::fs::metadata(out.join(f)).unwrap().modified().unwrap();
    for f in ["circuit.xbc", "sources.json", "digest", "schema.json"] {
        assert!(written(f) <= written("deps"), "{f} was written after deps");
    }
}

/// Builds of one crate at once (an editor's `xark check` beside a terminal's `xark
/// build`) each read a whole `.wasm`: none finds it mid-replacement.
#[test]
fn concurrent_builds_of_a_crate_all_succeed() {
    let tmp = tempdir();
    let dir = cube(tmp.path());
    for round in 0..2 {
        if round > 0 {
            edit(&dir, "pub fn cube", "// edited\npub fn cube");
        }
        let builds: Vec<_> = (0..4)
            .map(|i| {
                Command::new(xark_bin())
                    .args(["build", ".", "--out", &format!("out{i}")])
                    .current_dir(&dir)
                    .stderr(std::process::Stdio::piped())
                    .spawn()
                    .expect("spawn xark build")
            })
            .collect();
        for b in builds {
            let o = b.wait_with_output().unwrap();
            assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));
        }
    }
}

#[test]
fn client_builds_a_missing_or_stale_circuit() {
    let tmp = tempdir();
    let dir = cube(tmp.path());
    let out = tmp.path().join("client/cube.ts");
    let client = [
        "client",
        ".",
        "--no-functions",
        "--out",
        out.to_str().unwrap(),
    ];
    let (ok, err) = xark(&dir, &client);
    assert!(ok && err.contains("no build found"), "{err}");
    edit(&dir, "secret", "seed");
    let (ok, err) = xark(&dir, &client);
    assert!(ok && err.contains("changed since it was built"), "{err}");
    let schema = std::fs::read_to_string(out.with_file_name("cube.schema.ts")).unwrap();
    assert!(
        schema.contains("seed") && !schema.contains("secret"),
        "{schema}"
    );
}

#[test]
fn inspect_rebuilds_a_stale_circuit() {
    let tmp = tempdir();
    let dir = cube(tmp.path());
    let (ok, err) = xark(&dir, &["inspect", "."]);
    assert!(ok && err.contains("no build found"), "{err}");
    let (ok, err) = xark(&dir, &["inspect", "."]);
    assert!(ok && !err.contains("building circuit"), "{err}");
    edit(&dir, "pub fn cube", "// edited\npub fn cube");
    let (ok, err) = xark(&dir, &["inspect", "."]);
    assert!(
        ok && err.contains("src/lib.rs changed since it was built"),
        "{err}"
    );
}

#[test]
fn prove_rebuilds_a_stale_circuit_and_asks_for_new_keys() {
    let tmp = tempdir();
    let dir = cube(tmp.path());
    for args in [&["build", "."][..], &["setup", ".", "--insecure-dev-mode"]] {
        let (ok, err) = xark(&dir, args);
        assert!(ok, "{err}");
    }
    edit(&dir, "secret.pow(3)", "secret.pow(3) + secret");
    // The proof would be of the circuit as it was: rebuilt, the old key is refused.
    let (ok, err) = xark(
        &dir,
        &["prove", ".", "--inputs", r#"{"secret": 3, "result": 30}"#],
    );
    assert!(!ok, "{err}");
    assert!(
        err.contains("src/lib.rs changed since it was built"),
        "{err}"
    );
    assert!(err.contains("run `xark setup` again"), "{err}");
    let (ok, err) = xark(&dir, &["setup", ".", "--insecure-dev-mode"]);
    assert!(ok && !err.contains("changed since"), "{err}");
    let (ok, err) = xark(
        &dir,
        &["prove", ".", "--inputs", r#"{"secret": 3, "result": 30}"#],
    );
    assert!(ok, "{err}");
}
