//! `xark init` scaffolds a crate whose own tests pass under `xark test` — the
//! first thing a new user runs.

mod common;
use common::{run, tempdir};
use std::path::Path;

#[test]
fn init_then_test() {
    let tmp = tempdir();
    // A dash: the package is `zk-demo`, its circuit fn `zk_demo`, and the build (named
    // after the package) is where the generated test function looks.
    let dir = tmp.path().join("zk-demo");
    let dir_s = dir.to_str().unwrap();
    let (ok, _, err) = run(&["init", dir_s]);
    assert!(ok, "init failed: {err}");

    // The scaffold depends on the published crates; point it at this checkout.
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let root = root.canonicalize().unwrap();
    let manifest = dir.join("Cargo.toml");
    let toml = std::fs::read_to_string(&manifest).unwrap();
    // The scaffold pins major.minor (of a pre-release too).
    let core = env!("CARGO_PKG_VERSION").split('-').next().unwrap();
    let ver = core.rsplit_once('.').unwrap().0;
    let patched = toml.replace(
        &format!("xark = {{ version = \"{ver}\" }}"),
        &format!(
            "xark = {{ path = \"{}\" }}",
            root.join("crates/lang").display()
        ),
    );
    assert!(
        !toml.contains("xark-prover"),
        "a circuit crate needs only `xark`:\n{toml}"
    );
    assert!(
        toml.contains("name = \"zk-demo\""),
        "crate not named after the directory:\n{toml}"
    );
    assert_ne!(
        toml, patched,
        "the scaffold's dependencies changed shape:\n{toml}"
    );
    std::fs::write(&manifest, patched).unwrap();

    // A target shared across runs: the prover's dependencies build once.
    let target = root.join("target/init-test");
    let xark = |args: &[&str]| {
        let o = std::process::Command::new(common::xark_bin())
            .args(args)
            .env("CARGO_TARGET_DIR", &target)
            .output()
            .expect("invoke xark");
        let out =
            String::from_utf8_lossy(&o.stdout).into_owned() + &String::from_utf8_lossy(&o.stderr);
        assert!(o.status.success(), "xark {args:?} failed:\n{out}");
        out
    };

    let out = xark(&["test", dir_s]);
    assert!(
        out.contains("2 passed"),
        "expected the scaffold's 2 tests:\n{out}"
    );
    // Arguments after `--` reach the test binary.
    let out = xark(&["test", dir_s, "--", "--list"]);
    assert!(
        out.contains("tests::accepts_valid: test"),
        "--list didn't reach the tests:\n{out}"
    );

    // The editor check (rust-analyzer's `overrideCommand`) reports errors in
    // the tests too, not only in what the circuit build compiles.
    let lib = dir.join("src/lib.rs");
    let clean = std::fs::read_to_string(&lib).unwrap();
    let broken = clean.replacen(
        "fn accepts_valid() {",
        "fn accepts_valid() {\n        let _n: u32 = \"not a number\";",
        1,
    );
    assert_ne!(clean, broken, "the scaffold's tests changed shape");
    std::fs::write(&lib, broken).unwrap();
    let o = std::process::Command::new(common::xark_bin())
        .args(["check", dir_s, "--message-format=json"])
        .env("CARGO_TARGET_DIR", &target)
        .output()
        .expect("invoke xark");
    let errors = String::from_utf8_lossy(&o.stdout)
        .lines()
        .filter_map(|l| serde_json::from_str::<serde_json::Value>(l).ok())
        .filter(|v| v["reason"] == "compiler-message" && v["message"]["level"] == "error")
        .count();
    assert!(
        !o.status.success() && errors > 0,
        "no error for the tests module"
    );
    std::fs::write(&lib, clean).unwrap();

    // Plain `cargo test` after an edit tests the edited circuit: the stale build
    // is rebuilt (with `$XARK`), not silently reused. Cubing breaks `2 * 2 == 4`.
    std::thread::sleep(std::time::Duration::from_millis(1100)); // mtime granularity
    let src = std::fs::read_to_string(&lib).unwrap();
    let edited = src.replace("secret * secret,", "secret * secret * secret,");
    assert_ne!(src, edited, "the scaffold's circuit changed shape");
    std::fs::write(&lib, edited).unwrap();
    let o = std::process::Command::new("cargo")
        .args(["test", "--release"])
        .current_dir(&dir)
        .env("CARGO_TARGET_DIR", &target)
        .env("XARK", common::xark_bin())
        .output()
        .expect("invoke cargo");
    let log = String::from_utf8_lossy(&o.stdout).into_owned() + &String::from_utf8_lossy(&o.stderr);
    assert!(
        !o.status.success() && log.contains("accepts_valid ... FAILED"),
        "cargo test ran the stale circuit:\n{log}"
    );

    // A build over another field (`--field 7`) isn't the circuit Rust tests check:
    // plain `cargo test` rebuilds it for BN254, then passes.
    std::fs::write(&lib, &src).unwrap();
    let (ok, _, err) = run(&["build", dir_s, "--field", "7"]);
    assert!(ok, "build --field 7 failed: {err}");
    let o = std::process::Command::new("cargo")
        .args(["test", "--release"])
        .current_dir(&dir)
        .env("CARGO_TARGET_DIR", &target)
        .env("XARK", common::xark_bin())
        .output()
        .expect("invoke cargo");
    let log = String::from_utf8_lossy(&o.stdout).into_owned() + &String::from_utf8_lossy(&o.stderr);
    assert!(
        o.status.success() && log.contains("building circuit"),
        "cargo test didn't rebuild the field-7 circuit:\n{log}"
    );
    let (ok, field, _) = run(&["inspect", dir_s]);
    assert!(ok && field.contains("bn254"), "{field}");
}
