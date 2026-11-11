//! `xark add` grows a project: a circuit, then a program verifying it, all members
//! of one Cargo workspace that builds.

use crate::common::tempdir;
use std::path::Path;
use std::process::Command;

#[test]
fn add_a_circuit_then_its_program() {
    let tmp = tempdir();
    let app = tmp.path().join("app");
    std::fs::create_dir_all(&app).unwrap();
    let xark = |args: &[&str]| {
        let o = Command::new(crate::common::xark_bin())
            .args(args)
            .current_dir(&app)
            .output()
            .expect("invoke xark");
        let out =
            String::from_utf8_lossy(&o.stdout).into_owned() + &String::from_utf8_lossy(&o.stderr);
        (o.status.success(), out)
    };
    let members = || {
        std::fs::read_to_string(app.join("Cargo.toml"))
            .unwrap()
            .lines()
            .find(|l| l.starts_with("members = "))
            .unwrap()
            .to_string()
    };

    let (ok, out) = xark(&["add", "circuit", "claim"]);
    assert!(ok, "{out}");
    assert!(app.join("xark.toml").is_file() && app.join(".gitignore").is_file());
    assert!(app.join("circuits/claim/src/lib.rs").is_file());
    // The project's root has the editor settings and `.gitignore`, not the circuit.
    assert!(!app.join("circuits/claim/.gitignore").exists());
    // A glob that matches nothing would be a missing path to cargo.
    assert_eq!(members(), r#"members = ["circuits/*"]"#);

    // The scaffold depends on the published crates; point the workspace at this
    // checkout's.
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap();
    let mut manifest = std::fs::read_to_string(app.join("Cargo.toml")).unwrap();
    manifest += &format!(
        "\n[patch.crates-io]\nxark = {{ path = \"{}\" }}\nxark-verifier = {{ path = \"{}\" }}\n",
        root.join("crates/lang").display(),
        root.join("crates/verifier").display()
    );
    std::fs::write(app.join("Cargo.toml"), manifest).unwrap();

    // The program's verifier crate and TypeScript client are generated first.
    let (ok, out) = xark(&["add", "program", "claim"]);
    assert!(ok, "{out}");
    for f in [
        "programs/claim/src/lib.rs",
        "programs/claim/src/errors.rs",
        "programs/claim/src/instructions/verify.rs",
        "clients/claim/rust/src/lib.rs",
        "clients/claim/ts/claim.ts",
        "tests/claim.test.ts",
        "package.json",
    ] {
        assert!(app.join(f).is_file(), "no {f}:\n{out}");
    }
    assert_eq!(
        members(),
        r#"members = ["circuits/*", "programs/*", "clients/*/rust"]"#
    );
    // A workspace member, not a workspace of its own.
    let verifier = std::fs::read_to_string(app.join("clients/claim/rust/Cargo.toml")).unwrap();
    assert!(!verifier.contains("[workspace]"), "{verifier}");
    let test = std::fs::read_to_string(app.join("tests/claim.test.ts")).unwrap();
    assert!(
        test.contains("{ secret: 3, result: 9 }") && test.contains("toInstructionData()"),
        "{test}"
    );

    // Adding either again is refused, not overwritten.
    let (ok, out) = xark(&["add", "program", "claim"]);
    assert!(!ok && out.contains("already exists"), "{out}");
    let (ok, out) = xark(&["add", "program", "other", "--circuit", "missing"]);
    assert!(!ok && out.contains("no circuit `missing`"), "{out}");

    // The whole workspace builds: the circuit (on the host), the program and its
    // verifier crate.
    let o = Command::new("cargo")
        .args(["check", "--workspace", "--quiet"])
        .current_dir(&app)
        .env("CARGO_TARGET_DIR", root.join("target/add-test"))
        .output()
        .expect("invoke cargo");
    assert!(
        o.status.success(),
        "the project doesn't build:\n{}",
        String::from_utf8_lossy(&o.stderr)
    );
}

/// A project is a new directory: `xark add` won't make one over an existing crate.
#[test]
fn add_refuses_to_make_a_project_in_a_crate() {
    let tmp = tempdir();
    std::fs::write(
        tmp.path().join("Cargo.toml"),
        "[package]\nname = \"mine\"\n",
    )
    .unwrap();
    let o = Command::new(crate::common::xark_bin())
        .args(["add", "circuit", "claim"])
        .current_dir(tmp.path())
        .output()
        .expect("invoke xark");
    let err = String::from_utf8_lossy(&o.stderr);
    assert!(
        !o.status.success() && err.contains("already has a Cargo.toml"),
        "{err}"
    );
    assert!(!tmp.path().join("xark.toml").exists());
}
