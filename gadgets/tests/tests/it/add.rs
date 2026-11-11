//! `xark add` grows a project: a circuit, then a program verifying it, all members
//! of one Cargo workspace that builds.

use crate::common::tempdir;
use std::path::Path;
use std::process::Command;

#[test]
fn add_a_circuit_then_its_program() {
    let tmp = tempdir();
    let app = tmp.path().join("claim");
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

    let (ok, _, err) = crate::common::run(&["init", app.to_str().unwrap()]);
    assert!(ok, "{err}");
    assert!(app.join("xark.toml").is_file() && app.join(".gitignore").is_file());
    assert!(app.join("circuits/claim/src/lib.rs").is_file());
    // The project's root has the editor settings and `.gitignore`, not the circuit.
    assert!(!app.join("circuits/claim/.gitignore").exists());
    // A glob that matches nothing would be a missing path to cargo.
    assert_eq!(members(), r#"members = ["circuits/*"]"#);
    // A second circuit beside it.
    let (ok, out) = xark(&["add", "circuit", "other"]);
    assert!(ok, "{out}");
    assert!(app.join("circuits/other/src/lib.rs").is_file());

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

    // CI's `xark build --check`: a project's keys are committed in `keys/`, so a
    // fresh clone builds the same clients, and a change to them is caught.
    let (ok, out) = xark(&["build"]);
    assert!(ok, "{out}");
    assert!(
        app.join("keys/claim/pk.bin").is_file() && app.join(".github/workflows/ci.yml").is_file()
    );
    for t in ["circuits/claim/target", "circuits/other/target"] {
        std::fs::remove_dir_all(app.join(t)).unwrap();
    }
    let (ok, out) = xark(&["build", "--check"]);
    assert!(ok, "a fresh clone's build differs:\n{out}");
    let ts = app.join("clients/claim/ts/claim.ts");
    let committed = std::fs::read_to_string(&ts).unwrap();
    std::fs::write(&ts, format!("{committed}// edited\n")).unwrap();
    let (ok, out) = xark(&["build", "--check"]);
    assert!(!ok && out.contains("clients/claim/ts/claim.ts"), "{out}");
    std::fs::write(&ts, &committed).unwrap();
    // A lost key isn't quietly replaced: the committed verifier embeds it.
    std::fs::rename(app.join("keys"), app.join("keys.lost")).unwrap();
    let (ok, out) = xark(&["build"]);
    assert!(!ok && out.contains("embeds one"), "{out}");
    std::fs::rename(app.join("keys.lost"), app.join("keys")).unwrap();

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
    // A bare `cargo build-sbf` (or `cargo test`) at the root is the programs'.
    let manifest = std::fs::read_to_string(app.join("Cargo.toml")).unwrap();
    assert!(
        manifest.contains("\ndefault-members = [\"programs/*\"]\n"),
        "{manifest}"
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

/// `xark add` grows a project; outside one it says how to start one, and `xark init`
/// won't make one over an existing crate.
#[test]
fn add_needs_a_project() {
    let tmp = tempdir();
    let o = Command::new(crate::common::xark_bin())
        .args(["add", "circuit", "claim"])
        .current_dir(tmp.path())
        .output()
        .expect("invoke xark");
    let err = String::from_utf8_lossy(&o.stderr);
    assert!(
        !o.status.success() && err.contains("xark init <name>"),
        "{err}"
    );
    assert!(!tmp.path().join("xark.toml").exists());

    std::fs::write(
        tmp.path().join("Cargo.toml"),
        "[package]\nname = \"mine\"\n",
    )
    .unwrap();
    let o = Command::new(crate::common::xark_bin())
        .args(["init"])
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

/// The edges of a project: `xark init` beside files a directory already has, a
/// workspace member of your own, names that would clash, a `--check` that fails
/// partway, and a program added after a client went missing.
#[test]
fn a_project_keeps_what_isnt_xarks() {
    let tmp = tempdir();
    let app = tmp.path().join("edge");
    std::fs::create_dir_all(&app).unwrap();
    std::fs::write(app.join(".gitignore"), "dist/\n").unwrap();
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
    let (ok, out) = xark(&["init"]);
    assert!(ok, "{out}");
    let ignore = std::fs::read_to_string(app.join(".gitignore")).unwrap();
    assert!(
        ignore.starts_with("dist/\n") && ignore.contains("target/"),
        "{ignore}"
    );

    // A crate of your own in the workspace stays a member through `xark add`.
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap();
    std::fs::create_dir_all(app.join("shared/src")).unwrap();
    std::fs::write(
        app.join("shared/Cargo.toml"),
        "[package]\nname = \"shared\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    std::fs::write(app.join("shared/src/lib.rs"), "").unwrap();
    let manifest = std::fs::read_to_string(app.join("Cargo.toml"))
        .unwrap()
        .replace(
            r#"members = ["circuits/*"]"#,
            r#"members = ["circuits/*", "shared"] # and ours"#,
        )
        + &format!(
            "\n[patch.crates-io]\nxark = {{ path = \"{}\" }}\nxark-verifier = {{ path = \"{}\" }}\n",
            root.join("crates/lang").display(),
            root.join("crates/verifier").display()
        );
    std::fs::write(app.join("Cargo.toml"), manifest).unwrap();
    let (ok, out) = xark(&["add", "circuit", "second"]);
    assert!(ok, "{out}");
    // A library the circuits share sits beside them: a member, but no circuit.
    std::fs::create_dir_all(app.join("circuits/common/src")).unwrap();
    std::fs::write(
        app.join("circuits/common/Cargo.toml"),
        "[package]\nname = \"common\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    std::fs::write(
        app.join("circuits/common/src/lib.rs"),
        "pub const N: u32 = 3;\n",
    )
    .unwrap();
    let manifest = std::fs::read_to_string(app.join("Cargo.toml")).unwrap();
    assert!(
        manifest.contains(r#""shared""#) && manifest.contains("# and ours"),
        "{manifest}"
    );

    // Names a workspace can't hold, or that leave `circuits/`.
    for (args, why) in [
        (&["add", "circuit", "edge-program"][..], "can't end in"),
        (&["add", "circuit", "../escape"][..], "can't name a circuit"),
        (
            &["add", "program", "a/b", "--circuit", "edge"][..],
            "can't name a program",
        ),
    ] {
        let (ok, out) = xark(args);
        assert!(!ok && out.contains(why), "{args:?}:\n{out}");
    }
    assert!(!tmp.path().join("escape").exists());

    // A `--check` that fails partway (a key gone) still leaves the clients as they
    // were, and names the one that differs.
    let (ok, out) = xark(&["build"]);
    assert!(ok, "{out}");
    let ts = app.join("clients/edge/ts/edge.ts");
    let edited = std::fs::read_to_string(&ts).unwrap() + "// edited\n";
    std::fs::write(&ts, &edited).unwrap();
    std::fs::rename(app.join("keys/second"), tmp.path().join("second-keys")).unwrap();
    let (ok, out) = xark(&["build", "--check"]);
    assert!(!ok && out.contains("clients/edge/ts/edge.ts"), "{out}");
    assert_eq!(std::fs::read_to_string(&ts).unwrap(), edited);
    std::fs::rename(tmp.path().join("second-keys"), app.join("keys/second")).unwrap();

    // A program added after its circuit's client went missing regenerates the
    // client, and keeps the key.
    let vk = std::fs::read(app.join("keys/edge/vk.bin")).unwrap();
    std::fs::remove_dir_all(app.join("clients/edge/ts")).unwrap();
    let (ok, out) = xark(&["add", "program", "edge"]);
    assert!(ok, "{out}");
    assert!(ts.is_file());
    assert_eq!(std::fs::read(app.join("keys/edge/vk.bin")).unwrap(), vk);
}
