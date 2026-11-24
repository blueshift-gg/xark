//! A project's root: `xark build`, `xark test` and `xark check` there act on all of
//! it (see `docs/projects.md`).
//!
//! * `build`: each circuit and its clients (`clients/<circuit>/{rust,ts}`). A
//!   missing key is bootstrapped; a changed plain dev key is rotated; other keys
//!   are read-only. Programs are built by their framework outside xark.
//! * `test`: each circuit's tests and those of a library beside them. Program
//!   tests are run by the framework (`npm test` for Pinocchio's LiteSVM test).
//! * `check`: what rust-analyzer runs. `cargo check` over the workspace once, then
//!   xark's own validation of each circuit.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::xark_project::{PROJECT_FILE, XarkProject};

/// The project at `arg` (a directory argument, or the current directory when it's
/// `None` or `.`), when that's a project's root.
pub fn root_at(arg: Option<&str>) -> Option<PathBuf> {
    let cwd = std::env::current_dir().ok()?;
    let dir = match arg {
        None | Some(".") => cwd,
        Some(a) => cwd.join(a),
    };
    dir.join(PROJECT_FILE).is_file().then_some(dir)
}

/// Warn when this `xark` is another release than the project's (`xark.toml`'s
/// `xark = "0.5"`): a circuit can change between releases (its digest, and so its
/// keys and verifier), so the project builds with the one it records.
pub fn check_release(root: &Path) {
    let Ok(text) = std::fs::read_to_string(root.join(PROJECT_FILE)) else {
        return;
    };
    let pinned = text.lines().find_map(|l| {
        let v = l
            .trim()
            .strip_prefix("xark")?
            .trim_start()
            .strip_prefix('=')?;
        let v = v.split('#').next()?.trim().trim_matches('"');
        Some(xark_ir::major_minor(v))
    });
    let this = xark_ir::major_minor(env!("CARGO_PKG_VERSION"));
    if let Some(pinned) = pinned
        && pinned != this
    {
        eprintln!(
            "{} this project is made with xark {pinned} ({PROJECT_FILE}), and this xark is \
             {this}: install that release (`cargo install xark-cli --version {pinned}.*`), or \
             move the project to {this} on purpose and update `xark` in {PROJECT_FILE}",
            crate::style::warn("warning:")
        );
    }
}

/// The project's circuits: the crates in `circuits/` with a `#[circuit]`. A
/// library beside them (helpers the circuits share) is a member of the workspace,
/// but nothing xark builds.
pub fn circuits(root: &Path) -> Vec<PathBuf> {
    members(root, "circuits")
        .into_iter()
        .filter(|c| has_circuit(&c.join("src")))
        .collect()
}

/// Whether a source file under `dir` declares a `#[circuit]`.
fn has_circuit(dir: &Path) -> bool {
    std::fs::read_dir(dir)
        .into_iter()
        .flatten()
        .flatten()
        .any(|e| {
            let p = e.path();
            if p.is_dir() {
                has_circuit(&p)
            } else {
                p.extension().is_some_and(|x| x == "rs")
                    && std::fs::read_to_string(&p).is_ok_and(|t| t.contains("#[circuit]"))
            }
        })
}

/// The circuit a directory argument means: at a project's root with one circuit,
/// that circuit's crate.
pub fn only_circuit(arg: &str) -> Option<PathBuf> {
    match circuits(&root_at(Some(arg))?).as_slice() {
        [one] => Some(one.clone()),
        _ => None,
    }
}

/// The crates in `root/<group>/`, by name.
pub fn members(root: &Path, group: &str) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = std::fs::read_dir(root.join(group))
        .into_iter()
        .flatten()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.join("Cargo.toml").is_file())
        .collect();
    out.sort();
    out
}

/// `xark build` at a project's root. A missing key is bootstrapped and a changed
/// plain dev key is rotated; other keys are read-only. With `check` (CI), the
/// generated clients are staged and compared: the build fails if they differ.
pub fn build(root: &Path, check: bool) -> i32 {
    check_release(root);
    build_all(root, check)
}

fn build_all(root: &Path, check: bool) -> i32 {
    if check {
        // `--check` writes nothing that is committed: verify the workspace members
        // and stage the generated clients under target/ for comparison.
        if let Err(e) = crate::xark_project::check_members(root) {
            eprintln!("{} {e:#}", crate::style::err("error:"));
            return 1;
        }
    } else {
        // A program may already depend on a circuit's verifier crate before its
        // first build (moved in from elsewhere): cargo can't load the workspace
        // without it, so the circuit couldn't build to make it. A placeholder stands
        // in until the export below replaces it.
        for circuit in circuits(root) {
            if let Some(name) = crate::xark_project::read_pkg_name(&circuit) {
                let dir = root.join("clients").join(&name).join("rust");
                if !dir.join("Cargo.toml").exists() {
                    let _ = std::fs::create_dir_all(dir.join("src"));
                    let _ = std::fs::write(
                        dir.join("Cargo.toml"),
                        format!(
                            "# Auto-generated by `xark export` (a placeholder until it runs).\n\
                             [package]\nname = \"{}\"\nversion = \"0.1.0\"\n\
                             edition = \"2024\"\n",
                            super::export::client_crate_name(&name)
                        ),
                    );
                    let _ = std::fs::write(
                        dir.join("src/lib.rs"),
                        "//! Auto-generated by `xark export` (a placeholder until it runs).\n",
                    );
                }
            }
        }
        if let Err(e) = crate::xark_project::sync_members(root) {
            eprintln!("{} {e:#}", crate::style::err("error:"));
            return 1;
        }
    }
    for circuit in circuits(root) {
        if let Err(code) = build_circuit(root, &circuit, check) {
            return code;
        }
    }
    0
}

/// Bootstrap or rotate a circuit's dev key from this machine's randomness, as
/// `xark build` does: never a phase-2 key from a stray `.ptau`. Run in-process
/// so asking for it needn't be a flag on the CLI.
fn setup_dev_key(circuit: &Path) -> Result<(), i32> {
    super::setup::make(super::setup::SetupArgs {
        path: Some(circuit.to_path_buf()),
        out: None,
        without_ptau: true,
        deterministic_rng: None,
        ptau_file: None,
        phase2_seed: None,
        uncompressed: false,
        r1cs_form: super::setup::R1csForm::Auto,
        domain: super::setup::QapDomain::Auto,
    })
    .map_err(|e| {
        eprintln!("{} {e:#}", crate::style::err("error:"));
        1
    })?;
    Ok(())
}

/// One circuit: built (if it isn't current), its key bootstrapped or a dev key
/// rotated if needed, then its clients. In `check` mode the clients are staged
/// under `target/` and compared, so nothing committed is written.
pub(crate) fn build_circuit(root: &Path, circuit: &Path, check: bool) -> Result<(), i32> {
    let dir = circuit.display().to_string();
    let project = XarkProject::resolve(Some(circuit.to_path_buf())).map_err(|e| {
        eprintln!("{} {e:#}", crate::style::err("error:"));
        1
    })?;
    let name = circuit
        .strip_prefix(root)
        .unwrap_or(circuit)
        .display()
        .to_string();
    if crate::cli::stale_build(&project.xark_dir, "circuit.xbc", Some("bn254")).is_some() {
        let code = crate::cli::cmd_build(&dir);
        if code != 0 {
            return Err(code);
        }
    } else {
        eprintln!(
            "{} circuit `{name}` is unchanged since the last build",
            crate::style::tag()
        );
    }
    let state = key_state(&project);
    if check {
        let why = match state {
            KeyState::Fits => None,
            KeyState::None => Some("has no key".to_string()),
            KeyState::Changed => Some("changed since its keys were made".to_string()),
            KeyState::Unknown => Some("has no readable build".to_string()),
            KeyState::Unpaired => Some(format!(
                "has no `circuit.xbc` beside its key (the build it was made from, in {})",
                super::shown(&project.key_dir())
            )),
            KeyState::BuildLost => Some(
                "has a key made from another build of it, which isn't kept beside the key"
                    .to_string(),
            ),
        };
        if let Some(why) = why {
            let fix = match state {
                KeyState::BuildLost => {
                    format!("restore it, or make a new key with `xark setup {name}`")
                }
                KeyState::Unknown => format!("run `xark build {name}`"),
                _ => format!("run `xark setup {name}`"),
            };
            eprintln!(
                "{} {name} {why}: {fix}, and commit `keys/` and `clients/`",
                crate::style::err("error:")
            );
            return Err(1);
        }
        check_key_metadata(&project)?;
        return check_clients(root, circuit);
    }
    match state {
        KeyState::Fits => {}
        KeyState::None => {
            if let Err(e) = project.may_make_key() {
                eprintln!("{} {e:#}", crate::style::err("error:"));
                return Err(1);
            }
            // Bootstrap a dev key, never a phase-2 key from a stray `.ptau`:
            // `xark setup` prints how it was made.
            setup_dev_key(circuit)?;
        }
        KeyState::Unpaired => {
            // Made from this very build: keep it beside the key.
            let keyed = project.key_dir().join("circuit.xbc");
            if let Err(e) = std::fs::copy(project.circuit_xbc(), &keyed) {
                eprintln!("xark: writing {}: {e}", keyed.display());
                return Err(1);
            }
        }
        KeyState::Unknown => {
            eprintln!(
                "{} {name} has no readable build: run `xark build {name}` and try again",
                crate::style::err("error:")
            );
            return Err(1);
        }
        KeyState::BuildLost => {
            eprintln!(
                "{} the key in {} was made from another build of {name} (the same \
                 constraints, compiled differently), and that build isn't kept beside it \
                 as `circuit.xbc`. A key proves only with the build it was made from: \
                 restore that file, or make a new key with `xark setup {name}` (the \
                 deployed program then needs the new verifier)",
                crate::style::err("error:"),
                super::shown(&project.key_dir())
            );
            return Err(1);
        }
        KeyState::Changed => {
            if plain_dev_key(&project) {
                eprintln!(
                    "{} {name} changed since its keys were made: making new ones, so its \
                     verifier changes too (deploy the program again)",
                    crate::style::warn("warning:")
                );
                setup_dev_key(circuit)?;
            } else {
                eprintln!(
                    "{} {name} changed since its keys were made: run `xark setup {name}` \
                     (or `xark ceremony`) and `xark build` again; its verifier changes too \
                     (deploy the program again)",
                    crate::style::err("error:")
                );
                return Err(1);
            }
        }
    }
    xark(root, &["export", &dir])?;
    xark(root, &["client", &dir])
}

/// Stage this circuit's clients under `target/xark/check/` and compare them with
/// the committed `clients/<pkg>/`.
fn check_clients(root: &Path, circuit: &Path) -> Result<(), i32> {
    let Some(pkg) = crate::xark_project::read_pkg_name(circuit) else {
        eprintln!(
            "{} can't read the package name of {}",
            crate::style::err("error:"),
            circuit.display()
        );
        return Err(2);
    };
    let committed = root.join("clients").join(&pkg);
    let check_root = root.join("target/xark/check");
    let stage_root = check_root.join(format!("{pkg}-{}", std::process::id()));
    if !stage_root.starts_with(&check_root) {
        eprintln!(
            "{} refusing to stage outside {}",
            crate::style::err("error:"),
            check_root.display()
        );
        return Err(2);
    }
    let staged = stage_root.join("clients").join(&pkg);
    if let Err(e) = std::fs::remove_dir_all(&stage_root)
        && e.kind() != std::io::ErrorKind::NotFound
    {
        eprintln!("xark: removing {}: {e}", stage_root.display());
        return Err(1);
    }
    let rust = staged.join("rust");
    let ts = staged.join("ts");
    if let Err(e) = std::fs::create_dir_all(&ts) {
        eprintln!("xark: creating {}: {e}", ts.display());
        return Err(1);
    }
    // Seed the staged crate with the committed sample; the generator writes the
    // rest.
    for sample in ["proof.solana.bin", "public_inputs.solana.bin"] {
        let from = committed.join("rust").join(sample);
        if from.is_file() {
            let _ = std::fs::create_dir_all(&rust);
            let _ = std::fs::copy(from, rust.join(sample));
        }
    }

    // The name the committed crate has: an earlier export keeps its own (0.4.0
    // named it `<name>-verifier`), so `--check` must ask for that one to compare.
    let crate_name = crate::xark_project::read_pkg_name(&committed.join("rust"))
        .unwrap_or_else(|| super::export::client_crate_name(&pkg));
    let dir = circuit.display().to_string();
    let rust_out = rust.display().to_string();

    xark(
        root,
        &[
            "export",
            dir.as_str(),
            "--out",
            rust_out.as_str(),
            "--crate-name",
            crate_name.as_str(),
            "--member",
        ],
    )?;

    let ts_out = ts.display().to_string();

    xark(root, &["client", dir.as_str(), "--out", ts_out.as_str()])?;

    let changes = diff_tree(&committed, &staged);
    if !changes.is_empty() {
        eprintln!(
            "{} the committed clients aren't what this build generates (run `xark build` \
             and commit them):",
            crate::style::err("error:")
        );
        for (kind, path) in changes {
            eprintln!("  {kind} clients/{pkg}/{}", path.display());
        }
        return Err(1);
    }

    let _ = std::fs::remove_dir_all(&stage_root);

    Ok(())
}

/// File-level differences between a committed tree and a staged one.
fn diff_tree(committed: &Path, staged: &Path) -> Vec<(&'static str, PathBuf)> {
    fn files(root: &Path) -> std::collections::BTreeMap<PathBuf, Vec<u8>> {
        let mut out = std::collections::BTreeMap::new();
        let mut stack = vec![root.to_path_buf()];
        while let Some(dir) = stack.pop() {
            for entry in std::fs::read_dir(&dir).into_iter().flatten().flatten() {
                let path = entry.path();
                let Ok(meta) = std::fs::symlink_metadata(&path) else {
                    continue;
                };
                if meta.is_dir() {
                    stack.push(path);
                } else if meta.is_file()
                    && let Ok(bytes) = std::fs::read(&path)
                    && let Ok(rel) = path.strip_prefix(root)
                {
                    out.insert(rel.to_path_buf(), bytes);
                }
            }
        }
        out
    }
    let committed = files(committed);
    let staged = files(staged);
    let mut changes = Vec::new();
    for (path, bytes) in &staged {
        match committed.get(path) {
            Some(old) if old == bytes => {}
            Some(_) => changes.push(("changed", path.clone())),
            None => changes.push(("new", path.clone())),
        }
    }
    for path in committed.keys().filter(|p| !staged.contains_key(*p)) {
        changes.push(("missing", path.clone()));
    }
    changes
}

/// A circuit's key, against its current build.
enum KeyState {
    /// No key yet.
    None,
    /// The key and the build it was made from (`circuit.xbc` beside it), whose
    /// constraints are the current build's.
    Fits,
    /// A key made from this very build, without the build beside it yet.
    Unpaired,
    /// A key made from another build of the same constraints, which isn't kept: a key
    /// proves only with its own build.
    BuildLost,
    /// The constraints changed since the key was made.
    Changed,
    /// There is no readable build to compare the key with.
    Unknown,
}

/// Verify the metadata still describes this key and build. `--check` uses this to
/// catch an edited metadata.json or verifying key; it never makes a key.
fn check_key_metadata(project: &XarkProject) -> Result<(), i32> {
    let path = project.key_dir().join("metadata.json");
    let Ok(text) = std::fs::read_to_string(&path) else {
        return Ok(());
    };
    let Ok(meta) = serde_json::from_str::<serde_json::Value>(&text) else {
        eprintln!(
            "{} {} is not valid JSON",
            crate::style::err("error:"),
            path.display()
        );
        return Err(1);
    };
    if let Some(expected) = meta.get("verifying_key_sha256").and_then(|v| v.as_str()) {
        let Ok(vk) = std::fs::read(project.verifying_key()) else {
            eprintln!(
                "{} can't read {}",
                crate::style::err("error:"),
                project.verifying_key().display()
            );
            return Err(1);
        };
        let actual = super::sha256_hex(&vk);
        if actual != expected {
            eprintln!(
                "{} {} doesn't match the key it records (metadata says {expected})",
                crate::style::err("error:"),
                path.display()
            );
            return Err(1);
        }
    }
    if let Some(expected) = meta.get("digest").and_then(|v| v.as_str()) {
        let Ok(xbc) = std::fs::read(project.circuit_xbc()) else {
            eprintln!(
                "{} can't read {}",
                crate::style::err("error:"),
                project.circuit_xbc().display()
            );
            return Err(1);
        };
        let actual = super::r1cs_digest(&xbc);
        if actual != expected {
            eprintln!(
                "{} {} is for another build (metadata says {expected})",
                crate::style::err("error:"),
                path.display()
            );
            return Err(1);
        }
    }
    Ok(())
}

/// A plain OS-random single-party key, the kind a local build bootstraps. A
/// ceremony, phase-2, seeded, or unknown key is not rotated by a build.
fn plain_dev_key(project: &XarkProject) -> bool {
    plain_dev_key_dir(&project.key_dir())
}

fn plain_dev_key_dir(dir: &Path) -> bool {
    let Ok(text) = std::fs::read_to_string(dir.join("metadata.json")) else {
        return false;
    };
    let Ok(meta) = serde_json::from_str::<serde_json::Value>(&text) else {
        return false;
    };
    meta.get("setup_mode").and_then(|m| m.as_str()) == Some("single-party")
        && meta.get("production_safe").and_then(|b| b.as_bool()) != Some(true)
        && meta
            .get("deterministic_rng_seed")
            .is_none_or(serde_json::Value::is_null)
}

fn key_state(project: &XarkProject) -> KeyState {
    if !project.verifying_key().is_file() {
        return KeyState::None;
    }
    let Ok(build) = std::fs::read(project.circuit_xbc()) else {
        return KeyState::Unknown;
    };
    let keyed = project.key_dir().join("circuit.xbc");
    if let Ok(kept) = std::fs::read(&keyed) {
        return if super::r1cs_digest(&kept) == super::r1cs_digest(&build) {
            KeyState::Fits
        } else {
            KeyState::Changed
        };
    }
    match super::key_fit(&project.verifying_key(), &build) {
        super::KeyFit::Same => KeyState::Unpaired,
        super::KeyFit::SameCircuit => KeyState::BuildLost,
        super::KeyFit::Different => KeyState::Changed,
    }
}

/// `xark test` at a project's root. `forwarded` goes to each circuit's
/// `cargo test`; `check` verifies the committed clients/keys instead of
/// refreshing them.
pub fn test(root: &Path, forwarded: &[String], check: bool) -> i32 {
    check_release(root);
    if check {
        let code = build(root, true);
        if code != 0 {
            return code;
        }
    }
    circuit_tests(root, forwarded)
}

/// The circuit-side tests at a project's root.
fn circuit_tests(root: &Path, forwarded: &[String]) -> i32 {
    let circuit_crates = circuits(root);
    for circuit in &circuit_crates {
        let code = crate::cli::cmd_test(&circuit.display().to_string(), forwarded);
        if code != 0 {
            return code;
        }
    }
    // A library beside the circuits isn't a circuit `xark test` tests above, but its
    // tests are still circuit-side: run them without the programs' fat LTO.
    let libraries: Vec<PathBuf> = members(root, "circuits")
        .into_iter()
        .filter(|c| !circuit_crates.contains(c))
        .collect();
    if libraries.is_empty() {
        return 0;
    }
    eprintln!(
        "{} running the circuit libraries' Rust tests",
        crate::style::tag()
    );
    let mut cargo = Command::new("cargo");
    cargo
        .args(["test", "--release"])
        .env("CARGO_PROFILE_RELEASE_LTO", "false")
        .env("CARGO_PROFILE_RELEASE_CODEGEN_UNITS", "16");
    let mut picked = false;
    for dir in libraries {
        if let Some(name) = crate::xark_project::read_pkg_name(&dir) {
            cargo.args(["-p", &name]);
            picked = true;
        }
    }
    if !picked {
        return 0;
    }
    match run(root, &mut cargo) {
        Ok(()) => 0,
        Err(code) => code,
    }
}

/// `xark check` at a project's root: `cargo check` over the workspace, then each
/// circuit's validation.
pub fn check(root: &Path, json: bool) -> i32 {
    let mut seen = std::collections::HashSet::new();
    if json {
        match crate::cli::host_check_json(root, true) {
            Some((true, rendered)) => seen = rendered,
            Some((false, _)) => return 1,
            None => {}
        }
    }
    let mut code = 0;
    for circuit in circuits(root) {
        let c = crate::cli::check_circuit(&circuit, json, seen.clone());
        if c != 0 {
            code = c;
        }
    }
    code
}

/// Run `xark` (this binary) with `args` in `dir`.
fn xark(dir: &Path, args: &[&str]) -> Result<(), i32> {
    let exe = std::env::current_exe().map_err(|_| 1)?;
    run(
        dir,
        Command::new(exe).args(args).env(crate::style::NESTED, "1"),
    )
}

fn run(dir: &Path, cmd: &mut Command) -> Result<(), i32> {
    match cmd.current_dir(dir).status() {
        Ok(s) if s.success() => Ok(()),
        Ok(s) => Err(s.code().unwrap_or(1)),
        Err(e) => {
            eprintln!("xark: couldn't run {:?}: {e}", cmd.get_program());
            Err(1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::plain_dev_key_dir;

    fn metadata(json: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "xark-key-kind-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("metadata.json"), json).unwrap();
        dir
    }

    #[test]
    fn only_an_unseeded_single_party_key_is_a_dev_key() {
        let dir = metadata(
            r#"{"setup_mode":"single-party","production_safe":false,"deterministic_rng_seed":null}"#,
        );
        assert!(plain_dev_key_dir(&dir));
        std::fs::remove_dir_all(dir).unwrap();

        let dir = metadata(
            r#"{"setup_mode":"single-party","production_safe":false,"deterministic_rng_seed":7}"#,
        );
        assert!(!plain_dev_key_dir(&dir));
        std::fs::remove_dir_all(dir).unwrap();

        for json in [
            r#"{"setup_mode":"phase2-from-ptau","production_safe":true}"#,
            r#"{"setup_mode":"phase2-from-ptau+mpc[1 contributor]","production_safe":true}"#,
            r#"{"setup_mode":"phase2-from-ptau+mpc[2 contributors]","production_safe":true}"#,
            r#"{"production_safe":false}"#,
        ] {
            let dir = metadata(json);
            assert!(!plain_dev_key_dir(&dir), "{json}");
            std::fs::remove_dir_all(dir).unwrap();
        }
    }
}
