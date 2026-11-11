//! A project's root: `xark build`, `xark test` and `xark check` there act on all of
//! it (see `docs/projects.md`).
//!
//! * `build`: each circuit, its keys when they're missing or for an older circuit,
//!   its clients (`clients/<circuit>/{rust,ts}`), then the programs with
//!   `cargo build-sbf`, which fails on a stack frame past the SBF limit.
//! * `test`: each circuit's tests, the programs' Rust tests, then the TypeScript
//!   tests in `tests/`.
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
/// `xark = "0.4"`): a circuit can change between releases (its digest, and so its
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

/// `xark build` at a project's root. With `check` (CI), keys are never made and
/// `clients/` is left as it was: the build fails if what it generates differs.
pub fn build(root: &Path, check: bool) -> i32 {
    check_release(root);
    build_all(root, check)
}

fn build_all(root: &Path, check: bool) -> i32 {
    // What `--check` compares, and leaves as it found it on every way out: the
    // generated clients, and the workspace manifest an export keeps in sync.
    let watched = |root: &Path| {
        let mut files = snapshot(&root.join("clients"));
        if let Ok(b) = std::fs::read(root.join("Cargo.toml")) {
            files.insert(root.join("Cargo.toml"), b);
        }
        files
    };
    let before = check.then(|| watched(root));
    let mut failed = None;
    for circuit in circuits(root) {
        if let Err(code) = build_circuit(root, &circuit, check) {
            failed = Some(code);
            break;
        }
    }
    if let Some(before) = before {
        let after = watched(root);
        let changed: Vec<&PathBuf> = before
            .keys()
            .chain(after.keys().filter(|p| !before.contains_key(*p)))
            .filter(|p| before.get(*p) != after.get(*p))
            .collect();
        restore(&before, &after);
        if !changed.is_empty() {
            eprintln!(
                "{} the committed clients aren't what this build generates (run `xark \
                 build` and commit them):",
                crate::style::err("error:")
            );
            for p in &changed {
                eprintln!("  {}", p.strip_prefix(root).unwrap_or(p).display());
            }
            return 1;
        }
    }
    if let Some(code) = failed {
        return code;
    }
    if members(root, "programs").is_empty() {
        return 0;
    }
    build_programs(root)
}

/// Every file under `dir`, by path.
fn snapshot(dir: &Path) -> std::collections::BTreeMap<PathBuf, Vec<u8>> {
    let mut out = std::collections::BTreeMap::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).into_iter().flatten().flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else if let Ok(b) = std::fs::read(&p) {
                out.insert(p, b);
            }
        }
    }
    out
}

/// Put the files in `before` back, and remove the ones only `after` has.
fn restore(
    before: &std::collections::BTreeMap<PathBuf, Vec<u8>>,
    after: &std::collections::BTreeMap<PathBuf, Vec<u8>>,
) {
    for (p, b) in before {
        if let Some(dir) = p.parent() {
            let _ = std::fs::create_dir_all(dir);
        }
        let _ = std::fs::write(p, b);
    }
    for p in after.keys().filter(|p| !before.contains_key(*p)) {
        let _ = std::fs::remove_file(p);
    }
}

/// One circuit: built (if it isn't current), keys (if they're missing or for
/// another circuit, unless `check`), then its clients.
pub(crate) fn build_circuit(root: &Path, circuit: &Path, check: bool) -> Result<(), i32> {
    let dir = circuit.display().to_string();
    let code = crate::cli::cmd_build(std::slice::from_ref(&dir));
    if code != 0 {
        return Err(code);
    }
    let project = XarkProject::resolve(Some(circuit.to_path_buf())).map_err(|e| {
        eprintln!("{} {e:#}", crate::style::err("error:"));
        1
    })?;
    let vk = project.verifying_key();
    if check {
        let why = if !vk.is_file() {
            Some("has no key")
        } else if super::ensure_key_matches_circuit(&vk, &project.circuit_xbc()).is_err() {
            Some("changed since its keys were made")
        } else {
            None
        };
        if let Some(why) = why {
            eprintln!(
                "{} {} {why}: run `xark build` and commit `keys/` and `clients/`",
                crate::style::err("error:"),
                circuit.strip_prefix(root).unwrap_or(circuit).display()
            );
            return Err(1);
        }
    } else if !vk.is_file() {
        if let Err(e) = project.may_make_key() {
            eprintln!("{} {e:#}", crate::style::err("error:"));
            return Err(1);
        }
        xark(root, &["setup", &dir])?;
    } else if super::ensure_key_matches_circuit(&vk, &project.circuit_xbc()).is_err() {
        // A changed circuit needs new keys, and so a new verifier: say so, since the
        // deployed program has to change with it.
        eprintln!(
            "{} {} changed since its keys were made: making new ones, so its verifier \
             changes too (deploy the program again)",
            crate::style::warn("warning:"),
            circuit.display()
        );
        xark(root, &["setup", &dir])?;
    }
    xark(root, &["export", &dir])?;
    xark(root, &["client", &dir])
}

/// The programs, with `cargo build-sbf` at the root (the workspace's
/// `default-members` are the programs, so the circuits' host dependencies stay out
/// of it). Its output is shown; a stack frame past the SBF limit of 4 KiB fails the
/// build, which `cargo build-sbf` only warns about.
fn build_programs(root: &Path) -> i32 {
    eprintln!(
        "{} building the programs (cargo build-sbf)",
        crate::style::tag()
    );
    let out = match Command::new("cargo")
        .arg("build-sbf")
        .current_dir(root)
        .output()
    {
        Ok(o) => o,
        Err(e) => {
            eprintln!(
                "xark: couldn't run `cargo build-sbf` ({e}): install the Solana CLI \
                 (https://solana.com/docs/intro/installation)"
            );
            return 1;
        }
    };
    let log =
        String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr);
    eprint!("{log}");
    if !out.status.success() {
        return out.status.code().unwrap_or(1);
    }
    if log.contains("overflows the maximum allowed frame space") {
        eprintln!(
            "{} a stack frame is past the SBF limit of 4 KiB (the warning above): the \
             program would overwrite its own stack at run time. Move the big work out \
             of line with #[inline(never)], as the generated `verify` is.",
            crate::style::err("error:")
        );
        return 1;
    }
    0
}

/// `xark test` at a project's root: `forwarded` goes to each circuit's `cargo test`.
pub fn test(root: &Path, forwarded: &[String]) -> i32 {
    check_release(root);
    for circuit in circuits(root) {
        let mut args = vec![circuit.display().to_string()];
        args.extend(forwarded.iter().cloned());
        let code = crate::cli::cmd_test(&args);
        if code != 0 {
            return code;
        }
    }
    if members(root, "programs").is_empty() {
        return 0;
    }
    // The programs' tests need them built, and their clients current.
    let code = build_all(root, false);
    if code != 0 {
        return code;
    }
    eprintln!("{} running the programs' Rust tests", crate::style::tag());
    if let Err(code) = run(root, Command::new("cargo").arg("test")) {
        return code;
    }
    if !root.join("package.json").is_file() {
        return 0;
    }
    if !root.join("node_modules").is_dir() {
        eprintln!(
            "xark: the TypeScript tests need their packages: run `npm install`, then `xark test` \
             again"
        );
        return 1;
    }
    eprintln!(
        "{} running the TypeScript tests (npm test)",
        crate::style::tag()
    );
    match run(root, Command::new("npm").arg("test")) {
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
