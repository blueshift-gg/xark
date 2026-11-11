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

/// `xark build` at a project's root.
pub fn build(root: &Path) -> i32 {
    for circuit in members(root, "circuits") {
        if let Err(code) = build_circuit(root, &circuit) {
            return code;
        }
    }
    if members(root, "programs").is_empty() {
        return 0;
    }
    build_programs(root)
}

/// One circuit: built (if it isn't current), keys (if they're missing or for
/// another circuit), then its clients.
fn build_circuit(root: &Path, circuit: &Path) -> Result<(), i32> {
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
    if !vk.is_file() || super::ensure_key_matches_circuit(&vk, &project.circuit_xbc()).is_err() {
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
    for circuit in members(root, "circuits") {
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
    let code = build(root);
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
    for circuit in members(root, "circuits") {
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
