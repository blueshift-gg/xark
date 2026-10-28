//! xark's repository tasks, run as `cargo xtask <task>` (`.cargo/config.toml`):
//!
//! * `digests`: every example circuit's R1CS digest, against `tests/stable-digests.txt`;
//! * `difftest`: every example on its own test inputs, adversarially;
//! * `publish`: the crates in dependency order: checked, rehearsed, or uploaded;
//! * `wasm`: xark-wasm's JavaScript packages, into `crates/wasm/dist/`.

mod difftest;
mod digests;
mod publish;
mod wasm;

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

use anyhow::{Context, Result, bail};
use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(about = "xark's repository tasks")]
struct Cli {
    #[command(subcommand)]
    task: Task,
}

#[derive(Subcommand)]
enum Task {
    /// Every example circuit's R1CS digest, against tests/stable-digests.txt.
    Digests(digests::Args),
    /// Every example on its own test inputs, decided by exhaustive witness search.
    Difftest(difftest::Args),
    /// The crates in dependency order: checked (--plan), rehearsed (--dry-run) or
    /// uploaded (--execute).
    Publish(publish::Args),
    /// xark-wasm's JavaScript packages (nodejs, web, bundler, module, or all of
    /// them), into crates/wasm/dist/.
    Wasm(wasm::Args),
}

fn main() -> Result<()> {
    match Cli::parse().task {
        Task::Digests(a) => digests::run(a),
        Task::Difftest(a) => difftest::run(a),
        Task::Publish(a) => publish::run(a),
        Task::Wasm(a) => wasm::run(a),
    }
}

/// The repository root.
pub fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("xtask/ is in the root")
        .to_path_buf()
}

/// The workspace's cargo target directory.
pub fn target_dir() -> PathBuf {
    std::env::var_os("CARGO_TARGET_DIR").map_or_else(|| root().join("target"), PathBuf::from)
}

/// Every example that is a circuit (its `src/lib.rs` has a `#[circuit]`), sorted.
pub fn circuits() -> Result<Vec<String>> {
    let mut names = Vec::new();
    for entry in std::fs::read_dir(root().join("examples"))? {
        let dir = entry?.path();
        let lib = std::fs::read_to_string(dir.join("src/lib.rs")).unwrap_or_default();
        if lib.contains("#[circuit]") {
            names.push(dir.file_name().unwrap().to_string_lossy().into_owned());
        }
    }
    names.sort();
    Ok(names)
}

/// Run `cmd` to completion; an error carries what it printed.
pub fn run(cmd: &mut Command) -> Result<()> {
    let out = cmd.output().with_context(|| format!("running {cmd:?}"))?;
    if !out.status.success() {
        bail!(
            "{cmd:?} failed ({})\n{}{}",
            out.status,
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    Ok(())
}

/// `cargo build -q --release <args>` in the workspace.
pub fn cargo_build(args: &[&str]) -> Result<()> {
    run(Command::new("cargo")
        .args(["build", "-q", "--release"])
        .args(args)
        .current_dir(root()))
}

/// Run `f` on every item, `jobs` at a time.
pub fn parallel<T: Send>(items: Vec<T>, jobs: usize, f: impl Fn(T) + Sync) {
    let queue = Mutex::new(items.into_iter());
    std::thread::scope(|s| {
        for _ in 0..jobs.max(1) {
            s.spawn(|| {
                loop {
                    // Take the next item, releasing the lock before running it.
                    let next = queue.lock().unwrap().next();
                    let Some(item) = next else { break };
                    f(item);
                }
            });
        }
    });
}

/// Half the cores, at most 4: what a machine running heavy builds can take.
pub fn default_jobs() -> usize {
    let cores = std::thread::available_parallelism().map_or(2, |n| n.get());
    (cores / 2).clamp(1, 4)
}
