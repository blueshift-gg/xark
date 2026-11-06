//! `cargo xtask ci`: every check a pull request gets, on this machine, side by side.
//!
//! First, in order: `cargo fmt --check`, clippy, and a build of every test binary (so
//! the steps after don't queue on one `target/` lock). Then every independent step at
//! once, each logging to `target/ci/<step>.log`: the workspace and `crates/lang`
//! tests (nextest, and their doctests), the digests, the Lean exports and coverage,
//! the minimizer certificates, the publish plan, xark-wasm's wasm build, the
//! generated clients, the Lean proofs and, after them, xtask's ignored tests (they
//! need the Lean build). Steps whose tools aren't installed (`lake`, `npm`,
//! `cargo build-sbf`) are skipped and say so. Keyed rows are pinned under one rustc
//! ([`KEYED_TOOLCHAIN`], as CI's `keyed-rows` job), so those steps run under it.
//!
//! `--since <REF>` runs only the steps the files changed since `REF` (committed or
//! not, and untracked ones) can affect ([`affected`]); fmt and clippy always run.

use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use anyhow::{Result, bail};

/// The rustc keyed digests are pinned under (`.github/workflows/ci.yml`'s
/// `keyed-rows` job).
const KEYED_TOOLCHAIN: &str = "1.99.1";

#[derive(clap::Args)]
pub struct Args {
    /// Run only these steps (comma-separated; `--list` names them).
    #[arg(long, value_delimiter = ',')]
    only: Vec<String>,
    /// Skip these steps (comma-separated).
    #[arg(long, value_delimiter = ',')]
    skip: Vec<String>,
    /// Steps run at once (default: all of them).
    #[arg(long)]
    jobs: Option<usize>,
    /// Name the steps and exit.
    #[arg(long)]
    list: bool,
    /// Only the steps the files changed since this git ref can affect (`HEAD`: the
    /// uncommitted changes).
    #[arg(long, value_name = "REF")]
    since: Option<String>,
}

/// Every step after the build ones.
const ALL: &[&str] = &[
    "workspace",
    "lang",
    "sbpf",
    "digests",
    "lean-check",
    "coverage",
    "minimize",
    "publish",
    "wasm32",
    "clients",
    "lake",
    "xtask-ignored",
];

/// The steps a change to `path` can affect. What compiles circuits (the language,
/// the frontend, the IR, the macros, the gadgets, the examples) affects nearly all of
/// them; the prover side the tests, the wasm build, the clients and the on-chain
/// tests; `formal/` the Lean steps; xtask its own tasks. Docs affect none; anything
/// not listed, all.
fn affected(path: &str) -> &'static [&'static str] {
    const CIRCUITS: &[&str] = &[
        "workspace",
        "lang",
        "digests",
        "lean-check",
        "coverage",
        "minimize",
        "wasm32",
        "clients",
        "sbpf",
        "publish",
    ];
    const PROVER: &[&str] = &["workspace", "wasm32", "clients", "sbpf", "publish"];
    const LEAN: &[&str] = &[
        "lake",
        "xtask-ignored",
        "lean-check",
        "coverage",
        "minimize",
    ];
    const XTASK: &[&str] = &[
        "workspace",
        "digests",
        "lean-check",
        "coverage",
        "minimize",
        "publish",
        "lake",
        "xtask-ignored",
    ];
    let top = |p: &str| path.starts_with(p);
    if path.ends_with(".md") || top("docs/") || top("LICENSE") || top(".github/") {
        &[]
    } else if [
        "crates/lang/",
        "crates/frontend/",
        "crates/ir/",
        "crates/macros/",
    ]
    .iter()
    .any(|p| top(p))
        || top("gadgets/")
        || top("examples/")
        || top("tests/stable-digests.txt")
    {
        CIRCUITS
    } else if [
        "crates/backend/",
        "crates/cli/",
        "crates/groth16/",
        "crates/prover/",
        "crates/schema/",
        "crates/verifier/",
        "crates/wasm/",
    ]
    .iter()
    .any(|p| top(p))
    {
        PROVER
    } else if top("crates/test-harness/") {
        // The gadget crates' and crates/lang's tests compile through it.
        &["workspace", "lang"]
    } else if top("formal/") {
        LEAN
    } else if top("xtask/") {
        XTASK
    } else if top("clients/") {
        &["clients"]
    } else {
        ALL
    }
}

/// The files changed since `base`: committed, staged, unstaged and untracked.
fn changed_since(base: &str) -> Result<Vec<String>> {
    let git = |args: &[&str]| -> Result<Vec<String>> {
        let out = Command::new("git")
            .args(args)
            .current_dir(crate::root())
            .output()?;
        if !out.status.success() {
            bail!(
                "git {}: {}",
                args.join(" "),
                String::from_utf8_lossy(&out.stderr).trim()
            );
        }
        Ok(String::from_utf8(out.stdout)?
            .lines()
            .map(str::to_string)
            .collect())
    };
    let mut files = git(&["diff", "--name-only", base])?;
    files.extend(git(&["ls-files", "--others", "--exclude-standard"])?);
    files.sort();
    files.dedup();
    Ok(files)
}

/// One step: a shell command run from the repository root, `after` another step.
struct Step {
    name: &'static str,
    what: &'static str,
    cmd: String,
    /// Needs this tool on `PATH` (or as a cargo subcommand); skipped without it.
    needs: Option<&'static str>,
    after: Option<&'static str>,
}

fn steps() -> Vec<Step> {
    let keyed = format!("RUSTUP_TOOLCHAIN={KEYED_TOOLCHAIN}");
    let step = |name, what, cmd: String, needs, after| Step {
        name,
        what,
        cmd,
        needs,
        after,
    };
    vec![
        step(
            "workspace",
            "workspace tests (nextest) and doctests",
            // The Solana tests are their own step (they need `cargo build-sbf`).
            "cargo nextest run --release --no-fail-fast --workspace \
             -E 'not (binary(sbpf) | binary(differential_alt_bn128))' \
             && cargo test -q --release --doc --workspace"
                .into(),
            Some("cargo-nextest"),
            None,
        ),
        step(
            "lang",
            "crates/lang suite (nextest) and doctests",
            "cd crates/lang && cargo nextest run --release --no-fail-fast \
             && cargo test -q --release --doc"
                .into(),
            Some("cargo-nextest"),
            None,
        ),
        step(
            "sbpf",
            "on-chain verifier tests (Mollusk) and the alt_bn128 differential",
            "cargo test --release -p xark-tests --test sbpf --test differential_alt_bn128".into(),
            Some("cargo-build-sbf"),
            None,
        ),
        step(
            "digests",
            "circuit digests, keyed and flat",
            format!("{keyed} cargo xtask digests --check"),
            None,
            None,
        ),
        step(
            "lean-check",
            "proven templates match the code",
            format!("{keyed} cargo xtask lean-export --check"),
            None,
            None,
        ),
        step(
            "coverage",
            "every call of a proven gadget is covered",
            format!("{keyed} cargo xtask lean-export --coverage"),
            None,
            None,
        ),
        step(
            "minimize",
            "keyed rows certified against the minimizer",
            format!("{keyed} cargo xtask minimize-check"),
            Some("lake"),
            None,
        ),
        step(
            "publish",
            "every crate can publish",
            "cargo xtask publish --plan".into(),
            None,
            None,
        ),
        step(
            "wasm32",
            "xark-wasm builds for wasm32",
            "cargo build -q --release -p xark-wasm --target wasm32-unknown-unknown".into(),
            None,
            None,
        ),
        step(
            "clients",
            "generated TypeScript clients",
            // Its setup builds `xark` with `-p xark-cli`, whose features differ from the
            // workspace build's: in the shared `target/` it would relink the binary the
            // workspace tests are running (`spawn xark: No such file`).
            format!(
                "cd clients/check && CARGO_TARGET_DIR={} npm test",
                crate::target_dir().join("ci-clients").display()
            ),
            Some("npm"),
            None,
        ),
        step(
            "lake",
            "Lean proofs, axioms, circuit hashes",
            // mathlib's prebuilt cache first (a fresh clone would build ~8,000 of its
            // modules); offline, the build carries on without it.
            "cd formal && (lake exe cache get || true) && lake build \
             && lake env lean AxiomCheck.lean && lake env lean CircuitHash.lean"
                .into(),
            Some("lake"),
            None,
        ),
        step(
            "xtask-ignored",
            "xtask's ignored tests (mutation tests over the Lean build)",
            "cargo test -q --release -p xtask -- --ignored".into(),
            Some("lake"),
            Some("lake"),
        ),
    ]
}

pub fn run(args: Args) -> Result<()> {
    let all = steps();
    let since: Option<Vec<&str>> = match &args.since {
        Some(base) => {
            let files = changed_since(base)?;
            let mut steps: Vec<&str> = files
                .iter()
                .flat_map(|f| affected(f).iter().copied())
                .collect();
            steps.sort();
            steps.dedup();
            println!(
                "{} files changed since {base}: {}",
                files.len(),
                if steps.is_empty() {
                    "fmt and clippy only".to_string()
                } else {
                    steps.join(", ")
                }
            );
            Some(steps)
        }
        None => None,
    };
    for n in args.only.iter().chain(&args.skip) {
        if !all.iter().any(|s| s.name == n) {
            bail!("no step `{n}` (`cargo xtask ci --list` names them)");
        }
    }
    let chosen: Vec<Step> = all
        .into_iter()
        .filter(|s| args.only.is_empty() || args.only.iter().any(|n| n == s.name))
        .filter(|s| !args.skip.iter().any(|n| n == s.name))
        .filter(|s| since.as_ref().is_none_or(|st| st.contains(&s.name)))
        .collect();
    if args.list {
        for s in &chosen {
            println!("{:14} {}", s.name, s.what);
        }
        return Ok(());
    }
    let logs = crate::target_dir().join("ci");
    std::fs::create_dir_all(&logs)?;
    let t0 = Instant::now();

    // Fast checks, then every test binary built once, in order.
    let mut prep = vec![
        ("fmt", "cargo fmt --all --check".to_string()),
        (
            "clippy",
            "cargo clippy -q --workspace --all-targets -- -D warnings".into(),
        ),
    ];
    let wants = |n: &str| chosen.iter().any(|s| s.name == n);
    if wants("workspace") || wants("sbpf") {
        prep.push((
            "build-tests",
            "cargo test -q --release --workspace --no-run".into(),
        ));
    }
    if wants("lang") {
        prep.push((
            "build-lang",
            "cd crates/lang && cargo test -q --release --no-run".into(),
        ));
    }
    if wants("xtask-ignored") || chosen.iter().any(|s| s.cmd.contains("cargo xtask")) {
        prep.push((
            "build-xtask",
            "cargo test -q --release -p xtask --no-run".into(),
        ));
    }
    if chosen.iter().any(|s| s.cmd.contains(KEYED_TOOLCHAIN)) && !has_toolchain(KEYED_TOOLCHAIN) {
        bail!(
            "the keyed-digest steps run under rustc {KEYED_TOOLCHAIN}: `rustup toolchain \
             install {KEYED_TOOLCHAIN} --target wasm32-unknown-unknown`, or `--skip` them"
        );
    }
    let mut results: Vec<(String, Outcome, Duration)> = Vec::new();
    for (name, cmd) in prep {
        let (o, d) = run_one(name, &cmd, &logs);
        report(name, &o, d, &logs);
        let failed = matches!(o, Outcome::Fail);
        results.push((name.to_string(), o, d));
        if failed {
            summary(&results, t0);
            bail!("{name} failed; the steps after it didn't run");
        }
    }

    let done = Mutex::new(Vec::<(String, Outcome, Duration)>::new());
    let pending = Mutex::new(chosen);
    let jobs = args.jobs.unwrap_or(usize::MAX).max(1);
    std::thread::scope(|s| {
        for _ in 0..jobs.min(pending.lock().unwrap().len()) {
            s.spawn(|| {
                loop {
                    // The next step whose `after` is done (or isn't run at all).
                    let next = {
                        let mut p = pending.lock().unwrap();
                        if p.is_empty() {
                            break;
                        }
                        let finished = done.lock().unwrap();
                        let ready = p.iter().position(|st| {
                            st.after.is_none_or(|a| {
                                finished.iter().any(|(n, ..)| n == a)
                                    || !p.iter().any(|q| q.name == a)
                            })
                        });
                        ready.map(|i| p.remove(i))
                    };
                    let Some(st) = next else {
                        std::thread::sleep(Duration::from_millis(200));
                        continue;
                    };
                    let (o, d) = match st.needs {
                        Some(tool) if !has_tool(tool) => (Outcome::Skip(tool), Duration::ZERO),
                        _ => {
                            // After a failed prerequisite, this step can't mean anything.
                            let blocked = st.after.is_some_and(|a| {
                                done.lock()
                                    .unwrap()
                                    .iter()
                                    .any(|(n, o, _)| n == a && !matches!(o, Outcome::Pass))
                            });
                            if blocked {
                                (Outcome::Blocked(st.after.unwrap()), Duration::ZERO)
                            } else {
                                run_one(st.name, &st.cmd, &logs)
                            }
                        }
                    };
                    report(st.name, &o, d, &logs);
                    done.lock().unwrap().push((st.name.to_string(), o, d));
                }
            });
        }
    });
    results.extend(done.into_inner().unwrap());
    summary(&results, t0);
    if results
        .iter()
        .any(|(_, o, _)| matches!(o, Outcome::Fail | Outcome::Blocked(_)))
    {
        bail!("some steps failed (logs in {})", logs.display());
    }
    Ok(())
}

enum Outcome {
    Pass,
    Fail,
    Skip(&'static str),
    Blocked(&'static str),
}

fn run_one(name: &str, cmd: &str, logs: &std::path::Path) -> (Outcome, Duration) {
    let t = Instant::now();
    let log = std::fs::File::create(logs.join(format!("{name}.log"))).expect("create a ci log");
    let ok = Command::new("sh")
        .args(["-c", cmd])
        .current_dir(crate::root())
        .stdin(Stdio::null())
        .stdout(log.try_clone().expect("clone a ci log"))
        .stderr(log)
        .status()
        .is_ok_and(|s| s.success());
    (if ok { Outcome::Pass } else { Outcome::Fail }, t.elapsed())
}

fn report(name: &str, o: &Outcome, d: Duration, logs: &std::path::Path) {
    let secs = d.as_secs();
    match o {
        Outcome::Pass => println!("PASS  {name:14} {secs:>5}s"),
        Outcome::Fail => println!(
            "FAIL  {name:14} {secs:>5}s  {}",
            logs.join(format!("{name}.log")).display()
        ),
        Outcome::Skip(tool) => println!("SKIP  {name:14}        no `{tool}`"),
        Outcome::Blocked(after) => println!("SKIP  {name:14}        `{after}` failed"),
    }
}

fn summary(results: &[(String, Outcome, Duration)], t0: Instant) {
    let failed: Vec<&str> = results
        .iter()
        .filter(|(_, o, _)| matches!(o, Outcome::Fail))
        .map(|(n, ..)| n.as_str())
        .collect();
    println!(
        "{} steps in {}s{}",
        results.len(),
        t0.elapsed().as_secs(),
        if failed.is_empty() {
            String::new()
        } else {
            format!("; failed: {}", failed.join(", "))
        }
    );
}

/// Whether `tool` runs: a program on `PATH`, or `cargo-<x>` as a cargo subcommand.
fn has_tool(tool: &str) -> bool {
    let mut c = match tool.strip_prefix("cargo-") {
        Some(sub) => {
            let mut c = Command::new("cargo");
            c.args([sub, "--version"]);
            c
        }
        None => {
            let mut c = Command::new(tool);
            c.arg("--version");
            c
        }
    };
    c.stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|s| s.success())
}

fn has_toolchain(t: &str) -> bool {
    Command::new("rustc")
        .env("RUSTUP_TOOLCHAIN", t)
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|s| s.success())
}

#[cfg(test)]
mod tests {
    use super::{ALL, affected, steps};

    #[test]
    fn all_names_every_step() {
        let names: Vec<&str> = steps().iter().map(|s| s.name).collect();
        assert_eq!(names, ALL);
        for path in [
            "crates/lang/src/lang.rs",
            "formal/Formal.lean",
            "xtask/src/ci.rs",
            "x",
        ] {
            for s in affected(path) {
                assert!(ALL.contains(s), "{path}: {s}");
            }
        }
    }

    #[test]
    fn changes_pick_their_steps() {
        assert!(affected("docs/subset.md").is_empty());
        assert!(affected("gadgets/xark-sha256/README.md").is_empty());
        assert!(affected("gadgets/xark-bignum/src/lib.rs").contains(&"coverage"));
        assert!(affected("crates/groth16/src/accel.rs").contains(&"wasm32"));
        assert!(!affected("crates/groth16/src/accel.rs").contains(&"lake"));
        assert_eq!(affected("formal/Formal/RequireLt.lean")[0], "lake");
        assert_eq!(affected("clients/check/zkyc/zkyc.test.ts"), ["clients"]);
        assert_eq!(
            affected("crates/test-harness/src/lib.rs"),
            ["workspace", "lang"]
        );
        assert_eq!(affected("rust-toolchain.toml"), ALL);
    }
}
