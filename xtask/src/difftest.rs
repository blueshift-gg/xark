//! `cargo xtask difftest`: an adversarial test of every example on its own test inputs.
//!
//! Each example is built, its `xark test` inputs recorded (`XARK_DUMP_INPUTS`), and
//! `difftest --search` run on them: every input, and single-leaf mutations of it,
//! must get the verdict the test saw, decided by exhaustive witness search (exactly
//! one witness where accepted, none where rejected). A search that can't decide in
//! time is counted, not failed, but an example where no search decides is reported
//! as undecided. A build failure or a failing `xark test` is a failure; an example
//! whose tests record no inputs (heavy tests are `#[ignore]`d, or they only drive
//! the prover) is listed, not failed.

use std::fs::File;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;

use anyhow::{Result, bail};

#[derive(clap::Args)]
pub struct Args {
    /// Examples to sweep (default: every circuit under `--max-rows`).
    examples: Vec<String>,
    /// Leave these examples out (comma-separated), as skipped.
    #[arg(long, value_delimiter = ',')]
    skip: Vec<String>,
    /// Skip circuits with more R1CS rows than this.
    #[arg(long, default_value_t = 2_500_000)]
    max_rows: u64,
    /// Sweep only every n-th example from the k-th (`k/n`): CI splits the sweep.
    #[arg(long, value_parser = parse_shard)]
    shard: Option<(usize, usize)>,
    /// Examples swept at once.
    #[arg(long, default_value_t = crate::default_jobs())]
    jobs: usize,
    /// A directory of `<example>/circuit.xbc` from another build (an older
    /// commit): also compare the two builds' verdicts.
    #[arg(long)]
    base: Option<PathBuf>,
    /// Use the `xark` and `difftest` already built.
    #[arg(long)]
    no_build: bool,
}

pub fn parse_shard(s: &str) -> Result<(usize, usize), String> {
    let (k, n) = s.split_once('/').ok_or("expected k/n")?;
    let (k, n): (usize, usize) = (
        k.parse().map_err(|_| "bad k")?,
        n.parse().map_err(|_| "bad n")?,
    );
    if n == 0 || k >= n {
        return Err("need 0 <= k < n".into());
    }
    Ok((k, n))
}

/// Intentionally unsound examples: the search must find their second witness.
const UNSOUND: &[&str] = &["underconstrained_bit"];
/// Examples whose searches can't decide by design: non-native modular inverses over
/// a ~256-bit prime (the witness_search.rs blind spot). They get the verdict checks
/// without search; the same gadget code is searched exhaustively over small fields
/// (`small_field_curve_gadgets_are_sound`, both curve shapes) and proven in Lean
/// (`ec_add_incomplete_*_sound`).
const BLINDSPOT: &[&str] = &["ec_incomplete", "ec_incomplete_r1"];
/// The ECDSA circuits are made of those inverses: skipped. Their blocks are searched
/// instead (`signature_blocks_are_sound`).
const UNSEARCHABLE: &[&str] = &["secp256k1_ecdsa", "secp256r1_ecdsa"];
/// Per-search time limits (seconds) for examples that need more than the default (20),
/// unless `XARK_SEARCH_SECS` is set: ed25519 is searched whole (396,912 rows), so
/// pull requests `--skip` it and the weekly run sweeps it alone.
const SLOW: &[(&str, u32)] = &[
    ("ed25519", 180),
    // The `HEAVY` examples' searches either decide within seconds or run out any
    // budget (the non-native relations): at 10 s each decided and undecided count
    // was the same as at 20 (grumpkin_ivc 18 of 51 inconclusive, on_curve_ed25519 11
    // of 14, grumpkin_ipa_fold 8 of 34, grumpkin_augmented_step 6 of 34,
    // grumpkin_nova_fold 6 of 34), in half the time.
    ("grumpkin_ivc", 10),
    ("on_curve_ed25519", 10),
    ("grumpkin_ipa_fold", 10),
    ("grumpkin_augmented_step", 10),
    ("grumpkin_nova_fold", 10),
];

/// Examples whose searches mostly run out their budget (the non-native modular
/// relations the search can't decide: `xark_ir::witness_search`), so each takes
/// minutes where the rest take seconds: dealt out first, one per shard, before the
/// rest. From the per-example times of CI run 42195095843 (shards of 4, `--jobs 2`):
/// grumpkin_ivc 6 min, on_curve_ed25519 3.7, grumpkin_ipa_fold 2.7, aes_gcm 2,
/// grumpkin_augmented_step 2, grumpkin_nova_fold 2, and aes256_gcm 5 min of decided
/// searches one at a time (PR #52's run); every other example under a minute. Each
/// run prints the times to check this against.
const HEAVY: &[&str] = &[
    "grumpkin_ivc",
    "on_curve_ed25519",
    "grumpkin_ipa_fold",
    "aes_gcm",
    "aes256_gcm",
    "grumpkin_augmented_step",
    "grumpkin_nova_fold",
    "ed25519",
];

#[derive(Clone, Copy, PartialEq)]
enum Outcome {
    Pass,
    Fail,
    Skip,
    Undecided,
    NoInputs,
}

struct Sweep {
    work: PathBuf,
    xark: PathBuf,
    difftest: PathBuf,
    max_rows: u64,
    base: Option<PathBuf>,
    /// Threads for one example's witness searches: its share of the cores.
    search_threads: usize,
}

pub fn run(args: Args) -> Result<()> {
    if !args.no_build {
        crate::cargo_build(&[
            "-p",
            "xark-cli",
            "--bin",
            "xark",
            "-p",
            "xark-frontend",
            "--example",
            "difftest",
        ])?;
    }
    let release = crate::target_dir().join("release");
    let sweep = Sweep {
        work: crate::target_dir().join("difftest-examples"),
        xark: release.join("xark"),
        difftest: release.join("examples/difftest"),
        max_rows: args.max_rows,
        base: args.base,
        // The time limit on a search is wall time, so no more threads than cores over
        // the examples running at once.
        search_threads: (std::thread::available_parallelism().map_or(1, |n| n.get()) / args.jobs)
            .max(1),
    };
    let mut names = if args.examples.is_empty() {
        crate::circuits()?
    } else {
        args.examples
    };
    names.retain(|n| !args.skip.contains(n));
    // Heavy examples first (in `HEAVY`'s order), then the rest by name, so round-robin
    // shards each get one heavy example before any gets two.
    names.sort_by_key(|n| HEAVY.iter().position(|h| h == n).unwrap_or(HEAVY.len()));
    if let Some((k, n)) = args.shard {
        names = names
            .into_iter()
            .enumerate()
            .filter(|(i, _)| i % n == k)
            .map(|(_, x)| x)
            .collect();
    }
    let results = Mutex::new(Vec::new());
    crate::parallel(names.clone(), args.jobs, |_, name| {
        let started = std::time::Instant::now();
        let (outcome, message) = sweep
            .one(&name)
            .unwrap_or_else(|e| (Outcome::Fail, format!("FAILED — {e}")));
        println!("{name}: {message} ({}s)", started.elapsed().as_secs());
        results.lock().unwrap().push((name, outcome));
    });
    let mut results = results.into_inner().unwrap();
    results.sort_by(|a, b| a.0.cmp(&b.0));
    let list = |o: Outcome| {
        let l: Vec<&str> = results
            .iter()
            .filter(|r| r.1 == o)
            .map(|r| r.0.as_str())
            .collect();
        if l.is_empty() {
            "none".to_string()
        } else {
            l.join(" ")
        }
    };
    let count = |o: Outcome| results.iter().filter(|r| r.1 == o).count();
    println!(
        "{} examples: {} passed, {} failed, {} skipped, undecided: {}, no inputs: {}",
        names.len(),
        count(Outcome::Pass),
        count(Outcome::Fail),
        count(Outcome::Skip),
        list(Outcome::Undecided),
        list(Outcome::NoInputs),
    );
    if count(Outcome::Fail) > 0 {
        bail!("failed: {}", list(Outcome::Fail));
    }
    Ok(())
}

impl Sweep {
    /// Sweep one example: its outcome, and a line saying why.
    fn one(&self, n: &str) -> Result<(Outcome, String)> {
        use Outcome::*;
        if UNSEARCHABLE.contains(&n) {
            return Ok((
                Skip,
                "skipped (256-bit inverses; its blocks are searched in snapshot.rs)".into(),
            ));
        }
        let out = self.work.join("build").join(n);
        let dump = self.work.join("dumps").join(n);
        let _ = std::fs::remove_dir_all(&dump);
        let example = crate::root().join("examples").join(n);
        let log = |what: &str| self.work.join(format!("{n}.{what}.log"));

        let build = logged(
            Command::new(&self.xark)
                .arg("build")
                .arg(&example)
                .arg("--out")
                .arg(&out),
            &log("build"),
        )?;
        if !build.success() {
            return Ok((
                Fail,
                format!("build FAILED (see {})", log("build").display()),
            ));
        }
        let xbc = out.join("circuit.xbc");
        let rows = xark_ir::function_decode::stream_count_constraints(&std::fs::read(&xbc)?) as u64;
        if rows > self.max_rows {
            return Ok((Skip, format!("skipped ({rows} rows > --max-rows)")));
        }
        // One cargo target for every example's `xark test`: host dependencies build once.
        let test = logged(
            Command::new(&self.xark)
                .arg("test")
                .arg(&example)
                .env("XARK_DUMP_INPUTS", &dump)
                .env("CARGO_TARGET_DIR", self.work.join("target")),
            &log("test"),
        )?;
        if !test.success() {
            return Ok((
                Fail,
                format!("FAILED — xark test (see {})", log("test").display()),
            ));
        }
        if !dump.is_dir() {
            return Ok((NoInputs, "no recorded inputs — nothing to search".into()));
        }

        let base = self
            .base
            .as_ref()
            .map(|b| b.join(n).join("circuit.xbc"))
            .unwrap_or_else(|| xbc.clone());
        let diff = |search: bool| -> Result<(Option<i32>, String)> {
            let mut cmd = Command::new(&self.difftest);
            cmd.arg(&base).arg(&xbc).arg(&dump);
            if search {
                cmd.arg("--search");
            }
            // `XARK_SEARCH_SECS` set by the caller wins (the weekly ed25519 sweep).
            if std::env::var_os("XARK_SEARCH_SECS").is_none() {
                let secs = SLOW.iter().find(|(s, _)| *s == n).map_or(20, |(_, s)| *s);
                cmd.env("XARK_SEARCH_SECS", secs.to_string());
            }
            cmd.env("XARK_SEARCH_THREADS", self.search_threads.to_string());
            let status = logged(&mut cmd, &log("diff"))?;
            Ok((
                status.code(),
                std::fs::read_to_string(log("diff")).unwrap_or_default(),
            ))
        };
        let fails = |text: &str| -> String {
            text.lines()
                .filter(|l| l.contains("FAIL"))
                .take(3)
                .collect::<Vec<_>>()
                .join(" ")
        };

        if UNSOUND.contains(&n) {
            let (_, text) = diff(true)?;
            return Ok(if text.contains("two witnesses") {
                (
                    Pass,
                    "intentionally under-constrained — second witness found".into(),
                )
            } else {
                (
                    Fail,
                    "FAILED — its known under-constraint went undetected".into(),
                )
            });
        }
        if BLINDSPOT.contains(&n) {
            let (code, text) = diff(false)?;
            return Ok(if code == Some(0) {
                (Pass, "verdicts agree; not searched (256-bit inverse — covered by the small-field search and Lean)".into())
            } else {
                (Fail, format!("FAILED — {}", fails(&text)))
            });
        }
        let (code, text) = diff(true)?;
        Ok(match code {
            Some(0) => {
                let tail: Vec<&str> = text.lines().rev().take(2).collect();
                (Pass, tail.into_iter().rev().collect::<Vec<_>>().join(" "))
            }
            Some(2) => (Undecided, "undecided — every search inconclusive".into()),
            _ => (Fail, format!("FAILED — {}", fails(&text))),
        })
    }
}

/// Run `cmd` with its output in `log`.
fn logged(cmd: &mut Command, log: &Path) -> Result<std::process::ExitStatus> {
    std::fs::create_dir_all(log.parent().unwrap())?;
    let file = File::create(log)?;
    Ok(cmd
        .stdout(Stdio::from(file.try_clone()?))
        .stderr(Stdio::from(file))
        .status()?)
}
