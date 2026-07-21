//! `xark profile <dir>` — attribute every R1CS constraint back to its source
//! line, call-chain, and kind, then print a drill-down sorted by cost.
//!
//! Builds with the extractor's `--profile` flag (writes a separate `profile.json`,
//! leaving `r1cs.json` / `circuit.json` byte-identical), then groups by `(file,
//! line)` → `chain` → [`ConstraintKind`], summing counts.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use clap::Args;
use serde_json::json;

use xark_ir::profile::{ConstraintKind, ProfileProgram};

use crate::xark_project::XarkProject;

#[derive(Args, Debug)]
pub struct ProfileArgs {
    /// Circuit crate directory to build and profile.
    #[arg(default_value = ".", value_hint = clap::ValueHint::DirPath)]
    pub crate_dir: String,
    /// Output directory for the intermediate artifacts + `profile.json`
    /// (default: `<crate>/target/xark/<pkg>/`).
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub out: Option<String>,
    /// Field the circuit is defined over.
    #[arg(long, default_value = "bn254")]
    pub field: String,
    /// Emit the aggregated drill-down as JSON instead of the human-readable tree.
    #[arg(long, default_value_t = false)]
    pub json: bool,
}

pub fn run(args: ProfileArgs) -> Result<()> {
    // 1. Build with `--profile` so `profile.json` is (re)generated.
    let mut build_argv = vec![args.crate_dir.clone()];
    if let Some(out) = &args.out {
        build_argv.push("--out".into());
        build_argv.push(out.clone());
    }
    build_argv.push("--field".into());
    build_argv.push(args.field.clone());
    let code = crate::cli::cmd_build_profile(&build_argv);
    if code != 0 {
        bail!("build failed (exit {code}); fix the circuit before `xark profile`");
    }

    // 2. Locate + read profile.json from the resolved output dir.
    let base = args.out.clone().unwrap_or_else(|| args.crate_dir.clone());
    let project = XarkProject::resolve(Some(base.into()))?;
    let profile_path = project.xark_dir.join("profile.json");
    let text = std::fs::read_to_string(&profile_path).with_context(|| {
        format!(
            "reading {} (did the build emit it?)",
            profile_path.display()
        )
    })?;
    let profile: ProfileProgram = xark_ir::profile::from_json(&text)
        .with_context(|| format!("parsing {}", profile_path.display()))?;

    // 3. Aggregate + render.
    let agg = aggregate(&profile);
    if args.json {
        println!("{}", serde_json::to_string_pretty(&agg_to_json(&agg))?);
    } else {
        print_tree(&agg);
    }
    Ok(())
}

/// The aggregated drill-down: per user line, per function chain, per kind.
struct Aggregate {
    lines: Vec<LineAgg>,
    total: u64,
}

struct LineAgg {
    file: String,
    line: u32,
    /// The source text of that line (best-effort; empty if unreadable).
    src: String,
    total: u64,
    chains: Vec<ChainAgg>,
}

struct ChainAgg {
    chain: Vec<String>,
    total: u64,
    kinds: Vec<KindCount>,
}

struct KindCount {
    kind: String,
    count: u64,
}

/// Render the aggregated tree as a JSON value (for `--json`).
fn agg_to_json(agg: &Aggregate) -> serde_json::Value {
    let lines: Vec<serde_json::Value> = agg
        .lines
        .iter()
        .map(|l| {
            let chains: Vec<serde_json::Value> = l
                .chains
                .iter()
                .map(|c| {
                    let kinds: Vec<serde_json::Value> = c
                        .kinds
                        .iter()
                        .map(|kc| json!({ "kind": kc.kind, "count": kc.count }))
                        .collect();
                    json!({ "chain": c.chain, "total": c.total, "kinds": kinds })
                })
                .collect();
            json!({
                "file": l.file,
                "line": l.line,
                "src": l.src,
                "total": l.total,
                "chains": chains,
            })
        })
        .collect();
    json!({ "lines": lines, "total": agg.total })
}

/// Group `profile` by `(file, line)` → `chain` → `kind`, summing counts, and
/// sort by cost (lines then chains descending; kinds descending). Source line
/// text is read once per distinct file.
fn aggregate(profile: &ProfileProgram) -> Aggregate {
    // (file, line) → chain → kind → count. `BTreeMap` keeps the pre-sort order
    // deterministic before the cost sort.
    type KindMap = BTreeMap<ConstraintKind, u64>;
    type ChainMap = BTreeMap<Vec<String>, KindMap>;
    let mut lines: BTreeMap<(String, u32), ChainMap> = BTreeMap::new();

    for c in &profile.constraints {
        let key = (c.file.clone(), c.line);
        *lines
            .entry(key)
            .or_default()
            .entry(c.chain.clone())
            .or_default()
            .entry(c.kind)
            .or_insert(0) += 1;
    }

    let source_root = Path::new(&profile.source_root);
    let mut src_cache: BTreeMap<String, Vec<String>> = BTreeMap::new();

    let mut line_aggs: Vec<LineAgg> = lines
        .into_iter()
        .map(|((file, line), chains)| {
            let mut chain_aggs: Vec<ChainAgg> = chains
                .into_iter()
                .map(|(chain, kinds)| {
                    let mut kind_counts: Vec<KindCount> = kinds
                        .into_iter()
                        .map(|(k, n)| KindCount {
                            kind: k.as_str().to_string(),
                            count: n,
                        })
                        .collect();
                    // Kinds: most-frequent first, name tie-break.
                    kind_counts
                        .sort_by(|a, b| b.count.cmp(&a.count).then_with(|| a.kind.cmp(&b.kind)));
                    let total = kind_counts.iter().map(|kc| kc.count).sum();
                    ChainAgg {
                        chain,
                        total,
                        kinds: kind_counts,
                    }
                })
                .collect();
            // Chains within a line: costliest first, chain tie-break.
            chain_aggs.sort_by(|a, b| b.total.cmp(&a.total).then_with(|| a.chain.cmp(&b.chain)));
            let total = chain_aggs.iter().map(|c| c.total).sum();
            let src = read_source_line(source_root, &file, line, &mut src_cache);
            LineAgg {
                file,
                line,
                src,
                total,
                chains: chain_aggs,
            }
        })
        .collect();

    // Lines: costliest first, then file/line for determinism.
    line_aggs.sort_by(|a, b| {
        b.total
            .cmp(&a.total)
            .then_with(|| a.file.cmp(&b.file))
            .then_with(|| a.line.cmp(&b.line))
    });

    let total = line_aggs.iter().map(|l| l.total).sum();
    Aggregate {
        lines: line_aggs,
        total,
    }
}

/// Read line `line` (1-based) of `file`, resolving `file` against `source_root`
/// when relative. Caches each file's lines. Returns `""` if unreadable.
fn read_source_line(
    source_root: &Path,
    file: &str,
    line: u32,
    cache: &mut BTreeMap<String, Vec<String>>,
) -> String {
    if !cache.contains_key(file) {
        let path: PathBuf = if Path::new(file).is_absolute() {
            PathBuf::from(file)
        } else {
            source_root.join(file)
        };
        let lines = std::fs::read_to_string(&path)
            .map(|s| s.lines().map(str::to_string).collect())
            .unwrap_or_default();
        cache.insert(file.to_string(), lines);
    }
    let lines = &cache[file];
    line.checked_sub(1)
        .and_then(|i| lines.get(i as usize))
        .map(|s| s.trim().to_string())
        .unwrap_or_default()
}

/// Truncate `s` to `max` display chars, appending `…` when cut.
fn truncate(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        s.to_string()
    } else {
        let mut out: String = s.chars().take(max.saturating_sub(1)).collect();
        out.push('…');
        out
    }
}

/// The `basename:line` locator for a line (basename keeps output compact).
fn locator(file: &str, line: u32) -> String {
    let base = Path::new(file)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(file);
    format!("{base}:{line}")
}

/// Render `(Kind n, Kind m)` for a kind breakdown.
fn kinds_str(kinds: &[KindCount]) -> String {
    let inner = kinds
        .iter()
        .map(|kc| format!("{} {}", kc.kind, kc.count))
        .collect::<Vec<_>>()
        .join(", ");
    format!("({inner})")
}

fn print_tree(agg: &Aggregate) {
    println!(
        "{}",
        crate::style::brand("xark profile — constraints by source line")
    );
    println!();
    for line in &agg.lines {
        let loc = locator(&line.file, line.line);
        let src = if line.src.is_empty() {
            String::new()
        } else {
            truncate(&line.src, 48)
        };
        // A single top-level (empty-chain) group collapses onto the line with its
        // kinds inline; anything else drills down into per-chain sub-bullets.
        let inline_single = line.chains.len() == 1 && line.chains[0].chain.is_empty();
        let head = format!("{:<14} {:<50}", crate::style::brand(&loc), src);
        if inline_single {
            println!(
                "{head} {:>5}   {}",
                line.total,
                kinds_str(&line.chains[0].kinds)
            );
        } else {
            println!("{head} {:>5}", line.total);
            for (i, chain) in line.chains.iter().enumerate() {
                let connector = if i + 1 == line.chains.len() {
                    "└─"
                } else {
                    "├─"
                };
                let label = if chain.chain.is_empty() {
                    "(top-level)".to_string()
                } else {
                    chain.chain.join(" → ")
                };
                println!(
                    "    {connector} {:<38} {:>4}   {}",
                    label,
                    chain.total,
                    kinds_str(&chain.kinds)
                );
            }
        }
    }
    println!("{}", crate::style::brand(&"─".repeat(60)));
    println!(
        "{}  {} constraints",
        crate::style::brand("TOTAL"),
        agg.total
    );
}
