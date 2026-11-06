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
    /// Field the circuit is defined over: `bn254`, or a prime modulus in decimal.
    #[arg(long, default_value = "bn254", value_parser = super::parse_field)]
    pub field: String,
    /// Emit the aggregated drill-down as JSON instead of the human-readable tree.
    #[arg(long, default_value_t = false)]
    pub json: bool,
    /// Also write `profile.html` beside the build: the breakdown, with the circuit's
    /// source shaded by what each line costs.
    #[arg(long, default_value_t = false)]
    pub html: bool,
}

pub fn run(args: ProfileArgs) -> Result<()> {
    let base = args.out.clone().unwrap_or_else(|| args.crate_dir.clone());
    // 1. The last `profile.json` when it's current, else a profile build (`--profile`)
    //    and the one it writes.
    let profile = match current_profile(&base, &args.field) {
        Some(p) => {
            eprintln!(
                "{} profile.json is current (no source changed since): not rebuilding",
                crate::style::tag()
            );
            p
        }
        None => {
            build(&args)?;
            read_profile(&XarkProject::resolve(Some(base.clone().into()))?.xark_dir)?
        }
    };
    let project = XarkProject::resolve(Some(base.into()))?;

    // 3. Aggregate + render.
    let agg = aggregate(&profile);
    if args.json {
        println!("{}", serde_json::to_string_pretty(&agg_to_json(&agg))?);
    } else {
        print_tree(&agg);
    }
    if args.html {
        let name = project
            .xark_dir
            .file_name()
            .map_or("circuit".into(), |n| n.to_string_lossy().into_owned());
        let path = project.xark_dir.join("profile.html");
        std::fs::write(&path, html(&agg, &name, Path::new(&profile.source_root)))
            .with_context(|| format!("writing {}", path.display()))?;
        eprintln!(
            "{} wrote {}",
            crate::style::tag(),
            crate::style::brand(&path.display().to_string())
        );
    }
    Ok(())
}

/// The breakdown as one self-contained HTML page: what kinds of constraints the
/// circuit has, the costliest functions and lines (each opening onto its call
/// chains), and the circuit's source with each line shaded by what it costs.
fn html(agg: &Aggregate, name: &str, source_root: &Path) -> String {
    use std::fmt::Write as _;
    let total = agg.total.max(1);
    let share = |n: u64| 100.0 * n as f64 / total as f64;
    let bar = |n: u64| {
        format!(
            "<div class=bar><i style=\"width:{:.1}%\"></i></div>",
            share(n)
        )
    };
    let mut out = String::new();
    let _ = write!(
        out,
        "<!doctype html>\n<html lang=en><head><meta charset=utf-8>\
         <meta name=viewport content=\"width=device-width, initial-scale=1\">\
         <title>{name} constraints</title><style>{}</style></head><body><main>\
         <header><p class=eyebrow>xark profile</p><h1>{name}</h1>\
         <p class=total><b>{}</b> constraints from <b>{}</b> source lines</p></header>",
        include_str!("profile.css"),
        thousands(agg.total),
        agg.lines.len(),
        name = esc(name),
    );

    out.push_str("<section><h2>By kind</h2><div class=rows>");
    for &(kind, n) in &agg.kinds {
        let _ = write!(
            out,
            "<div class=row><span class=pct>{}</span>{}<span class=n>{}</span>\
             <span class=label>{}</span><p class=why>{}</p></div>",
            pct(n, total),
            bar(n),
            thousands(n),
            kind_name(kind),
            esc(explain(kind)),
        );
    }
    out.push_str("</div></section>");

    if !agg.functions.is_empty() {
        out.push_str(
            "<section><h2>Costliest functions</h2><p class=total>Each with everything it \
             calls; a function only ever called by the one before it shares its row.</p>\
             <div class=rows>",
        );
        for (path, n) in agg.functions.iter().take(10) {
            let _ = write!(
                out,
                "<div class=row><span class=pct>{}</span>{}<span class=n>{}</span>\
                 <code class=label>{}</code></div>",
                pct(*n, total),
                bar(*n),
                thousands(*n),
                esc(&path.join(" → ")),
            );
        }
        out.push_str("</div></section>");
    }

    // The source files the lines are in, numbered for anchors (`#f0-L96`).
    let files: Vec<&str> = {
        let mut f: Vec<&str> = agg.lines.iter().map(|l| l.file.as_str()).collect();
        f.sort();
        f.dedup();
        f
    };
    let anchor = |file: &str, line: u32| {
        let i = files.iter().position(|f| *f == file).unwrap_or(0);
        format!("f{i}-L{line}")
    };

    out.push_str("<section><h2>Costliest lines</h2>");
    for l in agg.lines.iter().take(25) {
        let _ = write!(
            out,
            "<details><summary><span class=pct>{}</span>{}<span class=n>{}</span>\
             <a href=\"#{}\">{}</a><code>{}</code></summary><table class=chains>",
            pct(l.total, total),
            bar(l.total),
            thousands(l.total),
            anchor(&l.file, l.line),
            esc(&locator(&l.file, l.line)),
            esc(&l.src),
        );
        for c in &l.chains {
            let chain = if c.chain.is_empty() {
                "(the statement itself)".to_string()
            } else {
                c.chain.join(" → ")
            };
            let _ = write!(
                out,
                "<tr><td class=n>{}</td><td><code>{}</code></td><td>{}</td></tr>",
                thousands(c.total),
                esc(&chain),
                esc(&kinds_str(&c.kinds)),
            );
        }
        out.push_str("</table></details>");
    }
    out.push_str("</section>");

    // Each file, every line shaded by its cost relative to the costliest line.
    let max = agg.lines.iter().map(|l| l.total).max().unwrap_or(1).max(1);
    out.push_str("<section><h2>Source</h2>");
    for file in &files {
        let path = if Path::new(file).is_absolute() {
            PathBuf::from(file)
        } else {
            source_root.join(file)
        };
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        let costs: BTreeMap<u32, u64> = agg
            .lines
            .iter()
            .filter(|l| l.file == *file)
            .map(|l| (l.line, l.total))
            .collect();
        let _ = write!(out, "<h3>{}</h3><div class=src><table>", esc(file));
        for (i, src) in text.lines().enumerate() {
            let line = i as u32 + 1;
            let cost = costs.get(&line).copied();
            let heat = cost.map_or(0.0, |n| (n as f64 / max as f64).sqrt());
            let _ = write!(
                out,
                "<tr id=\"{}\" style=\"--h:{heat:.3}\"><td class=ln>{line}</td>\
                 <td class=cost>{}</td><td>{}</td></tr>",
                anchor(file, line),
                cost.map(thousands).unwrap_or_default(),
                esc(src),
            );
        }
        out.push_str("</table></div>");
    }
    out.push_str("</section></main></body></html>\n");
    out
}

/// `1234567` → `1,234,567`.
fn thousands(n: u64) -> String {
    let s = n.to_string();
    let mut out = String::new();
    for (i, c) in s.chars().enumerate() {
        if i > 0 && (s.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(c);
    }
    out
}

/// `s` safe in HTML text and attribute values.
fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// The profile build (`xark build` with constraint attribution).
fn build(args: &ProfileArgs) -> Result<()> {
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
    Ok(())
}

/// The build directory's `profile.json`, when it's current (see
/// [`stale_build`](crate::cli::stale_build)) and made for `field`.
fn current_profile(base: &str, field: &str) -> Option<ProfileProgram> {
    let dir = XarkProject::resolve(Some(base.into())).ok()?.xark_dir;
    if crate::cli::stale_build(&dir, "profile.json", Some(field)).is_some() {
        return None;
    }
    read_profile(&dir)
        .ok()
        .filter(|p| p.field.as_ref() == Some(&xark_ir::FieldSpec::named(field)))
}

/// `profile.json` from the build directory `dir`.
fn read_profile(dir: &Path) -> Result<ProfileProgram> {
    let path = dir.join("profile.json");
    let text = std::fs::read_to_string(&path)
        .with_context(|| format!("reading {} (did the build emit it?)", path.display()))?;
    xark_ir::profile::from_json(&text).with_context(|| format!("parsing {}", path.display()))
}

/// The aggregated drill-down: per user line, per function chain, per kind.
struct Aggregate {
    lines: Vec<LineAgg>,
    total: u64,
    /// Every constraint by kind, most first.
    kinds: Vec<(ConstraintKind, u64)>,
    /// Constraints per function, counting everything it called (so a hash
    /// function includes its rounds), most first. A function that only ever
    /// runs inside another at the same cost shares its row, outermost first
    /// (`commitment → hash → perm`).
    functions: Vec<(Vec<String>, u64)>,
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
    let kinds: Vec<serde_json::Value> = agg
        .kinds
        .iter()
        .map(|(k, n)| json!({ "kind": k.as_str(), "count": n, "explain": explain(*k) }))
        .collect();
    let functions: Vec<serde_json::Value> = agg
        .functions
        .iter()
        .map(|(path, n)| json!({ "functions": path, "count": n }))
        .collect();
    json!({ "lines": lines, "total": agg.total, "kinds": kinds, "functions": functions })
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
    let mut kinds: BTreeMap<ConstraintKind, u64> = BTreeMap::new();
    let mut chains: BTreeMap<&[String], u64> = BTreeMap::new();

    for c in &profile.constraints {
        *kinds.entry(c.kind).or_default() += 1;
        *chains.entry(&c.chain).or_default() += 1;
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
    let mut kinds: Vec<(ConstraintKind, u64)> = kinds.into_iter().collect();
    kinds.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    let functions = function_costs(&chains);
    Aggregate {
        lines: line_aggs,
        total,
        kinds,
        functions,
    }
}

/// Inclusive cost per function from per-chain counts, with functions that only
/// ever run inside another at the same cost folded into its row.
fn function_costs(chains: &BTreeMap<&[String], u64>) -> Vec<(Vec<String>, u64)> {
    use std::collections::BTreeSet;
    // Per function: its cost, and the functions every call of it runs inside.
    let mut costs: BTreeMap<&str, (u64, Option<BTreeSet<&str>>)> = BTreeMap::new();
    for (chain, &n) in chains {
        let mut outer: BTreeSet<&str> = BTreeSet::new();
        for f in chain.iter() {
            // A recursive function counts each constraint once.
            if outer.contains(f.as_str()) {
                continue;
            }
            let e = costs.entry(f).or_default();
            e.0 += n;
            e.1 = Some(match e.1.take() {
                None => outer.clone(),
                Some(prev) => prev.intersection(&outer).copied().collect(),
            });
            outer.insert(f);
        }
    }
    let mut sorted: Vec<(&str, u64, BTreeSet<&str>)> = costs
        .into_iter()
        .map(|(f, (n, outer))| (f, n, outer.unwrap_or_default()))
        .collect();
    // Costliest first; at equal cost, outermost first.
    sorted.sort_by(|a, b| (b.1, a.2.len(), a.0).cmp(&(a.1, b.2.len(), b.0)));
    let mut rows: Vec<(Vec<&str>, u64)> = Vec::new();
    for (f, n, outer) in sorted {
        match rows
            .iter_mut()
            .find(|(path, m)| *m == n && outer.contains(path[path.len() - 1]))
        {
            Some((path, _)) => path.push(f),
            None => rows.push((vec![f], n)),
        }
    }
    rows.into_iter()
        .map(|(path, n)| (path.into_iter().map(str::to_string).collect(), n))
        .collect()
}

/// What a kind of constraint is, and how to have fewer of them.
fn explain(kind: ConstraintKind) -> &'static str {
    match kind {
        ConstraintKind::RangeCheck => {
            "proving a value fits in N bits, one constraint per bit. These come from \
             `uN` inputs, wrapping arithmetic, bit operations and comparisons; use the \
             narrowest integer type that fits."
        }
        ConstraintKind::Comparison => {
            "the extra steps of `<`, `<=`, `>` and `>=` (each also range-checks the \
             difference). Compare at the narrowest width, and compare once and reuse \
             the result."
        }
        ConstraintKind::Booleanity => "`require_bool`: one per value proven to be 0 or 1.",
        ConstraintKind::Mul => {
            "multiplying two values the prover supplies, one each. Additions and \
             multiplying by a constant are free."
        }
        ConstraintKind::Equality => {
            "`require_eq`, and joining split bits back into their value: one each."
        }
        ConstraintKind::Xor | ConstraintKind::Or => {
            "bitwise logic, one per bit. Hashes built on it (SHA-256, Keccak) are costly \
             here; a field-native hash such as Poseidon2 is far cheaper."
        }
        ConstraintKind::HintPin => {
            "checking a value worked out outside the circuit, such as an inverse: one each."
        }
        ConstraintKind::Other => "a sum the compiler had to store as its own value: one each.",
    }
}

/// A kind's name for people.
fn kind_name(kind: ConstraintKind) -> &'static str {
    match kind {
        ConstraintKind::Mul => "multiplications",
        ConstraintKind::Booleanity => "bool checks",
        ConstraintKind::RangeCheck => "range checks",
        ConstraintKind::Comparison => "comparisons",
        ConstraintKind::Equality => "equalities",
        ConstraintKind::Xor => "xor",
        ConstraintKind::Or => "or",
        ConstraintKind::HintPin => "hint checks",
        ConstraintKind::Other => "stored sums",
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
    print_summary(agg);
}

/// Split `text` into lines of at most `width` chars, at spaces.
fn wrap(text: &str, width: usize) -> Vec<String> {
    let mut lines = vec![String::new()];
    for word in text.split(' ') {
        let line = lines.last_mut().expect("starts with a line");
        if !line.is_empty() && line.chars().count() + 1 + word.chars().count() > width {
            lines.push(word.to_string());
        } else {
            if !line.is_empty() {
                line.push(' ');
            }
            line.push_str(word);
        }
    }
    lines
}

/// Percent of the circuit, for display.
fn pct(n: u64, total: u64) -> String {
    let p = 100.0 * n as f64 / total.max(1) as f64;
    if n > 0 && p < 0.5 {
        "<1%".into()
    } else {
        format!("{p:.0}%")
    }
}

/// The circuit-wide view: what kinds of constraints it has, what each means,
/// and which functions cost the most.
fn print_summary(agg: &Aggregate) {
    println!();
    println!("{}", crate::style::brand("By kind"));
    for &(kind, n) in &agg.kinds {
        println!("  {:>4}  {n:>8}  {}", pct(n, agg.total), kind_name(kind));
        for line in wrap(explain(kind), 72) {
            println!("        {}", crate::style::dim(&line));
        }
    }
    if !agg.functions.is_empty() {
        println!();
        println!(
            "{}",
            crate::style::brand("Costliest functions (including what they call)")
        );
        for (path, n) in agg.functions.iter().take(5) {
            println!("  {:>4}  {n:>8}  {}", pct(*n, agg.total), path.join(" → "));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn chain(fs: &[&str]) -> Vec<String> {
        fs.iter().map(|f| f.to_string()).collect()
    }

    #[test]
    fn functions_fold_wrappers_and_count_inclusively() {
        let commit = chain(&["commitment", "hash", "perm", "round"]);
        let commit_other = chain(&["commitment", "hash", "perm", "sbox"]);
        let le = chain(&["le"]);
        let nested_le = chain(&["require", "le", "le"]);
        let mut chains: BTreeMap<&[String], u64> = BTreeMap::new();
        chains.insert(&commit, 30);
        chains.insert(&commit_other, 10);
        chains.insert(&le, 4);
        chains.insert(&nested_le, 1);
        let rows = function_costs(&chains);
        let rows: Vec<(String, u64)> = rows.into_iter().map(|(p, n)| (p.join(" → "), n)).collect();
        assert_eq!(
            rows,
            [
                ("commitment → hash → perm".to_string(), 40),
                ("round".to_string(), 30),
                ("sbox".to_string(), 10),
                // `le` also runs outside `require`, so it keeps its own row, and
                // its recursive call counts once.
                ("le".to_string(), 5),
                ("require".to_string(), 1),
            ]
        );
    }

    #[test]
    fn html_shades_the_source_and_escapes_it() {
        let dir = std::env::temp_dir().join(format!("xark-profile-html-{}", std::process::id()));
        std::fs::create_dir_all(dir.join("src")).unwrap();
        std::fs::write(dir.join("src/lib.rs"), "fn a() {}\nlet x = a < b && c;\n").unwrap();
        let c = |id, kind| xark_ir::profile::ConstraintProfile {
            id,
            file: "src/lib.rs".into(),
            line: 2,
            col: 1,
            chain: chain(&["le"]),
            kind,
        };
        let profile = ProfileProgram {
            source_root: dir.display().to_string(),
            field: None,
            constraints: vec![
                c(0, ConstraintKind::Comparison),
                c(1, ConstraintKind::RangeCheck),
            ],
        };
        let page = html(&aggregate(&profile), "a<b", &dir);
        let _ = std::fs::remove_dir_all(&dir);
        assert!(
            page.starts_with("<!doctype html>")
                && page.contains("<title>a&lt;b constraints</title>")
        );
        // The costly line links to its row in the source, which is shaded and escaped.
        assert!(page.contains("<a href=\"#f0-L2\">lib.rs:2</a>"), "{page}");
        assert!(page.contains("<tr id=\"f0-L2\" style=\"--h:1.000\"><td class=ln>2</td><td class=cost>2</td><td>let x = a &lt; b &amp;&amp; c;</td></tr>"), "{page}");
        assert!(
            page.contains("<tr id=\"f0-L1\" style=\"--h:0.000\">"),
            "{page}"
        );
        assert_eq!(
            (thousands(1_234_567), thousands(999), thousands(0)),
            ("1,234,567".into(), "999".into(), "0".into())
        );
    }

    #[test]
    fn wraps_at_spaces() {
        assert_eq!(wrap("aa bb cc dd", 5), ["aa bb", "cc dd"]);
        assert_eq!(wrap("toolongword x", 4), ["toolongword", "x"]);
        assert_eq!(pct(1, 1000), "<1%");
        assert_eq!(pct(0, 1000), "0%");
    }
}
