//! `cargo xtask publish`: every publishable crate, dependencies first.
//!
//! * `--plan`: check every crate can publish, and print the order (CI runs this);
//! * `--dry-run`: package every crate and build each from its own `.crate`, as
//!   crates.io will see it, uploading nothing;
//! * `--execute`: the real release (needs `cargo login`). `cargo publish` waits for
//!   each crate to index before the next, so its dependencies are always there;
//!   `--skip-published` skips the crates already at this version, so a re-run after a
//!   failed publish resumes instead of stopping at the first published crate.
//!
//! A crate is publishable unless its manifest says `publish = false`. Every
//! dependency of a publishable crate on another local crate (dev-dependencies
//! included, since crates.io resolves them too) must itself be publishable and carry
//! a `version`: a mistake fails here, not halfway through a release.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::{Command, Stdio};

use anyhow::{Context, Result, bail};
use serde_json::Value;

#[derive(clap::Args)]
#[command(group(
    clap::ArgGroup::new("mode")
        .required(true)
        .multiple(false)
        .args(["plan", "dry_run", "execute"]),
))]
pub struct Args {
    /// Check every crate can publish, and print the order.
    #[arg(long)]
    plan: bool,
    /// Package and build every crate from its `.crate`; upload nothing.
    #[arg(long)]
    dry_run: bool,
    /// Publish every crate to crates.io.
    #[arg(long)]
    execute: bool,
    /// With --execute: skip the crates already on crates.io at this version.
    #[arg(long)]
    skip_published: bool,
}

pub fn run(args: Args) -> Result<()> {
    // `requires = "execute"` would be tidier, but clap treats a bool flag's default as
    // present, so the requirement is never enforced.
    if args.skip_published && !args.execute {
        bail!("--skip-published needs --execute");
    }
    let order = plan()?;
    if args.plan {
        println!("{} crates, in publish order:", order.len());
        for (name, _) in &order {
            println!("  {name}");
        }
    } else if args.dry_run {
        dry_run()?;
    } else {
        for (name, version) in &order {
            if args.skip_published && published(name, version) {
                println!(">>> {name} {version} is already on crates.io; skipped");
                continue;
            }
            println!(">>> publishing {name}");
            let status = Command::new("cargo")
                .args(["publish", "-p", name])
                .current_dir(crate::root())
                .status()?;
            if !status.success() {
                bail!("publishing {name} failed");
            }
        }
        println!("All {} crates published.", order.len());
    }
    Ok(())
}

/// Whether `name@version` is already on crates.io. `cargo info` asks the index, the
/// same one `cargo publish` checks; a failure of any kind (a network one included)
/// reads as "not published", and the publish then reports the real problem.
fn published(name: &str, version: &str) -> bool {
    Command::new("cargo")
        .args(["info", "-q", &format!("{name}@{version}")])
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
}

/// The publishable crates in dependency order, with the version being published.
fn plan() -> Result<Vec<(String, String)>> {
    let root = crate::root();
    let mut pkgs: BTreeMap<String, Value> = BTreeMap::new();
    for p in metadata(&root)? {
        pkgs.insert(p["name"].as_str().unwrap_or_default().to_string(), p);
    }
    let publishable: BTreeSet<&str> = pkgs
        .iter()
        .filter(|(_, p)| p["publish"] != serde_json::json!([]))
        .map(|(n, _)| n.as_str())
        .collect();
    let mut errors = Vec::new();
    let mut deps: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for &n in &publishable {
        let mine = deps.entry(n).or_default();
        for d in pkgs[n]["dependencies"].as_array().into_iter().flatten() {
            let (dep, req) = (
                d["name"].as_str().unwrap_or_default(),
                d["req"].as_str().unwrap_or("*"),
            );
            if !pkgs.contains_key(dep) || d["path"].is_null() || dep == n {
                continue;
            }
            if d["kind"] == "dev" && req == "*" {
                continue; // a path-only dev-dependency: cargo drops it on publish
            }
            if req == "*" {
                errors.push(format!("{n} -> {dep}: a path dependency without a version"));
            }
            if !publishable.contains(dep) {
                errors.push(format!("{n} -> {dep}: depends on an unpublished crate"));
            }
            mine.insert(pkgs.get_key_value(dep).unwrap().0.as_str());
        }
    }
    errors.extend(npm_version_errors(
        pkgs["xark-cli"]["version"].as_str().unwrap_or_default(),
    ));
    if !errors.is_empty() {
        bail!("cannot publish:\n  {}", errors.join("\n  "));
    }
    // Leaves first; ties alphabetical, so the order is stable.
    let mut order: Vec<&str> = Vec::new();
    while order.len() < deps.len() {
        let ready: Vec<&str> = deps
            .iter()
            .filter(|(n, d)| !order.contains(n) && d.iter().all(|x| order.contains(x)))
            .map(|(n, _)| *n)
            .collect();
        if ready.is_empty() {
            let rest: Vec<&str> = deps
                .keys()
                .filter(|n| !order.contains(n))
                .copied()
                .collect();
            bail!("dependency cycle among: {}", rest.join(" "));
        }
        order.extend(ready);
    }
    Ok(order
        .into_iter()
        .map(|n| {
            (
                n.to_string(),
                pkgs[n]["version"].as_str().unwrap_or_default().to_string(),
            )
        })
        .collect())
}

/// The npm package `@blueshift-gg/xark` is released with the crates: its
/// `package.json` and its client runtime's `VERSION` (which checks a client's
/// `schema.json` came from the same release) must carry the workspace's version.
fn npm_version_errors(version: &str) -> Vec<String> {
    let wasm = crate::root().join("crates/wasm");
    let read = |f: &str| std::fs::read_to_string(wasm.join(f)).unwrap_or_default();
    let package: Value = serde_json::from_str(&read("package.json")).unwrap_or_default();
    let client = read("js/client.mjs");
    let runtime = client
        .lines()
        .find_map(|l| l.strip_prefix("export const VERSION = \""))
        .and_then(|l| l.split('"').next())
        .unwrap_or_default();
    let mut errors = Vec::new();
    if package["version"] != version {
        errors.push(format!(
            "crates/wasm/package.json is {}, not {version}",
            package["version"]
        ));
    }
    if runtime != version {
        errors.push(format!(
            "crates/wasm/js/client.mjs's VERSION is {runtime:?}, not {version}"
        ));
    }
    errors
}

/// `cargo metadata --no-deps` for the workspace at `dir`: its packages.
fn metadata(dir: &Path) -> Result<Vec<Value>> {
    let out = Command::new("cargo")
        .args(["metadata", "--no-deps", "--format-version", "1"])
        .current_dir(dir)
        .output()
        .context("running cargo metadata")?;
    if !out.status.success() {
        bail!(
            "cargo metadata in {}: {}",
            dir.display(),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    let v: Value = serde_json::from_slice(&out.stdout)?;
    Ok(v["packages"].as_array().cloned().unwrap_or_default())
}

/// Package every crate and build each from its `.crate`. A plain `cargo publish
/// --dry-run -p <crate>` can't, before a release: it resolves the crate's xark
/// dependencies at the new version from crates.io, where they aren't yet. `cargo
/// package --workspace` resolves them from the other local packages instead. This
/// runs in a copy of HEAD so uncommitted changes are not included.
fn dry_run() -> Result<()> {
    let root = crate::root();
    let copy = crate::target_dir().join("publish-dry");
    let _ = std::fs::remove_dir_all(&copy);
    std::fs::create_dir_all(&copy)?;
    let mut archive = Command::new("git")
        .args(["archive", "HEAD"])
        .current_dir(&root)
        .stdout(Stdio::piped())
        .spawn()?;
    let tar = Command::new("tar")
        .args(["-x", "-C"])
        .arg(&copy)
        .stdin(archive.stdout.take().unwrap())
        .status()?;
    if !archive.wait()?.success() || !tar.success() {
        bail!("extracting HEAD into {}", copy.display());
    }
    let mut cmd = Command::new("cargo");
    cmd.args(["package", "--workspace"])
        .current_dir(&copy)
        // Its own target: cargo never rechecks a registry package's build, so a
        // shared one would reuse an earlier run's build of a crate at this version.
        .env("CARGO_TARGET_DIR", copy.join("target"));
    for p in metadata(&copy)? {
        if p["publish"] == serde_json::json!([]) {
            cmd.args(["--exclude", p["name"].as_str().unwrap_or_default()]);
        }
    }
    if !cmd.status()?.success() {
        bail!("cargo package failed");
    }
    println!("Dry run complete: every crate packages and builds from its tarball.");
    Ok(())
}
