//! `--cache` (minimized-R1CS cache) end-to-end behavior: `setup --cache` writes
//! it, `prove` reloads it (skipping the minimize + validate) and still verifies,
//! and an absent / stale / corrupt cache falls back to a recompute that also
//! verifies. Uses `bignum_ops` — a function (v8) circuit — so the cache path is
//! actually exercised (only function artifacts read the cache).

mod common;

use std::path::Path;
use std::process::{Command, Stdio};

use common::{tempdir, xark_bin, xark_build};

const INPUTS: &[(&str, &str)] = &[
    ("a.limbs[0]", "1"),
    ("a.limbs[1]", "0"),
    ("a.limbs[2]", "0"),
    ("b.limbs[0]", "1"),
    ("b.limbs[1]", "0"),
    ("b.limbs[2]", "0"),
    ("out", "1"),
];

fn setup(out: &Path, cache: bool) -> (bool, String) {
    let mut c = Command::new(xark_bin());
    c.arg("setup")
        .arg(out)
        .arg("--insecure-dev-mode")
        .arg("--deterministic-rng")
        .arg("1");
    if cache {
        c.arg("--cache");
    }
    let o = c
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("spawn xark setup");
    (
        o.status.success(),
        String::from_utf8_lossy(&o.stderr).into_owned(),
    )
}

/// `xark prove` with `PROVE_TIME=1` so the `cached=true/false` marker is emitted.
fn prove(out: &Path, cache: bool) -> (bool, String) {
    let mut c = Command::new(xark_bin());
    c.arg("prove").arg(out).env("PROVE_TIME", "1");
    if cache {
        c.arg("--cache");
    }
    // Unified `--inputs` JSON object (values quoted so large decimals round-trip),
    // matching `common::inputs_json` / `xark prove --inputs`.
    let body = INPUTS
        .iter()
        .map(|(k, v)| format!("\"{k}\": \"{v}\""))
        .collect::<Vec<_>>()
        .join(", ");
    c.arg("--inputs").arg(format!("{{{body}}}"));
    let o = c
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("spawn xark prove");
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&o.stdout),
        String::from_utf8_lossy(&o.stderr),
    );
    (o.status.success(), combined)
}

#[test]
fn cache_hit_fallback_and_warm_all_verify() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");
    let (ok, err) = xark_build("bignum_ops", &out, &target);
    assert!(ok, "build failed: {err}");

    // `setup --cache` writes the minimized-R1CS cache next to the keys.
    let (ok, err) = setup(&out, true);
    assert!(ok, "setup --cache failed: {err}");
    let cache = out.join("r1cs.min.wcz");
    assert!(
        cache.exists(),
        "setup --cache did not write {}",
        cache.display()
    );

    // Cache HIT: prove reloads it (cached=true) and verifies.
    let (ok, o) = prove(&out, false);
    assert!(ok, "prove (cache hit) failed: {o}");
    assert!(o.contains("cached=true"), "expected a cache hit, got:\n{o}");

    // FALLBACK: delete the cache → prove recomputes (cached=false), still verifies,
    // and a *plain* prove must not rewrite it.
    std::fs::remove_file(&cache).unwrap();
    let (ok, o) = prove(&out, false);
    assert!(ok, "prove (recompute fallback) failed: {o}");
    assert!(
        o.contains("cached=false"),
        "expected a recompute, got:\n{o}"
    );
    assert!(!cache.exists(), "a plain prove must not write the cache");

    // WARM: `prove --cache` repopulates it from the recomputed circuit…
    let (ok, o) = prove(&out, true);
    assert!(ok, "prove --cache failed: {o}");
    assert!(cache.exists(), "prove --cache should warm the cache");

    // …and the next plain prove hits the warmed cache and still verifies.
    let (ok, o) = prove(&out, false);
    assert!(ok, "prove (warmed hit) failed: {o}");
    assert!(
        o.contains("cached=true"),
        "expected a warmed cache hit, got:\n{o}"
    );
}

/// The common newcomer flow: `xark prove` with no prior `setup`. The auto-setup
/// it triggers now always warms the R1CS cache (its output feeds this same prove),
/// so the minimize runs ONCE — the prove takes the cache-HIT path instead of
/// re-minimizing the identical circuit.
#[test]
fn bare_prove_auto_setup_warms_cache_and_hits() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");
    let (ok, err) = xark_build("bignum_ops", &out, &target);
    assert!(ok, "build failed: {err}");
    let cache = out.join("r1cs.min.wcz");

    // No explicit setup — a plain `prove` (no `--cache`). Auto-setup runs because
    // no proving key exists yet.
    let (ok, o) = prove(&out, false);
    assert!(ok, "bare auto-setup prove failed: {o}");
    assert!(
        cache.exists(),
        "auto-setup should have warmed the cache at {}",
        cache.display()
    );
    assert!(
        o.contains("cached=true"),
        "expected the first prove after auto-setup to be a cache hit (minimize once), got:\n{o}"
    );
}

#[test]
fn corrupt_cache_is_ignored_and_recomputes() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let target = tmp.path().join("target");
    assert!(xark_build("bignum_ops", &out, &target).0, "build failed");
    assert!(setup(&out, true).0, "setup --cache failed");

    // Corrupt the cache: prove must fall back to a recompute (never panic) and
    // still produce a verifying proof.
    std::fs::write(out.join("r1cs.min.wcz"), b"XBC1 not a real cache").unwrap();
    let (ok, o) = prove(&out, false);
    assert!(ok, "prove with a corrupt cache failed: {o}");
    assert!(
        o.contains("cached=false"),
        "a corrupt cache must be ignored:\n{o}"
    );
}
