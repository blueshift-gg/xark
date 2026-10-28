//! Minimized-circuit cache end-to-end behavior. A `minimized`-form key proves from
//! the `r1cs.stream` setup writes next to it (the minimized rows, so `prove` never
//! re-runs the minimize) and still verifies; an absent or corrupt `r1cs.stream`
//! falls back to rebuilding the minimized circuit, which also verifies, and
//! `prove --cache` writes it back. Uses `bignum_ops` — a function (v8) circuit —
//! with `--r1cs-form minimized` so the cache path is always exercised (`auto` may
//! pick `reduced`, which streams from `circuit.xbc` and never minimizes).

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

fn setup(out: &Path) -> (bool, String) {
    let mut c = Command::new(xark_bin());
    c.arg("setup")
        .arg(out)
        .arg("--insecure-dev-mode")
        .arg("--deterministic-rng")
        .arg("1")
        .arg("--r1cs-form")
        .arg("minimized");
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

    // Setup writes the minimized rows (`r1cs.stream`) next to the keys.
    let (ok, err) = setup(&out);
    assert!(ok, "setup failed: {err}");
    let cache = out.join("r1cs.stream");
    assert!(cache.exists(), "setup did not write {}", cache.display());

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
    // No explicit setup — a plain `prove` (no `--cache`). Auto-setup runs because
    // no proving key exists yet.
    let (ok, o) = prove(&out, false);
    assert!(ok, "bare auto-setup prove failed: {o}");
    // A `minimized` key comes with its rows; a `reduced` one streams `circuit.xbc`.
    let meta = std::fs::read_to_string(out.join("metadata.json")).unwrap();
    if meta.contains("\"minimized\"") {
        assert!(
            out.join("r1cs.stream").exists(),
            "auto-setup should have written {}",
            out.join("r1cs.stream").display()
        );
    }
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
    assert!(setup(&out).0, "setup failed");

    // Corrupt the cache: prove must fall back to a recompute (never panic) and
    // still produce a verifying proof.
    std::fs::write(out.join("r1cs.stream"), b"XRS1 not a real row file").unwrap();
    let (ok, o) = prove(&out, false);
    assert!(ok, "prove with a corrupt cache failed: {o}");
    assert!(
        o.contains("cached=false"),
        "a corrupt cache must be ignored:\n{o}"
    );
}
