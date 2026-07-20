//! Diagnostic: what does the minimize pass actually remove from the raw binary
//! expansion? Run: `cargo test -p xark-tests --release --test minimize_analysis
//! -- --ignored --nocapture`. Read-only; no fixtures touched.
//!
//! For each analyzed circuit it expands `circuit.xbc` to the raw flat R1CS, runs
//! the guarded minimizer, and reports the delta: constraint / var / nonzero counts
//! before and after, plus a histogram of the *removed* internal vars keyed by their
//! name prefix (which encodes the codegen op that emitted them) and a count of the
//! raw "linear-identity" constraints (`A·const = C` — the plug/copy shape the
//! eliminator collapses). This says how much of the gap is codegen artifact.

use std::path::PathBuf;

use xark_ir::R1csProgram;

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn nonzeros(p: &R1csProgram) -> usize {
    p.constraints
        .iter()
        .map(|c| c.a.terms.len() + c.b.terms.len() + c.c.terms.len())
        .sum()
}

/// A constraint is "linear" (an eliminable candidate) when one multiplicand has no
/// variable terms — i.e. `A·const = C`, the shape a plug/copy/assert-eq collapses to.
fn linear_identity_count(p: &R1csProgram) -> usize {
    p.constraints
        .iter()
        .filter(|c| c.a.terms.is_empty() || c.b.terms.is_empty())
        .count()
}

fn analyze(label: &str, xbc_path: &PathBuf) {
    let Ok(bytes) = std::fs::read(xbc_path) else {
        eprintln!("[{label}] SKIP — no xbc at {}", xbc_path.display());
        return;
    };
    let cp = xark_ir::function_decode::expand_function_blob(&bytes).expect("expand circuit.xbc");
    let raw = cp.to_r1cs();
    let fft = |n: usize| n.next_power_of_two().trailing_zeros();

    println!("\n===== {label} =====");
    println!(
        "raw:            {:>9} constraints  {:>10} nonzeros  {:>9} vars  FFT 2^{}  (linear-identity constraints: {})",
        raw.constraints.len(),
        nonzeros(&raw),
        raw.variables.len(),
        fft(raw.constraints.len()),
        linear_identity_count(&raw),
    );
    // Sweep the fill threshold: fill=1/2 does only cheap copy/rename eliminations
    // (no densification); higher fills substitute denser definitions in, trading
    // constraint count for nonzeros. `usize::MAX` (unguarded) is skipped — it OOMs
    // on the large flat circuits, which is the whole reason the guard exists.
    for &fill in &[1usize, 2, 4, 8, 16, 32] {
        let m = xark_ir::minimize::minimize_with_fill(&raw, fill);
        let nz = nonzeros(&m);
        println!(
            "  fill={:<3} {:>9} constraints ({:+.2}%)  {:>10} nonzeros ({:+.1}%)  {:>9} vars  FFT 2^{}",
            fill,
            m.constraints.len(),
            100.0 * (m.constraints.len() as f64 - raw.constraints.len() as f64)
                / raw.constraints.len() as f64,
            nz,
            100.0 * (nz as f64 - nonzeros(&raw) as f64) / nonzeros(&raw).max(1) as f64,
            m.variables.len(),
            fft(m.constraints.len()),
        );
    }
}

#[test]
#[ignore = "diagnostic; run explicitly with --ignored --nocapture"]
fn analyze_minimize_removals() {
    let work = manifest_dir().join("target/regen-work");
    for dir in [
        "poseidon2",
        "ec_incomplete",
        "blake3",
        "sha256",
        "keccak",
        "aes",
        "secp256k1_ecdsa",
        "secp256r1_ecdsa",
    ] {
        analyze(dir, &work.join(dir).join("circuit.xbc"));
    }
}
