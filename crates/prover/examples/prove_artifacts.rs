//! Prove and verify from a directory of `xark build` / `xark setup` artifacts
//! with [`xark_prover::artifacts::ArtifactProver`]:
//!
//! ```sh
//! cargo run --release -p xark-prover --example prove_artifacts -- \
//!     target/test-out/cube '{"secret": "3", "result": "27"}'
//! ```
//!
//! Reads `circuit.xbc` and `pk.bin`, and `r1cs.min.wcz` when `xark setup
//! --cache` wrote one. Exits non-zero unless the proof verifies.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::time::Instant;

use xark_prover::artifacts::ArtifactProver;

fn main() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let dir = PathBuf::from(
        args.next()
            .ok_or("usage: prove_artifacts <dir> <inputs-json>")?,
    );
    let inputs: BTreeMap<String, serde_json::Value> =
        serde_json::from_str(&args.next().ok_or("missing <inputs-json>")?)
            .map_err(|e| format!("inputs: {e}"))?;
    let inputs: BTreeMap<String, String> = inputs
        .into_iter()
        .map(|(k, v)| {
            (
                k,
                v.as_str()
                    .map(str::to_owned)
                    .unwrap_or_else(|| v.to_string()),
            )
        })
        .collect();
    let read = |name: &str| std::fs::read(dir.join(name)).map_err(|e| format!("{name}: {e}"));

    let t = Instant::now();
    let xbc = read("circuit.xbc")?;
    let pk = read("pk.bin")?;
    let prover = match read("r1cs.min.wcz") {
        Ok(cache) => ArtifactProver::load_with_r1cs_cache(&xbc, &cache, &pk)?,
        Err(_) => ArtifactProver::load(&xbc, &pk)?,
    };
    println!("loaded {prover:?} in {:?}", t.elapsed());

    let t = Instant::now();
    let (proof, public) = prover.prove(
        inputs.iter().map(|(k, v)| (k.as_str(), v.as_str())),
        &mut rand::rngs::OsRng,
    )?;
    println!(
        "proved in {:?}, {} public inputs",
        t.elapsed(),
        public.len()
    );
    if !prover.verify(&proof, &public)? {
        return Err("the proof does not verify".into());
    }
    println!("verified");
    Ok(())
}
