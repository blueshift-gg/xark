use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::Args;

use groth16_backend::keys::Groth16Keys;
use groth16_backend::serialization::{canonical_write_to_file, VerifyingKeyJson};

#[derive(Args, Debug)]
pub struct WriteVkArgs {
    /// Path to an existing proving key.
    #[arg(long)]
    pub proving_key: PathBuf,
    /// Output path. The extension (`.json` vs `.bin`) controls the format.
    #[arg(long)]
    pub out: PathBuf,
}

pub fn run(args: WriteVkArgs) -> Result<()> {
    let pk = Groth16Keys::read_proving_key(&args.proving_key)
        .with_context(|| format!("reading proving key {}", args.proving_key.display()))?;
    let vk = pk.vk.clone();

    let ext = args.out.extension().and_then(|s| s.to_str()).unwrap_or("");
    match ext {
        "json" => {
            let json = VerifyingKeyJson::from_vk(&vk);
            fs::write(&args.out, serde_json::to_string_pretty(&json)?)
                .with_context(|| format!("writing {}", args.out.display()))?;
        }
        _ => {
            canonical_write_to_file(&vk, &args.out)?;
        }
    }
    println!("Wrote {}", args.out.display());
    Ok(())
}
