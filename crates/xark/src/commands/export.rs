//! `xark export` — generate a self-contained, importable Solana verifier
//! **crate** for a circuit, with its verifying key embedded at compile time.
//!
//! Your Solana program depends on the generated crate and calls
//! `verify(...)` / `verify_instruction_data(...)`. When the circuit changes,
//! re-run `xark export` and the generated crate is the *only* thing that
//! updates — your program code stays put.
//!
//! Layout written under `--out` (which is the crate root):
//!
//! ```text
//! <out>/
//!   Cargo.toml                 # depends on xark-verifier
//!   src/lib.rs                 # const VK<N> + verify(...) (generated)
//!   verifying_key.solana.bin   # LE VK, embedded by lib.rs
//!   proof.solana.bin           # sample proof (256 B)
//!   public_inputs.solana.bin   # sample public inputs (N * 32 B LE)
//!   instruction_data.bin       # proof || public_inputs (the on-chain ix data)
//!   README.md
//!   client_call_example.rs     # off-chain submission snippet
//! ```
//!
//! All field elements are 32-byte little-endian, matching the `alt_bn128` LE
//! syscalls and `xark-verifier`. This command is frontend-agnostic (vk →
//! verifier); only its input-path inference is unified-specific.

use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use clap::Args;

use xark_backend::keys::Groth16Keys;
use xark_backend::proof::ProofBundle;
use xark_backend::serialization::read_public_inputs;
use xark_backend::solana::{
    assemble_proof_bytes_le, assemble_public_inputs_bytes_le, assemble_vk_bytes_le,
};

use crate::xark_project::XarkProject;

#[derive(Args, Debug)]
pub struct ExportArgs {
    /// Circuit crate directory (or its `target/xark/` output dir). Defaults to
    /// the current directory; paths are inferred from `target/xark/`.
    #[arg(value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,

    /// Verifying key. Inferred as `target/xark/vk.bin` when omitted.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub verifying_key: Option<PathBuf>,
    /// Proof, bundled as the generated crate's self-test vector. Inferred as
    /// `target/xark/proof.bin`.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub proof: Option<PathBuf>,
    /// Public inputs file produced by `xark prove`. Inferred as
    /// `target/xark/public_inputs.bin`.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub public_inputs: Option<PathBuf>,
    /// Output directory — the root of the generated verifier crate. Inferred as
    /// `target/xark/verifier`.
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub out: Option<PathBuf>,
    /// Name for the generated crate. Defaults to the `--out` directory name.
    #[arg(long)]
    pub crate_name: Option<String>,
    /// Permit exporting a verifier for a non-production (dev-mode) key. Local
    /// testing only — never deploy a verifier built this way.
    #[arg(long)]
    pub allow_insecure: bool,
}

pub fn run(args: ExportArgs) -> Result<()> {
    let project = XarkProject::resolve(args.path.clone())?;
    let vk_path = args
        .verifying_key
        .clone()
        .unwrap_or_else(|| project.verifying_key());
    let proof_path = args.proof.clone().unwrap_or_else(|| project.proof());
    let public_inputs_path = args
        .public_inputs
        .clone()
        .unwrap_or_else(|| project.public_inputs());
    let out_dir = args.out.clone().unwrap_or_else(|| project.export_dir());

    // ---- Load inputs ------------------------------------------------------
    let vk = Groth16Keys::read_verifying_key(&vk_path)
        .with_context(|| format!("reading verifying key {}", vk_path.display()))?;
    // refuse a non-production key unless `--allow-insecure` is passed
    check_key_safe_for_export(&vk_path, args.allow_insecure)?;
    let proof = ProofBundle::read_proof(&proof_path)
        .with_context(|| format!("reading proof {}", proof_path.display()))?;
    let public_inputs = read_public_inputs(&public_inputs_path)
        .with_context(|| format!("reading public inputs {}", public_inputs_path.display()))?;

    let num_public_inputs = public_inputs.len();
    let ic_len = vk.gamma_abc_g1.len();
    if ic_len != num_public_inputs + 1 {
        anyhow::bail!(
            "VK ic length ({ic_len}) does not match num_public_inputs+1 ({}); \
             ic_len must equal num_public_inputs + 1 in Groth16",
            num_public_inputs + 1
        );
    }

    // ---- Encode (little-endian, the only on-chain wire format) -----------
    let vk_bytes = assemble_vk_bytes_le(&vk);
    let proof_bytes = assemble_proof_bytes_le(&proof);
    let public_inputs_bytes = assemble_public_inputs_bytes_le(&public_inputs);
    let mut instruction_data = Vec::with_capacity(proof_bytes.len() + public_inputs_bytes.len());
    instruction_data.extend_from_slice(&proof_bytes);
    instruction_data.extend_from_slice(&public_inputs_bytes);

    let crate_name = sanitize_crate_name(args.crate_name.as_deref().unwrap_or_else(|| {
        out_dir
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("groth16-verifier")
    }));

    // ---- Write the generated crate ---------------------------------------
    let out = &out_dir;
    fs::create_dir_all(out.join("src"))
        .with_context(|| format!("creating {}", out.join("src").display()))?;

    write_file(out, "verifying_key.solana.bin", &vk_bytes)?;
    write_file(out, "proof.solana.bin", &proof_bytes)?;
    write_file(out, "public_inputs.solana.bin", &public_inputs_bytes)?;
    write_file(out, "instruction_data.bin", &instruction_data)?;

    write_str(&out.join("Cargo.toml"), &gen_cargo_toml(&crate_name))?;
    write_str(&out.join("src/lib.rs"), &gen_lib_rs(num_public_inputs))?;
    write_str(
        &out.join("README.md"),
        &gen_readme(&crate_name, num_public_inputs),
    )?;
    write_str(&out.join("client_call_example.rs"), CLIENT_CALL_EXAMPLE)?;

    println!(
        "Generated verifier crate `{crate_name}` at {} ({} public input(s), \
         VK = {} B). Depend on it from your Solana program and call \
         `verify_instruction_data(...)`.",
        out.display(),
        num_public_inputs,
        vk_bytes.len(),
    );
    println!(
        "{}",
        crate::style::brand("✅ On-chain verifier crate ready (verifying key embedded).")
    );
    let p = super::path_arg(&args.path);
    println!(
        "\n{}",
        crate::style::next_steps(&[
            (
                format!("xark client {p}"),
                "scaffold a TypeScript client (verify + calldata)",
            ),
            (
                "cargo test".to_string(),
                "run inside the generated crate to self-check the bundled proof",
            ),
        ])
    );
    Ok(())
}

/// Reject (or with `--allow-insecure`, warn) if the verifying key beside
/// `vk_path` was produced by an insecure setup (`metadata.json` not marked
/// `production_safe`).
fn check_key_safe_for_export(vk_path: &Path, allow_insecure: bool) -> Result<()> {
    // production_safe only if a metadata.json beside the key says so
    let production_safe = vk_path
        .parent()
        .and_then(|dir| fs::read_to_string(dir.join("metadata.json")).ok())
        .and_then(|s| serde_json::from_str::<serde_json::Value>(&s).ok())
        .and_then(|v| v.get("production_safe").and_then(|b| b.as_bool()))
        .unwrap_or(false);

    if production_safe {
        return Ok(());
    }
    if allow_insecure {
        eprintln!(
            "{}",
            crate::style::warn(
                "⚠️  Exporting an on-chain verifier for an INSECURE dev-mode key \
                 (--allow-insecure). Its trapdoor is not protected by a trusted-setup \
                 ceremony — do NOT deploy this VK."
            )
        );
        return Ok(());
    }
    anyhow::bail!(
        "refusing to export an on-chain verifier for a non-production key: no \
         metadata.json marks it production_safe. Run `xark setup --ptau-file …` (or the \
         `xark ceremony` flow) first, or pass --allow-insecure for a local-testing verifier \
         you will not deploy."
    )
}

/// Sanitize an arbitrary string into a valid Cargo crate name
/// (`[a-z0-9_-]`, non-empty, not leading with a digit/sep).
fn sanitize_crate_name(s: &str) -> String {
    let mut out: String = s
        .to_ascii_lowercase()
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '-' })
        .collect();
    while out.starts_with(['-', '_']) || out.starts_with(|c: char| c.is_ascii_digit()) {
        out.remove(0);
    }
    let trimmed = out.trim_matches('-').to_string();
    if trimmed.is_empty() {
        "groth16-verifier".to_string()
    } else {
        trimmed
    }
}

/// The `xark-verifier` dependency written into the generated crate: a git
/// source on this repo, **pinned to the exact revision this `xark` binary was
/// built from** (`XARK_GIT_HASH`, the same revision `xark --version` prints).
/// So the generated verifier is byte-for-byte the one that matches your
/// toolchain, and the crate builds on a fresh clone with no sibling checkout —
/// no user input, no `[patch]`. Switch to a plain version once `xark-verifier`
/// is published to crates.io.
///
/// Falls back to an unpinned git source when the revision is unknown (an `xark`
/// built outside a git checkout).
fn verifier_dep() -> String {
    const REPO: &str = "https://github.com/blueshift-gg/xark";
    match env!("XARK_GIT_HASH") {
        "unknown" => format!(r#"{{ git = "{REPO}" }}"#),
        rev => format!(r#"{{ git = "{REPO}", rev = "{rev}" }}"#),
    }
}

fn gen_cargo_toml(name: &str) -> String {
    let verifier_dep = verifier_dep();
    format!(
        r#"# Auto-generated by `xark export` — regenerate to update the embedded VK.
[package]
name = "{name}"
version = "0.1.0"
edition = "2024"

# Standalone: this crate resolves its own lock, independent of the circuit or
# program workspace it lives beside. (Without this, cargo folds it into a
# parent workspace and refuses to build it.)
[workspace]

[dependencies]
# The verifier core, pinned to the xark revision this crate was generated with.
xark-verifier = {verifier_dep}

# `target_os = "solana"` / `target_arch = "bpf"` are Solana-toolchain-only cfg
# values; declare them so a host build with upstream rustc (1.80+) doesn't warn.
[lints.rust]
unexpected_cfgs = {{ level = "warn", check-cfg = [
    'cfg(target_os, values("solana"))',
    'cfg(target_arch, values("bpf"))',
] }}
"#
    )
}

fn gen_lib_rs(n: usize) -> String {
    format!(
        r#"//! Auto-generated by `xark export` — do not edit by hand.
//!
//! Self-contained Groth16 verifier for this circuit ({n} public input(s)).
//! The verifying key is embedded at compile time. Depend on this crate from
//! your Solana program and call [`verify`] / [`verify_instruction_data`];
//! re-run `xark export` when the circuit changes and this crate is the only
//! thing that updates.
#![cfg_attr(any(target_os = "solana", target_arch = "bpf"), no_std)]

pub use xark_verifier::{{Proof, VerifierError, Verifier}};

/// Number of public inputs this circuit exposes.
pub const NUM_PUBLIC_INPUTS: usize = {n};

/// The verifier for this circuit, embedding the verifying key at compile
/// time. Its byte length is checked against `NUM_PUBLIC_INPUTS` at compile
/// time.
pub const VERIFIER: Verifier<NUM_PUBLIC_INPUTS> =
    Verifier::from_le_bytes(include_bytes!("../verifying_key.solana.bin"));

/// Raw LE verifying-key wire bytes (for the dynamic byte API).
pub const VK_BYTES: &[u8] = include_bytes!("../verifying_key.solana.bin");

/// Verify `proof` against `public_inputs`. Returns `false` on any failure —
/// a non-holding pairing, a malformed point, or a non-canonical public input.
///
/// This matches the on-chain `alt_bn128` syscall, which masks the unused top
/// bits of each coordinate limb. If you need to reject non-canonical
/// *coordinate* encodings as well — e.g. when proof bytes are hashed, signed,
/// or used as a replay/dedup key — use [`verify_strict`].
#[inline]
pub fn verify(proof: &Proof, public_inputs: &[[u8; 32]; NUM_PUBLIC_INPUTS]) -> bool {{
    VERIFIER.verify(proof, public_inputs)
}}

/// Strict [`verify`]: additionally rejects any proof/VK coordinate whose
/// encoding is non-canonical (`>= q`, e.g. an unused top bit set). `xark`
/// proofs are always canonical, so this never rejects an honest proof — it
/// only removes byte-level proof malleability.
#[inline]
pub fn verify_strict(proof: &Proof, public_inputs: &[[u8; 32]; NUM_PUBLIC_INPUTS]) -> bool {{
    VERIFIER.verify_strict(proof, public_inputs)
}}

/// Verify from raw instruction data laid out as
/// `proof (256 B) || public_inputs ({n} * 32 B)` — the shape your program
/// receives in its instruction data. Returns `false` on any failure.
#[inline]
pub fn verify_instruction_data(data: &[u8]) -> bool {{
    xark_verifier::verify_proof_only(VK_BYTES, data).unwrap_or(false)
}}

/// Strict [`verify_instruction_data`]; see [`verify_strict`].
#[inline]
pub fn verify_instruction_data_strict(data: &[u8]) -> bool {{
    xark_verifier::verify_proof_only_strict(VK_BYTES, data).unwrap_or(false)
}}

#[cfg(test)]
mod tests {{
    /// The proof bundled at export time verifies against the embedded VK.
    #[test]
    fn bundled_proof_verifies() {{
        assert!(super::verify_instruction_data(include_bytes!(
            "../instruction_data.bin"
        )));
    }}
}}
"#
    )
}

fn gen_readme(name: &str, n: usize) -> String {
    let ident = name.replace('-', "_");
    format!(
        r#"# {name}

Auto-generated Solana Groth16 verifier for a circuit with **{n} public
input(s)**. The verifying key is embedded; re-run `xark export` to regenerate
when the circuit changes — this crate is the only dependency your program
updates.

## Use from your Solana program

```toml
[dependencies]
{name} = {{ path = "path/to/{name}" }}   # or a git/published source
```

```rust
// instruction_data = proof (256 B) || public_inputs ({n} * 32 B)
if {ident}::verify_instruction_data(instruction_data) {{
    // proof valid — proceed
}}
```

Or, with proof and public inputs already separated:

```rust
let ok = {ident}::verify(&proof, &public_inputs); // public_inputs: &[[u8; 32]; {n}]
```

`cargo test` in this crate verifies the bundled sample proof against the
embedded VK. `client_call_example.rs` shows how to submit a proof off-chain.
"#
    )
}

fn write_file(dir: &Path, name: &str, bytes: &[u8]) -> Result<()> {
    let path = dir.join(name);
    fs::write(&path, bytes).with_context(|| format!("writing {}", path.display()))?;
    Ok(())
}

fn write_str(path: &Path, contents: &str) -> Result<()> {
    fs::write(path, contents).with_context(|| format!("writing {}", path.display()))?;
    Ok(())
}

// -- Off-chain client snippet -------------------------------------------------

const CLIENT_CALL_EXAMPLE: &str = r#"//! Submit an xark-exported Groth16 proof to your on-chain verifier program.
//!
//! Your program embeds the verifying key via the generated verifier crate
//! (`<crate>::verify_instruction_data(...)`); the client just submits
//! `instruction_data.bin` (= `proof_bytes || public_inputs`, no VK).
//!
//! Uses Anza's broken-out client crates rather than the monolithic
//! `solana-sdk`. Copy this file into a fresh Cargo project with:
//!
//! ```toml
//! [dependencies]
//! anyhow = "1"
//! solana-address = "2"
//! solana-client = "2"
//! solana-commitment-config = "3"
//! solana-instruction = "3"
//! solana-keypair = "3"
//! solana-message = "3"
//! solana-signer = "3"
//! solana-transaction = "3"
//! ```

use std::str::FromStr;

use anyhow::Result;
use solana_address::Address;
use solana_client::rpc_client::RpcClient;
use solana_commitment_config::CommitmentConfig;
use solana_instruction::Instruction;
use solana_keypair::read_keypair_file;
use solana_signer::Signer;
use solana_transaction::Transaction;

// ---- Fill these in ---------------------------------------------------------
const PROGRAM_ID: &str = "REPLACE_WITH_DEPLOYED_PROGRAM_ID";
const RPC_URL: &str = "https://api.devnet.solana.com";
/// Absolute path to the `instruction_data.bin` produced by `xark export`.
/// Contents: `proof_bytes (256 B) || public_inputs (N * 32 B)`.
const INSTRUCTION_DATA_PATH: &str = "/absolute/path/to/instruction_data.bin";
const PAYER_KEYPAIR_PATH: &str = "/absolute/path/to/payer.json";

fn main() -> Result<()> {
    let instruction_data = std::fs::read(INSTRUCTION_DATA_PATH)?;
    let program_id = Address::from_str(PROGRAM_ID)?;
    let ix = Instruction {
        program_id,
        accounts: vec![],
        data: instruction_data,
    };
    let rpc = RpcClient::new_with_commitment(RPC_URL.to_string(), CommitmentConfig::confirmed());
    let payer = read_keypair_file(PAYER_KEYPAIR_PATH)
        .map_err(|e| anyhow::anyhow!("read keypair: {e}"))?;
    let blockhash = rpc.get_latest_blockhash()?;
    let tx =
        Transaction::new_signed_with_payer(&[ix], Some(&payer.pubkey()), &[&payer], blockhash);
    let sig = rpc.send_and_confirm_transaction(&tx)?;
    println!("Proof verified on-chain. Signature: {sig}");
    Ok(())
}
"#;

#[cfg(test)]
mod tests {
    use super::{gen_cargo_toml, verifier_dep};

    #[test]
    fn generated_manifest_is_standalone_and_git_sourced() {
        let manifest = gen_cargo_toml("example-verifier");

        // Standalone so cargo doesn't fold it into a neighbouring workspace.
        assert!(manifest.contains("\n[workspace]\n"));
        // A GitHub git source (bare or rev-pinned) — never a version req the
        // unpublished crate can't resolve, never a local path.
        assert!(manifest.contains(r#"xark-verifier = { git = "https://github.com/blueshift-gg/xark""#));
    }

    #[test]
    fn verifier_dep_pins_the_build_revision() {
        // In a git checkout (as in CI/tests) the dep pins `rev` to the exact
        // revision this binary was built from; otherwise it's an unpinned git
        // source. Either way it targets GitHub and takes no user input.
        let dep = verifier_dep();
        assert!(dep.starts_with(r#"{ git = "https://github.com/blueshift-gg/xark""#));
        if env!("XARK_GIT_HASH") != "unknown" {
            assert!(dep.contains(&format!(r#"rev = "{}""#, env!("XARK_GIT_HASH"))));
        }
    }
}
