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
    /// Circuit crate directory (or its `target/xark/<name>/` output dir). Defaults to
    /// the current directory; paths are inferred from `target/xark/<name>/`.
    #[arg(value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,

    /// Verifying key. Inferred as `target/xark/<name>/vk.bin` when omitted.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub verifying_key: Option<PathBuf>,
    /// Proof, bundled as the generated crate's self-test vector. Inferred as
    /// `target/xark/<name>/proof.bin`.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub proof: Option<PathBuf>,
    /// Public inputs file produced by `xark prove`. Inferred as
    /// `target/xark/<name>/public_inputs.bin`.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub public_inputs: Option<PathBuf>,
    /// Output directory — the root of the generated verifier crate (a warning if it
    /// isn't empty; a `Cargo.toml` or `src/lib.rs` it didn't write is never
    /// replaced). Inferred as `target/xark/<name>/verifier`.
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
    // The export carries the keys as they are: a newer source means they may be for
    // an older circuit.
    if project.circuit_xbc().exists()
        && let Some(why) = crate::cli::stale_build(&project.xark_dir, "circuit.xbc", None)
    {
        eprintln!(
            "{} {why}: these keys may be for an older circuit (run `xark build` and \
             `xark setup`, then export again)",
            crate::style::warn("warning:")
        );
    }
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

    // Load inputs.
    let vk = super::read_artifact(
        &vk_path,
        "verifying key",
        "xark setup",
        "run `xark setup` first?",
        || Groth16Keys::read_verifying_key(&vk_path),
    )?;
    check_key_safe_for_export(&vk_path, args.allow_insecure)?;
    super::ensure_key_matches_circuit(&vk_path, &project.circuit_xbc())?;
    let proof = super::read_artifact(
        &proof_path,
        "proof",
        "xark prove",
        "run `xark prove` first?",
        || ProofBundle::read_proof(&proof_path),
    )?;
    let public_inputs = super::read_artifact(
        &public_inputs_path,
        "public inputs file",
        "xark prove",
        "run `xark prove` first?",
        || read_public_inputs(&public_inputs_path),
    )?;

    let num_public_inputs = public_inputs.len();
    let ic_len = vk.gamma_abc_g1.len();
    if ic_len != num_public_inputs + 1 {
        anyhow::bail!(
            "VK ic length ({ic_len}) does not match num_public_inputs+1 ({}); \
             ic_len must equal num_public_inputs + 1 in Groth16",
            num_public_inputs + 1
        );
    }

    // The proof is the generated crate's self-test: one that doesn't verify (a
    // proof from an earlier key) would only fail there, after the export.
    if !xark_backend::verify(&vk, &proof, &public_inputs)? {
        anyhow::bail!(
            "the proof {} doesn't verify with {}: run `xark prove` again",
            proof_path.display(),
            vk_path.display()
        );
    }

    // Encode (little-endian, the only on-chain wire format).
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

    // Write the generated crate: over an earlier export, never over anything
    // else (an `--out` naming your own program must not lose its code).
    let out = &out_dir;
    for (file, marker) in [
        ("Cargo.toml", "# Auto-generated by `xark export`"),
        ("src/lib.rs", "//! Auto-generated by `xark export`"),
    ] {
        if let Ok(text) = fs::read_to_string(out.join(file))
            && !text.starts_with(marker)
        {
            anyhow::bail!(
                "{} exists and wasn't written by `xark export`; refusing to overwrite it \
                 (pick a new --out directory)",
                out.join(file).display()
            );
        }
    }
    if args.out.is_some() {
        super::warn_if_not_empty(out, "verifier crate");
    }
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
                "generate a typed TypeScript client (prove + verify in JS)",
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
    // production_safe only if a metadata.json beside the key says so.
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

/// The `xark-verifier` dependency written into the generated crate: pinned to
/// the crates.io version matching this `xark` binary (`CARGO_PKG_VERSION`, the
/// same version `xark --version` prints). `xark-verifier` and `xark-cli` share
/// the workspace version and are published in lockstep, so an exact-match req
/// resolves to the verifier that matches the CLI that generated the crate.
///
/// Resolved from crates.io — no git source, no sibling checkout, no user input,
/// no `[patch]`; a fresh clone builds with just `cargo build`.
fn verifier_dep() -> String {
    format!(r#""={}""#, env!("CARGO_PKG_VERSION"))
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
# The verifier core, pinned to the crates.io version of the `xark` CLI that
# generated this crate.
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
/// bits of each coordinate limb. To also reject non-canonical *coordinate*
/// encodings, use [`verify_strict`]. Neither makes a proof's bytes unique:
/// Groth16 proofs are re-randomizable, so anyone holding a valid proof can
/// derive a different valid proof of the same statement. Never key replay
/// protection on proof bytes; put it in the public inputs (a nullifier, nonce
/// or signer the circuit binds).
#[inline]
pub fn verify(proof: &Proof, public_inputs: &[[u8; 32]; NUM_PUBLIC_INPUTS]) -> bool {{
    VERIFIER.verify(proof, public_inputs)
}}

/// Strict [`verify`]: additionally rejects any proof/VK coordinate whose
/// encoding is non-canonical (`>= q`, e.g. an unused top bit set). `xark`
/// proofs are always canonical, so this never rejects an honest proof. It
/// removes *encoding* malleability only: a re-randomized proof is still
/// accepted (see [`verify`]).
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

The proof comes in the instruction data (256 bytes: a client's `proof.toBytes()`);
the public inputs are what your program requires, from its own state (a policy, a
root, a nullifier), each 32 bytes little-endian:

```rust
let Some(proof) = instruction_data.first_chunk::<256>() else {{
    return Err(ProgramError::InvalidInstructionData);
}};
let proof = {ident}::Proof::from_le_bytes(proof);
let public_inputs: [[u8; 32]; {n}] = [/* from your program's state */];
if !{ident}::verify(&proof, &public_inputs) {{
    return Err(ProgramError::InvalidArgument);
}}
```

When the transaction does carry the public inputs too (`proof || public_inputs`),
`{ident}::verify_instruction_data(instruction_data)` checks both.

## Replay protection

A valid proof is not unique: anyone holding one can re-randomize it into a
different valid proof of the same public inputs (a property of Groth16;
`verify_strict` does not change it). So never use proof bytes, or their hash,
as a replay or "already used" key. Put replay protection in the public inputs
instead: a nullifier or nonce the circuit derives from a secret, or the signer
or context the proof is for, and record *that* on-chain.

`cargo test` in this crate verifies the bundled sample proof against the
embedded VK. `instruction_data.bin` is that proof as your program receives it
(`proof || public_inputs`): send those bytes as an instruction's data, in a
transaction built however your client builds them. A TypeScript client from
`xark client` sends a proof in this format: `proof.toBytes()`.
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

#[cfg(test)]
mod tests {
    use super::{gen_cargo_toml, verifier_dep};

    #[test]
    fn generated_manifest_is_standalone_and_version_pinned() {
        let manifest = gen_cargo_toml("example-verifier");

        // Standalone so cargo doesn't fold it into a neighbouring workspace.
        assert!(manifest.contains("\n[workspace]\n"));
        // A crates.io version req exact-pinned to this CLI's version — never a
        // git source, never a local path.
        assert!(manifest.contains(&format!(
            r#"xark-verifier = "={}""#,
            env!("CARGO_PKG_VERSION")
        )));
    }

    #[test]
    fn verifier_dep_pins_the_cli_version() {
        // The dep is an exact-match req on this binary's own version, so the
        // generated crate resolves the verifier that matches the CLI from
        // crates.io — no git, no user input.
        assert_eq!(
            verifier_dep(),
            format!(r#""={}""#, env!("CARGO_PKG_VERSION"))
        );
    }
}
