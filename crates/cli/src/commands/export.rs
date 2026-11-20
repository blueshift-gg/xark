//! `xark export` — generate a self-contained, importable Solana verifier
//! **crate** for a circuit, with its verifying key embedded at compile time.
//!
//! Your Solana program depends on the generated crate and calls
//! `verify(...)`. When the circuit changes,
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
//!   proof.solana.bin           # sample proof (256 B)            } when there is a proof
//!   public_inputs.solana.bin   # sample public inputs (N * 32 B)  } (`xark prove`):
//!   instruction_data.bin       # proof || public_inputs          } the crate's self-test
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
    /// the current directory; the paths below are inferred from it.
    #[arg(value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,

    /// Verifying key. Inferred when omitted: `keys/<name>/vk.bin` in a project, and
    /// otherwise `<crate>/target/xark/<name>/vk.bin`.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub verifying_key: Option<PathBuf>,
    /// Proof, bundled as the generated crate's self-test vector. Inferred as
    /// `<crate>/target/xark/<name>/proof.bin`; without one (or with one for another
    /// key), the crate has no self-test.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub proof: Option<PathBuf>,
    /// Public inputs file produced by `xark prove`. Inferred as
    /// `<crate>/target/xark/<name>/public_inputs.bin`.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub public_inputs: Option<PathBuf>,
    /// Output directory — the root of the generated verifier crate (a warning if it
    /// isn't empty; a `Cargo.toml` or `src/lib.rs` it didn't write is never
    /// replaced). Defaults to `clients/<name>/rust/` in a project, and otherwise to
    /// `<crate>/clients/rust/`, beside the circuit's sources (tracked by git, kept by
    /// `cargo clean`); for a build output outside a crate's `target/`, its
    /// `clients/rust/`.
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub out: Option<PathBuf>,
    /// Name for the generated crate. Defaults to `<name>-client`, or with `--out`
    /// to that directory's name.
    #[arg(long)]
    pub crate_name: Option<String>,
    /// Write the manifest as a workspace member even when `--out` is outside
    /// `clients/`. Used by `xark build --check` to stage the comparison.
    #[arg(long, hide = true)]
    pub member: bool,
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
    // A proof given by flag must be there and verify; the inferred one is a sample,
    // left out when missing or made with another key.
    let explicit = args.proof.is_some() || args.public_inputs.is_some();
    let out_dir = args
        .out
        .clone()
        .unwrap_or_else(|| project.clients_dir().join("rust"));

    // Load inputs.
    let vk = super::read_artifact(
        &vk_path,
        "verifying key",
        "xark setup",
        "run `xark setup` first?",
        || Groth16Keys::read_verifying_key(&vk_path),
    )?;
    // Any key exports; the crate says how it was made (`SETUP`, and its README).
    let trust = super::setup_trust(vk_path.parent().unwrap_or(Path::new(".")));
    super::ensure_key_matches_circuit(&vk_path, &project.circuit_xbc())?;
    let num_public_inputs = vk.gamma_abc_g1.len().saturating_sub(1);
    // The sample a crate already has, while it still verifies with this key: kept
    // over any other, so regenerating doesn't change the crate (a proof is
    // randomized, and only whoever proved last has one) and a fresh clone's build
    // leaves the committed crate as it was.
    let kept = if explicit {
        None
    } else {
        existing_sample(&out_dir, &vk, num_public_inputs)
    };
    let sample = if kept.is_some() {
        kept
    } else if explicit || proof_path.exists() {
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
        if public_inputs.len() != num_public_inputs {
            anyhow::bail!(
                "{} holds {} public input(s), but the verifying key takes {num_public_inputs}",
                public_inputs_path.display(),
                public_inputs.len()
            );
        }
        // The proof is the generated crate's self-test: one that doesn't verify (a
        // proof from an earlier key) would only fail there, after the export.
        if xark_groth16::verify(&vk, &public_inputs, &proof)? {
            Some((proof, public_inputs))
        } else if explicit {
            anyhow::bail!(
                "the proof {} doesn't verify with {}: run `xark prove` again",
                proof_path.display(),
                vk_path.display()
            );
        } else {
            eprintln!(
                "{} {} is for another key, so the crate gets no self-test (run `xark \
                 prove` and export again to bundle one)",
                crate::style::warn("warning:"),
                proof_path.display()
            );
            None
        }
    } else {
        None
    };

    // Encode (little-endian, the only on-chain wire format).
    let vk_bytes = assemble_vk_bytes_le(&vk);

    // `clients/rust/` says nothing about the circuit: by default the crate is named
    // after the package. An earlier export's crate keeps its name, so the programs
    // depending on it still build (0.4.0 named it `<name>-verifier`); the check
    // below refuses a `Cargo.toml` that export didn't write before anything uses it.
    let default_name = match (&args.out, project.name()) {
        (None, Some(name)) => client_crate_name(&name),
        _ => out_dir
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("groth16-client")
            .to_string(),
    };
    let crate_name = match &args.crate_name {
        Some(name) => sanitize_crate_name(name),
        None => crate::xark_project::read_pkg_name(&out_dir)
            .unwrap_or_else(|| sanitize_crate_name(&default_name)),
    };

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
    if args.out.is_some() && !args.member {
        super::warn_if_not_empty(out, "verifier crate");
    }
    fs::create_dir_all(out.join("src"))
        .with_context(|| format!("creating {}", out.join("src").display()))?;

    // Whether this export changed a file: a rebuild that changed nothing says so.
    let mut changed = write_file(out, "verifying_key.solana.bin", &vk_bytes)?;
    const SAMPLE: [&str; 3] = [
        "proof.solana.bin",
        "public_inputs.solana.bin",
        "instruction_data.bin",
    ];
    if let Some((proof, public_inputs)) = &sample {
        let proof_bytes = assemble_proof_bytes_le(proof);
        let public_inputs_bytes = assemble_public_inputs_bytes_le(public_inputs);
        let instruction_data = [proof_bytes.as_slice(), &public_inputs_bytes].concat();
        for (name, bytes) in SAMPLE
            .iter()
            .zip([proof_bytes, public_inputs_bytes, instruction_data])
        {
            changed |= write_file(out, name, &bytes)?;
        }
    } else {
        // An earlier export's sample, for whatever key it had.
        for name in SAMPLE {
            changed |= fs::remove_file(out.join(name)).is_ok();
        }
    }

    // The public inputs by name, from the build's schema (none from a bare key).
    let schema: Option<serde_json::Value> =
        fs::read_to_string(project.xark_dir.join("schema.json"))
            .ok()
            .and_then(|t| serde_json::from_str(&t).ok());
    let typed = schema.as_ref().and_then(|s| {
        super::public_inputs::generate(
            s,
            num_public_inputs,
            sample.as_ref().map(|(_, inputs)| inputs.as_slice()),
        )
    });
    // In a project, the crate is a member of its workspace; otherwise it stands
    // alone, so cargo doesn't fold it into the circuit's.
    // Matched as the workspace globs it (`clients/*/rust`), on the real paths (a
    // `--out` through `..` or a symlink is the same directory).
    let member = args.member
        || project.project_root().is_some_and(|root| {
            match (out.canonicalize(), root.join("clients").canonicalize()) {
                (Ok(o), Ok(clients)) => {
                    o.file_name() == Some("rust".as_ref())
                        && o.parent().and_then(Path::parent) == Some(clients.as_path())
                }
                _ => false,
            }
        });
    changed |= write_str(
        &out.join("Cargo.toml"),
        &gen_cargo_toml(&crate_name, member),
    )?;
    if member
        && !args.member
        && let Some(root) = project.project_root()
    {
        crate::xark_project::sync_members(&root)?;
    }
    changed |= write_str(
        &out.join("src/lib.rs"),
        &gen_lib_rs(num_public_inputs, sample.is_some(), typed.as_ref(), &trust),
    )?;
    changed |= write_str(
        &out.join("README.md"),
        &gen_readme(&crate_name, num_public_inputs, sample.is_some(), &trust),
    )?;

    if !changed {
        println!(
            "{} verifier crate `{crate_name}` at {} is unchanged",
            crate::style::tag(),
            out.display()
        );
        // The key's trust still matters on every run when it's a warning.
        if trust.warn {
            eprintln!(
                "{}",
                crate::style::warn(&format!("⚠️  Key: {}.", trust.summary))
            );
        }
        return Ok(());
    }
    println!(
        "Generated verifier crate `{crate_name}` at {} ({} public input(s), \
         VK = {} B). Depend on it from your Solana program and call \
         `verify(&proof, PublicInputs {{ .. }})`.",
        out.display(),
        num_public_inputs,
        vk_bytes.len(),
    );
    let setup = format!("Key: {}.", trust.summary);
    if trust.warn {
        eprintln!("{}", crate::style::warn(&format!("⚠️  {setup}")));
    } else {
        println!("{setup}");
    }
    println!(
        "{}",
        crate::style::brand("✅ Onchain verifier crate ready (verifying key embedded).")
    );
    let p = super::path_arg(&args.path);
    let mut next = vec![(
        format!("xark client {p}"),
        "generate a typed TypeScript client (prove + verify in JS)",
    )];
    if sample.is_some() {
        next.push((
            "cargo test".to_string(),
            "run inside the generated crate to self-check the bundled proof",
        ));
    }
    println!("\n{}", crate::style::next_steps(&next));
    Ok(())
}

/// The sample proof an earlier export bundled in `out` (`proof.solana.bin`,
/// `public_inputs.solana.bin`), if it verifies with `vk`.
fn existing_sample(
    out: &Path,
    vk: &xark_groth16::VerifyingKey<ark_bn254::Bn254>,
    n: usize,
) -> Option<(xark_groth16::Proof<ark_bn254::Bn254>, Vec<ark_bn254::Fr>)> {
    use ark_serialize::CanonicalDeserialize;
    let proof =
        xark_groth16::solana::decode_proof_le(&fs::read(out.join("proof.solana.bin")).ok()?)
            .ok()?;
    let bytes = fs::read(out.join("public_inputs.solana.bin")).ok()?;
    if bytes.len() != n * 32 {
        return None;
    }
    let inputs: Vec<ark_bn254::Fr> = bytes
        .chunks(32)
        .map(|c| ark_bn254::Fr::deserialize_compressed(c).ok())
        .collect::<Option<_>>()?;
    xark_groth16::verify(vk, &inputs, &proof)
        .unwrap_or(false)
        .then_some((proof, inputs))
}

/// The name `xark export` gives a new client crate for `circuit`
/// (`shielded_transact` → `shielded-transact-client`).
pub(crate) fn client_crate_name(circuit: &str) -> String {
    sanitize_crate_name(&format!("{circuit}-client"))
}

/// Sanitize an arbitrary string into a valid Cargo crate name
/// (`[a-z0-9_-]`, non-empty, not leading with a digit/sep).
pub(crate) fn sanitize_crate_name(s: &str) -> String {
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
        "groth16-client".to_string()
    } else {
        trimmed
    }
}

/// The `xark-verifier` dependency written into the generated crate: pinned to
/// the crates.io version matching this `xark` binary (`CARGO_PKG_VERSION`, the
/// same version `xark --version` prints). `xark-verifier` and `xark-cli` share
/// the workspace version and are published in lockstep, so a compatible `"x.y.z"`
/// req resolves to the verifier that matches the CLI (or a later semver-compatible
/// patch).
///
/// Resolved from crates.io — no git source, no sibling checkout, no user input,
/// no `[patch]`; a fresh clone builds with just `cargo build`.
fn verifier_dep() -> String {
    format!(r#""{}""#, env!("CARGO_PKG_VERSION"))
}

fn gen_cargo_toml(name: &str, member: bool) -> String {
    let verifier_dep = verifier_dep();
    // A member crate inherits the project workspace; a standalone one needs its own
    // `[workspace]` so cargo doesn't fold it into a neighbouring one.
    let workspace = if member { "" } else { "[workspace]\n\n" };
    format!(
        r#"# Auto-generated by `xark export` — re-run to regenerate.
[package]
name = "{name}"
version = "0.1.0"
edition = "2024"

{workspace}[dependencies]
xark-verifier = {verifier_dep}
xark-prover = {{ version = {verifier_dep}, optional = true }}
serde_json = {{ version = "1", optional = true }}

[features]
prover = ["dep:xark-prover", "dep:serde_json"]

# `target_os = "solana"` / `target_arch = "bpf"` are Solana-toolchain-only cfg
# values; declare them so a host build with upstream rustc doesn't warn.
[lints.rust]
unexpected_cfgs = {{ level = "warn", check-cfg = [
    'cfg(target_os, values("solana"))',
    'cfg(target_arch, values("bpf"))',
] }}
"#
    )
}

fn gen_lib_rs(
    n: usize,
    sample: bool,
    typed: Option<&super::public_inputs::Typed>,
    trust: &super::SetupTrust,
) -> String {
    let setup = trust.tag;
    let (inputs, typed_test) = match typed {
        Some(t) => (
            t.items.clone(),
            t.sample
                .as_ref()
                .filter(|_| sample)
                .map_or(String::new(), |lit| {
                    format!(
                        r#"
    /// The sample's public inputs, by name, are its field elements, and verify.
    #[test]
    fn typed_public_inputs_match_the_sample() {{
        let inputs = {lit};
        let fields: Vec<[u8; 32]> = include_bytes!("../public_inputs.solana.bin")
            .chunks(32)
            .map(|c| c.try_into().unwrap())
            .collect();
        assert_eq!(inputs.to_fields().as_slice(), fields.as_slice());
        let proof = Proof::from_le_bytes(include_bytes!("../proof.solana.bin"));
        assert!(verify(&proof, inputs));
    }}
"#
                    )
                }),
        ),
        // Not every input has a Rust form here yet: `verify` takes the field elements
        // (`xark inspect` lists what each one is), packed with `fields` if need be.
        None => (
            "/// How the public inputs become field elements, as the circuit's `#[input]`\n\
             /// makes them.\n\
             pub use xark_verifier::fields;\n"
                .to_string(),
            String::new(),
        ),
    };
    let tests = if sample {
        format!(
            r#"
#[cfg(test)]
mod tests {{
    use super::*;

    /// The proof bundled at export time verifies against the embedded VK, with
    /// its public inputs and only with them.
    #[test]
    fn bundled_proof_verifies() {{
        let proof = Proof::from_le_bytes(include_bytes!("../proof.solana.bin"));
        let mut fields: Fields = [[0; 32]; NUM_PUBLIC_INPUTS];
        for (f, b) in fields
            .iter_mut()
            .zip(include_bytes!("../public_inputs.solana.bin").chunks(32))
        {{
            f.copy_from_slice(b);
        }}
        assert!(verify(&proof, fields));
        if let Some(first) = fields.first_mut() {{
            first[0] ^= 1;
            assert!(!verify(&proof, fields));
        }}
    }}
{typed_test}}}
"#
        )
    } else {
        String::new()
    };
    format!(
        r#"//! Auto-generated by `xark export` — do not edit by hand.
//!
//! Self-contained Groth16 verifier for this circuit ({n} public input(s)).
//! The verifying key is embedded at compile time. Depend on this crate from
//! your Solana program, build the [`PublicInputs`] it requires and call
//! [`verify`]; re-run `xark export` when the circuit changes and this crate is
//! the only thing that updates.
// Generated, and compared byte for byte by `xark build --check`: `cargo fmt` leaves
// it as written, and clippy's lints are for code you write.
#![cfg_attr(rustfmt, rustfmt::skip)]
#![allow(clippy::all)]
#![cfg_attr(any(target_os = "solana", target_arch = "bpf"), no_std)]

pub use xark_verifier::{{Proof, Verifiable, Verifier, VerifierError, XarkError}};

/// Number of public inputs this circuit exposes.
pub const NUM_PUBLIC_INPUTS: usize = {n};

/// How the embedded key was made: `seeded` (anyone with the seed can forge
/// proofs, so for tests only), `single-party` (sound unless whoever ran setup,
/// or a ceremony's one contributor, kept its randomness), `ceremony` (two or
/// more contributors: unless every one did), or `unknown`.
/// A deploy script can refuse a verifier whose `SETUP` it doesn't accept.
pub const SETUP: &str = "{setup}";

/// The verifier for this circuit, embedding the verifying key at compile
/// time. Its byte length is checked against `NUM_PUBLIC_INPUTS` at compile
/// time.
pub const VERIFIER: Verifier<NUM_PUBLIC_INPUTS> =
    Verifier::from_le_bytes(include_bytes!("../verifying_key.solana.bin"));

/// The public inputs as field elements, in proof order, each 32 bytes
/// little-endian: what [`verify`] takes, from anything that converts into it.
pub type Fields = [[u8; 32]; NUM_PUBLIC_INPUTS];

{inputs}
/// Verify `proof` against `inputs`: anything that converts into [`Fields`] (a
/// `PublicInputs`, your own struct with a `From` impl, or the elements
/// themselves). Returns `false` on any failure — a non-holding pairing, a
/// malformed point, or a non-canonical public input.
///
/// This matches the on-chain `alt_bn128` syscall, which masks the unused top
/// bits of each coordinate limb. To also reject non-canonical *coordinate*
/// encodings, use [`verify_strict`]. Neither makes a proof's bytes unique:
/// Groth16 proofs are re-randomizable, so anyone holding a valid proof can
/// derive a different valid proof of the same statement. Never key replay
/// protection on proof bytes; put it in the public inputs (a nullifier, nonce
/// or signer the circuit binds).
pub fn verify(proof: &Proof, inputs: impl Into<Fields>) -> bool {{
    verify_fields(proof, &inputs.into())
}}

/// Strict [`verify`]: additionally rejects any proof/VK coordinate whose
/// encoding is non-canonical (`>= q`, e.g. an unused top bit set). `xark`
/// proofs are always canonical, so this never rejects an honest proof. It
/// removes *encoding* malleability only: a re-randomized proof is still
/// accepted (see [`verify`]).
pub fn verify_strict(proof: &Proof, inputs: impl Into<Fields>) -> bool {{
    verify_fields_strict(proof, &inputs.into())
}}

// Never inlined: inlined into a program's
// entrypoint (as fat LTO does), the pairing check's buffers can take that one frame
// past the SBF limit of 4,096 bytes. `cargo build-sbf` only warns about that, and the
// program then overwrites its own stack at run time.
#[inline(never)]
fn verify_fields(proof: &Proof, public_inputs: &Fields) -> bool {{
    VERIFIER.verify(proof, public_inputs)
}}

#[inline(never)]
fn verify_fields_strict(proof: &Proof, public_inputs: &Fields) -> bool {{
    VERIFIER.verify_strict(proof, public_inputs)
}}

/// Host prover (the `prover` feature): generate proofs from this circuit's build
/// artifacts, for a server or local Rust app. The default build is the on-chain
/// verifier above and never pulls this in.
#[cfg(feature = "prover")]
pub mod prover {{
    use ::std::path::PathBuf;
    pub use ::xark_prover::ProveError;
    use ::xark_prover::{{circuit_at, try_fr_from_decimal, Fr, ProveInputs}};

    struct Raw(::std::vec::Vec<(::std::string::String, Fr)>);
    impl ProveInputs for Raw {{
        fn into_inputs(self) -> ::std::vec::Vec<(::std::string::String, Fr)> {{ self.0 }}
    }}

    /// A generated proof: the 256-byte Groth16 proof and its public inputs.
    pub struct Proof {{
        /// The 256-byte proof — what [`super::verify`] takes.
        pub bytes: [u8; 256],
        /// Public inputs as field elements ({n} * 32 bytes, little-endian).
        pub public_inputs: ::std::vec::Vec<u8>,
    }}

    impl Proof {{
        /// `proof || public_inputs`: the bytes a program carrying both receives.
        pub fn to_instruction_data(&self) -> ::std::vec::Vec<u8> {{
            let mut v = ::std::vec::Vec::with_capacity(256 + self.public_inputs.len());
            v.extend_from_slice(&self.bytes);
            v.extend_from_slice(&self.public_inputs);
            v
        }}
    }}

    /// Bound to this circuit's build directory (`target/xark/<circuit>/`: its
    /// `circuit.xbc` and the `pk.bin` from `xark setup`).
    pub struct Prover {{ dir: PathBuf }}

    impl Prover {{
        /// Bind to the circuit's build directory.
        pub fn new(build_dir: impl Into<PathBuf>) -> Self {{ Self {{ dir: build_dir.into() }} }}

        /// Prove from `(name, decimal field value)` pairs — every input, any order.
        /// A value that isn't a decimal is an error, not a panic.
        pub fn prove_fields<I, S>(&self, inputs: I) -> Result<Proof, ProveError>
        where
            I: IntoIterator<Item = (S, S)>,
            S: AsRef<str>,
        {{
            let fields = inputs
                .into_iter()
                .map(|(k, v)| {{
                    let (k, v) = (k.as_ref(), v.as_ref());
                    try_fr_from_decimal(v)
                        .map(|f| (k.to_string(), f))
                        .map_err(|e| ProveError(format!("input `{{k}}`: {{e}}")))
                }})
                .collect::<Result<::std::vec::Vec<_>, _>>()?;
            let proof = circuit_at(&self.dir).prove(Raw(fields))?;
            let bytes: [u8; 256] = proof
                .to_solana_proof()?
                .try_into()
                .expect("a Solana proof is 256 bytes");
            let public_inputs = proof.to_solana_public_inputs()?;
            Ok(Proof {{ bytes, public_inputs }})
        }}

        /// Prove from JSON `{{"name": "<decimal>"}}`: plain field values only. A struct or
        /// a natural value (a date, a string) needs the schema's encoding, which this
        /// crate doesn't have yet.
        pub fn prove_json(&self, json: &str) -> Result<Proof, ProveError> {{
            let map: ::std::collections::BTreeMap<::std::string::String, ::std::string::String> =
                ::serde_json::from_str(json).map_err(|e| ProveError(format!("reading the inputs: {{e}}")))?;
            self.prove_fields(map)
        }}
    }}
}}

{tests}"#
    )
}

fn gen_readme(name: &str, n: usize, sample: bool, trust: &super::SetupTrust) -> String {
    let setup = trust.tag;
    let mut summary = trust.summary.clone();
    summary[..1].make_ascii_uppercase();
    let ident = name.replace('-', "_");
    let sample = if sample {
        "`cargo test` in this crate verifies the bundled sample proof against the
embedded VK. `instruction_data.bin` is that proof as your program receives it
(`proof || public_inputs`): send those bytes as an instruction's data, in a
transaction built however your client builds them. "
    } else {
        "Export after `xark prove` to bundle a sample proof, which `cargo test` in this
crate then verifies against the embedded VK. "
    };
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

The proof comes in the instruction data (256 bytes: a client's `proof.toBytes()`).
The public inputs are what your program requires, from its own state (a policy, a
root, a nullifier): build a `PublicInputs`, the circuit's public inputs by name,
which packs them into field elements as the circuit's `#[input]` does:

```rust
let Some(proof) = instruction_data.first_chunk::<256>() else {{
    return Err(ProgramError::InvalidInstructionData);
}};
let proof = {ident}::Proof::from_le_bytes(proof);
let inputs = {ident}::PublicInputs {{ /* from your program's state */ }};
if !{ident}::verify(&proof, inputs) {{
    return Err(ProgramError::InvalidArgument);
}}
```

`verify` takes anything that converts into `{ident}::Fields`, the `[[u8; 32]; {n}]`
field elements in proof order: a `PublicInputs`, the elements themselves, or your
own struct with a `From` impl, packed with `{ident}::fields` (const fns, so inputs
known at compile time are constants).

A transaction that carries the public inputs too (`proof || public_inputs`, a
client's `proof.toInstructionData()`) splits them off after the proof's 256 bytes
into `Fields`, and `verify` checks both.

## Trusted setup

`{ident}::SETUP` is `{setup}`. {summary}. See xark's
[trusted setup](https://github.com/blueshift-gg/xark/blob/master/docs/trusted-setup.md)
guide for a setup that no single party has to be trusted for.

## Replay protection

A valid proof is not unique: anyone holding one can re-randomize it into a
different valid proof of the same public inputs (a property of Groth16;
`verify_strict` does not change it). So never use proof bytes, or their hash,
as a replay or "already used" key. Put replay protection in the public inputs
instead: a nullifier or nonce the circuit derives from a secret, or the signer
or context the proof is for, and record *that* on-chain.

{sample}A TypeScript client from `xark client` sends a proof in this format:
`proof.toBytes()`.
"#
    )
}

fn write_file(dir: &Path, name: &str, bytes: &[u8]) -> Result<bool> {
    write_str_bytes(&dir.join(name), bytes)
}

fn write_str(path: &Path, contents: &str) -> Result<bool> {
    write_str_bytes(path, contents.as_bytes())
}

/// Write `bytes` unless the file already holds them: an unchanged file keeps its
/// mtime, so cargo doesn't rebuild the crate and the program that depends on it.
/// Whether it wrote.
fn write_str_bytes(path: &Path, bytes: &[u8]) -> Result<bool> {
    if fs::read(path).is_ok_and(|b| b == bytes) {
        return Ok(false);
    }
    fs::write(path, bytes).with_context(|| format!("writing {}", path.display()))?;
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::{gen_cargo_toml, verifier_dep};

    #[test]
    fn generated_manifest_is_standalone_and_on_the_cli_version() {
        let manifest = gen_cargo_toml("example-client", false);
        assert!(!gen_cargo_toml("example-client", true).contains("[workspace]"));

        // Standalone so cargo doesn't fold it into a neighbouring workspace.
        assert!(manifest.contains("\n[workspace]\n"));
        // A crates.io version req on this CLI's version — never a git source,
        // never a local path.
        assert!(manifest.contains(&format!(
            r#"xark-verifier = "{}""#,
            env!("CARGO_PKG_VERSION")
        )));
    }

    #[test]
    fn verifier_dep_is_the_cli_version() {
        // The dep is a crates.io version req on this binary's own version, so the
        // generated crate resolves the matching verifier — no git, no user input.
        assert_eq!(
            verifier_dep(),
            format!(r#""{}""#, env!("CARGO_PKG_VERSION"))
        );
    }
}
