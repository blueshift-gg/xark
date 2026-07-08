//! `xark idl` — emit the circuit's interface descriptor (`<name>.idl.json` plus
//! a typed `<name>.idl.ts`): the ZK analog of an Anchor IDL, and the file the
//! `xark-client` library consumes.
//!
//! It carries the input names + visibility, the *ordered* public signals (the
//! order the proof commits to), the field/curve/protocol, a stable circuit hash,
//! the Solana wire layout, and — once `xark setup` has run — the verifying key
//! (snarkjs form + Solana little-endian bytes).
//!
//! There are no per-input types: by `r1cs.json` every input is a field element,
//! so the interface is exactly the (name, visibility, order) plus the key.

use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use clap::Args;
use serde_json::json;

use xark_backend::keys::Groth16Keys;
use xark_backend::serialization::vk_to_snarkjs;
use xark_backend::solana::assemble_vk_bytes_le;
use xark_ir::Visibility;

use super::{circuit_hash, load_r1cs};
use crate::xark_project::XarkProject;

/// A single declared circuit input.
pub struct IdlInput {
    pub name: String,
    /// `"public"` (known to the verifier) or `"private"` (prover's secret).
    pub visibility: &'static str,
}

/// The packed `proof ‖ public_inputs` calldata layout a Groth16 verifier
/// consumes (chain-agnostic; the on-chain verifier from `xark export` is one
/// consumer).
pub struct Calldata {
    pub endianness: &'static str,
    pub proof_bytes: usize,
    pub public_input_bytes: usize,
    pub total_bytes: usize,
    /// Human description of the byte layout.
    pub layout: &'static str,
}

/// The verifying key, embedded once `xark setup` has produced one.
pub struct VerifyingKeyIdl {
    /// Whether the key came from a production trusted setup (see `xark setup`).
    pub production_safe: bool,
    /// snarkjs `verification_key.json` shape — feed straight to `groth16.verify`.
    pub snarkjs: serde_json::Value,
    /// The Solana on-chain VK blob (little-endian), hex-encoded (`0x…`).
    pub solana_le_hex: String,
}

/// The circuit interface descriptor written to `<name>.idl.json`.
///
/// Serialized via [`Idl::to_json`] (built with `serde_json::json!`) rather than
/// `#[derive(Serialize)]`: the CLI/compiler crate is a `rustc_driver` and takes
/// no direct `serde` dependency, so a derive would bind to the sysroot's `serde`
/// and clash with `serde_json`'s. This matches `inspect`'s JSON handling.
pub struct Idl {
    pub xark_idl_version: &'static str,
    pub name: String,
    pub circuit_hash: String,
    pub field: String,
    pub curve: &'static str,
    pub protocol: &'static str,
    pub inputs: Vec<IdlInput>,
    /// Public inputs in the order the proof commits to them (variable-id order).
    /// A verifier MUST supply public signals in exactly this order.
    pub public_signals: Vec<String>,
    pub num_public_inputs: usize,
    pub num_private_inputs: usize,
    pub num_constraints: usize,
    pub calldata: Calldata,
    pub verifying_key: Option<VerifyingKeyIdl>,
}

impl Idl {
    /// Render the IDL as JSON (the on-disk `<name>.idl.json` shape).
    pub fn to_json(&self) -> serde_json::Value {
        let inputs: Vec<serde_json::Value> = self
            .inputs
            .iter()
            .map(|i| json!({ "name": i.name, "visibility": i.visibility }))
            .collect();
        let mut obj = json!({
            "xark_idl_version": self.xark_idl_version,
            "name": self.name,
            "circuit_hash": self.circuit_hash,
            "field": self.field,
            "curve": self.curve,
            "protocol": self.protocol,
            "inputs": inputs,
            "public_signals": self.public_signals,
            "num_public_inputs": self.num_public_inputs,
            "num_private_inputs": self.num_private_inputs,
            "num_constraints": self.num_constraints,
            "calldata": {
                "endianness": self.calldata.endianness,
                "proof_bytes": self.calldata.proof_bytes,
                "public_input_bytes": self.calldata.public_input_bytes,
                "total_bytes": self.calldata.total_bytes,
                "layout": self.calldata.layout,
            },
        });
        if let Some(vk) = &self.verifying_key {
            obj["verifying_key"] = json!({
                "production_safe": vk.production_safe,
                "snarkjs": vk.snarkjs,
                "solana_le_hex": vk.solana_le_hex,
            });
        }
        obj
    }

    /// Render the IDL as a typed TypeScript module: an `as const` constant plus
    /// an exported `typeof` type. Passing this to `xark-client`'s `XarkClient`
    /// gives compile-time knowledge of the circuit's public-signal names/order.
    pub fn to_typescript(&self) -> String {
        let json = serde_json::to_string_pretty(&self.to_json()).unwrap_or_else(|_| "{}".into());
        let const_name = ts_const_name(&self.name);
        let type_name = ts_type_name(&self.name);
        format!(
            "// Auto-generated by `xark` — the circuit's IDL as a typed constant.\n\
             // Use with the `xark-client` library:\n\
             //   import {{ XarkClient }} from \"xark-client\";\n\
             //   import {{ {const_name} }} from \"./{name}.idl\";\n\
             //   const client = new XarkClient({const_name});\n\
             export const {const_name} = {json} as const;\n\n\
             export type {type_name} = typeof {const_name};\n",
            name = self.name,
        )
    }

    /// The TS constant the typed IDL exports (`cube` → `cubeIdl`) — so `xark
    /// client` can `import { cubeIdl } from "./cube.idl"` in the starter.
    pub fn ts_const(&self) -> String {
        ts_const_name(&self.name)
    }
}

/// `cube` → `cubeIdl`, `my-circuit` → `myCircuitIdl` (a valid TS identifier).
fn ts_const_name(name: &str) -> String {
    format!("{}Idl", camel_ident(name))
}

/// `cube` → `CubeIdl`, `my-circuit` → `MyCircuitIdl`.
fn ts_type_name(name: &str) -> String {
    let camel = camel_ident(name);
    let mut chars = camel.chars();
    match chars.next() {
        Some(first) => format!("{}{}Idl", first.to_ascii_uppercase(), chars.as_str()),
        None => "CircuitIdl".to_string(),
    }
}

/// Lower-camelCase a circuit name into a safe TS identifier: keep alphanumerics,
/// capitalize the letter after any run of separators, and never start with a
/// digit. Falls back to `circuit`.
fn camel_ident(name: &str) -> String {
    let mut out = String::new();
    let mut capitalize = false;
    for c in name.chars() {
        if c.is_ascii_alphanumeric() {
            if out.is_empty() && c.is_ascii_digit() {
                out.push('_');
                out.push(c);
            } else if capitalize {
                out.push(c.to_ascii_uppercase());
                capitalize = false;
            } else {
                out.push(c);
            }
        } else {
            capitalize = !out.is_empty();
        }
    }
    if out.is_empty() {
        "circuit".to_string()
    } else {
        out
    }
}

/// Build the IDL for a resolved project by reading `r1cs.json` (and, when
/// present, `vk.bin` + `metadata.json`). Never fails on a missing key — the VK
/// section is simply omitted until `xark setup` has run.
pub fn build_idl(project: &XarkProject) -> Result<Idl> {
    let r1cs_path = project.r1cs_json();
    let r1cs_str = fs::read_to_string(&r1cs_path)
        .with_context(|| format!("reading {} (run `xark build` first?)", r1cs_path.display()))?;
    let prog = load_r1cs(&r1cs_path)?;

    // Inputs in declaration (variable-id) order; internal wires are not inputs.
    let mut vars: Vec<_> = prog
        .variables
        .iter()
        .filter(|v| v.visibility != Visibility::Internal)
        .collect();
    vars.sort_by_key(|v| v.id);

    let inputs: Vec<IdlInput> = vars
        .iter()
        .map(|v| IdlInput {
            name: v.name.clone(),
            visibility: match v.visibility {
                Visibility::Public => "public",
                _ => "private",
            },
        })
        .collect();

    let public_signals: Vec<String> = vars
        .iter()
        .filter(|v| v.visibility == Visibility::Public)
        .map(|v| v.name.clone())
        .collect();
    let num_public_inputs = public_signals.len();
    let num_private_inputs = inputs.len() - num_public_inputs;

    // VK section: present only once a key exists beside the artifacts.
    let verifying_key = build_vk_section(project, num_public_inputs);

    Ok(Idl {
        xark_idl_version: "1",
        name: project.entry_name(),
        circuit_hash: format!("sha256:{}", circuit_hash(&r1cs_str)),
        field: prog.field.name.clone(),
        curve: "bn128",
        protocol: "groth16",
        inputs,
        public_signals,
        num_public_inputs,
        num_private_inputs,
        num_constraints: prog.constraints.len(),
        calldata: Calldata {
            endianness: "little",
            proof_bytes: 256,
            public_input_bytes: 32,
            total_bytes: 256 + 32 * num_public_inputs,
            layout: "proof (256 B) || public_inputs (N * 32 B)",
        },
        verifying_key,
    })
}

/// Read `vk.bin` (+ `metadata.json` for the production flag) if present and
/// render the embeddable VK section. Returns `None` when there is no key yet.
fn build_vk_section(project: &XarkProject, num_public: usize) -> Option<VerifyingKeyIdl> {
    let vk = Groth16Keys::read_verifying_key(&project.verifying_key()).ok()?;
    let production_safe = fs::read_to_string(project.metadata())
        .ok()
        .and_then(|s| serde_json::from_str::<serde_json::Value>(&s).ok())
        .and_then(|v| v.get("production_safe").and_then(|b| b.as_bool()))
        .unwrap_or(false);
    Some(VerifyingKeyIdl {
        production_safe,
        snarkjs: vk_to_snarkjs(&vk, num_public),
        solana_le_hex: format!("0x{}", hex::encode(assemble_vk_bytes_le(&vk))),
    })
}

/// Build and write both `<name>.idl.json` and the typed `<name>.idl.ts`,
/// returning the JSON path. Reused by `xark idl` and by `xark setup` (which
/// refreshes the IDL once the verifying key exists).
pub fn write_idl(project: &XarkProject) -> Result<PathBuf> {
    let idl = build_idl(project)?;
    let json_path = project.idl_json();
    write_str(
        &json_path,
        &format!("{}\n", serde_json::to_string_pretty(&idl.to_json())?),
    )?;
    write_str(&project.idl_ts(), &idl.to_typescript())?;
    Ok(json_path)
}

fn write_str(path: &Path, contents: &str) -> Result<()> {
    fs::write(path, contents).with_context(|| format!("writing {}", path.display()))?;
    Ok(())
}

/// The `<name>.idl.ts` path sitting beside a `<name>.idl.json` path.
fn ts_sibling(json_path: &Path) -> PathBuf {
    let s = json_path.to_string_lossy();
    if let Some(stem) = s.strip_suffix(".idl.json") {
        PathBuf::from(format!("{stem}.idl.ts"))
    } else if let Some(stem) = s.strip_suffix(".json") {
        PathBuf::from(format!("{stem}.ts"))
    } else {
        json_path.with_extension("idl.ts")
    }
}

#[derive(Args, Debug)]
pub struct IdlArgs {
    /// Circuit crate directory (or its `target/xark/` output dir). Defaults to
    /// the current directory; paths are inferred from `target/xark/`.
    #[arg(value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,

    /// Write the IDL here instead of `target/xark/<name>/<name>.idl.json`.
    #[arg(long, value_hint = clap::ValueHint::FilePath)]
    pub out: Option<PathBuf>,
}

pub fn run(args: IdlArgs) -> Result<()> {
    let project = XarkProject::resolve(args.path.clone())?;
    let idl = build_idl(&project)?;
    let json_path = args.out.clone().unwrap_or_else(|| project.idl_json());
    let ts_path = ts_sibling(&json_path);
    write_str(
        &json_path,
        &format!("{}\n", serde_json::to_string_pretty(&idl.to_json())?),
    )?;
    write_str(&ts_path, &idl.to_typescript())?;

    let has_vk = idl.verifying_key.is_some();
    println!("Wrote {}", json_path.display());
    println!(
        "Wrote {}  {}",
        ts_path.display(),
        crate::style::dim("# typed IDL for the xark-client library")
    );
    println!(
        "{}",
        crate::style::brand(&format!(
            "✅ Circuit IDL for `{}` — {} input(s), {} public signal(s){}.",
            idl.name,
            idl.inputs.len(),
            idl.num_public_inputs,
            if has_vk {
                ", verifying key embedded"
            } else {
                " (run `xark setup` to embed the verifying key)"
            }
        ))
    );

    let p = super::path_arg(&args.path);
    let mut steps: Vec<(String, &str)> = Vec::new();
    if !has_vk {
        steps.push((
            format!("xark setup {p}"),
            "generate keys, then re-run to embed the VK",
        ));
    }
    steps.push((
        format!("xark client {p}"),
        "scaffold a TypeScript client (uses the xark-client library)",
    ));
    steps.push((
        format!("xark export {p}"),
        "generate the on-chain Solana verifier crate",
    ));
    println!("\n{}", crate::style::next_steps(&steps));
    Ok(())
}
