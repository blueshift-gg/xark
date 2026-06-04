//! Noir artifact parsing.
//!
//! We deliberately do **not** pull in `noirc_artifacts` (which transitively
//! depends on the whole Noir compiler tree). The artifact is a small JSON
//! envelope around a base64-encoded `Program<FieldElement>` bytecode blob, and
//! we already have `acir::circuit::Program::deserialize_program` available via
//! the `acir` crate. So we parse the JSON ourselves, extract the bytecode, and
//! hand it to `acir`.

use std::path::Path;

use acir::circuit::{Circuit, Opcode, Program};
use acir::FieldElement;
use base64::engine::general_purpose::STANDARD as B64;
use base64::Engine as _;
use serde::{Deserialize, Serialize};

use crate::error::BackendError;

/// Noir 1.0.0-beta.21 — the only supported Noir release for now.
pub const SUPPORTED_NOIR_VERSION_PREFIX: &str = "1.0.0-beta.21";

/// Newtype around `u32` to keep ACIR witness indices distinct from R1CS
/// variable indices throughout the lowering layer.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WitnessIndex(pub u32);

impl WitnessIndex {
    pub fn from_witness(w: acir::native_types::Witness) -> Self {
        WitnessIndex(w.0)
    }
}

impl std::fmt::Display for WitnessIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "w{}", self.0)
    }
}

/// Backend-relevant metadata extracted from a Noir artifact.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArtifactMetadata {
    pub noir_version: String,
    pub program_hash: String,
}

/// Normalized representation of a single-function Noir artifact ready for
/// lowering.
#[derive(Clone, Debug)]
pub struct NoirArtifact {
    pub circuit_name: String,
    pub program: Program<FieldElement>,
    /// Ordered list of public input witness indices, exactly as declared in the
    /// circuit (parameters first, then return values).
    pub public_inputs: Vec<WitnessIndex>,
    pub witness_count: usize,
    pub metadata: ArtifactMetadata,
}

impl NoirArtifact {
    /// The ACIR function we lower. For multi-function programs (Noir-emitted
    /// helpers that survive inlining) we only lower `functions[0]`; any
    /// `Opcode::Call` in `main` is rejected by the lowering layer's
    /// unsupported-opcode path. See ROADMAP step B.4.
    pub fn main_circuit(&self) -> &Circuit<FieldElement> {
        &self.program.functions[0]
    }

    pub fn opcodes(&self) -> &[Opcode<FieldElement>] {
        &self.main_circuit().opcodes
    }

    /// Number of helper functions (i.e. `functions[1..]`). These are not
    /// lowered; they exist in the artifact because Noir's inliner decided
    /// to keep them as separate ACIR functions. They are only reachable
    /// via `Opcode::Call`, which the lowering layer rejects.
    pub fn num_helper_functions(&self) -> usize {
        self.program.functions.len().saturating_sub(1)
    }

    /// Names of helper functions in the order Noir emitted them. Empty
    /// vector for ordinary single-function programs.
    pub fn helper_function_names(&self) -> Vec<String> {
        self.program
            .functions
            .iter()
            .skip(1)
            .map(|c| c.function_name.clone())
            .collect()
    }
}

#[derive(Deserialize)]
struct RawArtifact {
    noir_version: String,
    #[serde(default)]
    hash: serde_json::Value,
    bytecode: String,
}

/// Parse a `target/<name>.json` artifact file.
pub fn parse_artifact_file(path: &Path) -> Result<NoirArtifact, BackendError> {
    let bytes = std::fs::read(path)?;
    let circuit_name = path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("circuit")
        .to_string();
    parse_artifact_bytes(&bytes, circuit_name)
}

/// Parse raw artifact JSON bytes. `circuit_name` is what we report to the user
/// (typically the file stem of the artifact).
pub fn parse_artifact_bytes(
    bytes: &[u8],
    circuit_name: String,
) -> Result<NoirArtifact, BackendError> {
    let raw: RawArtifact = serde_json::from_slice(bytes)
        .map_err(|e| BackendError::ArtifactParse(format!("invalid artifact JSON: {e}")))?;

    if !raw.noir_version.starts_with(SUPPORTED_NOIR_VERSION_PREFIX) {
        return Err(BackendError::ArtifactVersionUnsupported {
            supported: format!("{SUPPORTED_NOIR_VERSION_PREFIX}.*"),
            found: raw.noir_version,
        });
    }

    let bytecode = B64
        .decode(raw.bytecode.as_bytes())
        .map_err(|e| BackendError::ArtifactParse(format!("bytecode base64 decode: {e}")))?;

    let program: Program<FieldElement> = Program::deserialize_program(&bytecode).map_err(|e| {
        BackendError::ArtifactParse(format!("ACIR bytecode deserialization failed: {e}"))
    })?;

    // ROADMAP B.4: accept multi-function programs. We only synthesize
    // `functions[0]` (the `main` entry point). Helpers exist in the artifact
    // because Noir's inliner left them as separate ACIR functions; if `main`
    // never invokes them via `Opcode::Call`, they are dead from our point
    // of view. If `main` does use `Opcode::Call`, the lowering layer
    // rejects it via `OpcodeClass::Call` -> unsupported.
    //
    // A program with *zero* functions is pathological — reject explicitly
    // so downstream indexing of `program.functions[0]` is sound.
    if program.functions.is_empty() {
        return Err(BackendError::MultiFunctionProgram {
            functions: program.functions.len(),
        });
    }

    let main = &program.functions[0];

    // Public inputs ordered: external public parameters first, then return values.
    // BTreeSet iteration order is by Witness index, which matches Noir's own
    // public-input ordering on the verifier side.
    let mut public_inputs: Vec<WitnessIndex> = main
        .public_parameters
        .0
        .iter()
        .copied()
        .map(WitnessIndex::from_witness)
        .collect();
    for w in main.return_values.0.iter() {
        let idx = WitnessIndex::from_witness(*w);
        if !public_inputs.contains(&idx) {
            public_inputs.push(idx);
        }
    }

    // The wire format does not directly expose `current_witness_index`, but we
    // can derive an upper bound from the opcodes and public/private parameter
    // sets. That's sufficient for inspection and for sizing R1CS allocations.
    let witness_count = compute_witness_count(main);

    let hash = match &raw.hash {
        serde_json::Value::String(s) => s.clone(),
        serde_json::Value::Number(n) => n.to_string(),
        other => other.to_string(),
    };

    Ok(NoirArtifact {
        circuit_name,
        program,
        public_inputs,
        witness_count,
        metadata: ArtifactMetadata {
            noir_version: raw.noir_version,
            program_hash: hash,
        },
    })
}

fn compute_witness_count(circuit: &Circuit<FieldElement>) -> usize {
    let mut max: u32 = 0;
    for w in circuit
        .public_parameters
        .0
        .iter()
        .chain(circuit.return_values.0.iter())
    {
        max = max.max(w.0);
    }
    for w in circuit.private_parameters.iter() {
        max = max.max(w.0);
    }
    for op in &circuit.opcodes {
        if let Opcode::AssertZero(expr) = op {
            for (_, l, r) in &expr.mul_terms {
                max = max.max(l.0).max(r.0);
            }
            for (_, w) in &expr.linear_combinations {
                max = max.max(w.0);
            }
        }
    }
    (max as usize) + 1
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn workspace_fixture(name: &str) -> PathBuf {
        // crates/acir-r1cs/src/artifact.rs -> .../src -> .../acir-r1cs -> .../crates -> workspace root
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        manifest
            .parent()
            .and_then(|p| p.parent())
            .expect("workspace root")
            .join("tests")
            .join("fixtures")
            .join(name)
    }

    #[test]
    fn single_function_artifact_reports_zero_helpers() {
        let artifact = parse_artifact_file(&workspace_fixture("arithmetic_square.json"))
            .expect("arithmetic_square parses");
        assert_eq!(artifact.num_helper_functions(), 0);
        assert!(artifact.helper_function_names().is_empty());
    }

    /// ROADMAP B.4 acceptance: multi-function artifacts must now parse
    /// cleanly (the pre-B.4 code returned `MultiFunctionProgram` here).
    #[test]
    fn multi_function_artifact_parses_and_reports_helpers() {
        let artifact = parse_artifact_file(&workspace_fixture("multi_function.json"))
            .expect("multi_function parses after B.4");
        assert!(
            artifact.num_helper_functions() >= 1,
            "expected helpers, got: {}",
            artifact.num_helper_functions()
        );
        let names = artifact.helper_function_names();
        assert_eq!(names.len(), artifact.num_helper_functions());
        assert!(
            names.iter().any(|n| n == "square"),
            "expected 'square' helper, got: {names:?}"
        );
        // Main is still functions[0]; we only lower its opcodes.
        assert_eq!(artifact.main_circuit().function_name, "main");
    }
}
