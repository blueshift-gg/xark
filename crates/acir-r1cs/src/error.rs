//! Error types surfaced from artifact parsing, witness loading, opcode
//! classification, and constraint synthesis. Every variant is rendered
//! verbatim to the user via the CLI, so the message text is part of the
//! supported interface — keep it self-explanatory and stable.

use thiserror::Error;

use crate::artifact::WitnessIndex;

/// Errors produced by the xark backend.
///
/// All variants are surfaced verbatim to the CLI so that users see the same
/// error text the library would emit in tests.
#[derive(Debug, Error)]
pub enum BackendError {
    #[error("Unsupported ACIR opcode at index {index}: {opcode}\n\n{help}")]
    UnsupportedOpcode {
        opcode: String,
        index: usize,
        help: String,
    },

    #[error(
        "Missing witness value: witness {witness}\n\n\
         The circuit references witness {witness}, but it was not present in the witness file.\n\
         Regenerate the witness with `nargo execute`."
    )]
    MissingWitness { witness: u32 },

    #[error("Constraint not satisfied: {detail}")]
    ConstraintUnsatisfied { detail: String },

    #[error(
        "Unsupported Noir/ACIR artifact version.\n\n\
         Supported:\n  Noir: {supported}\nFound:\n  {found}\n\n\
         Pin nargo to the supported version or update acir-r1cs parsing."
    )]
    ArtifactVersionUnsupported { found: String, supported: String },

    #[error("Failed to parse Noir artifact: {0}")]
    ArtifactParse(String),

    #[error("Failed to parse witness file: {0}")]
    WitnessParse(String),

    #[error("Field decoding error: {0}")]
    FieldDecode(String),

    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error(
        "Malformed ACIR program: expected at least 1 function (the entry point), got {functions}"
    )]
    MultiFunctionProgram { functions: usize },
}

impl BackendError {
    pub fn missing_witness(idx: WitnessIndex) -> Self {
        BackendError::MissingWitness { witness: idx.0 }
    }
}
