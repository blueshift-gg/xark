//! ACIR-to-R1CS lowering for the xark Noir backend.
//!
//! This crate owns:
//! * Reading Noir [`ProgramArtifact`](artifact::ProgramArtifact) JSON files.
//! * Reading [`WitnessStack`](witness::WitnessStack) files.
//! * Converting Noir field elements into `ark_bn254::Fr`.
//! * Lowering supported ACIR opcodes into Arkworks R1CS constraints.
//! * Reporting opcode coverage and rejecting unsupported opcodes explicitly.
//!
//! It deliberately does **not** depend on `ark-groth16` or perform any proving.

pub mod artifact;
pub mod error;
pub mod field;
pub mod lower;
pub mod opcodes;
pub mod public_inputs;
pub mod r1cs_builder;
pub mod witness;

pub mod gadgets;

pub use artifact::{ArtifactMetadata, NoirArtifact, WitnessIndex};
pub use error::BackendError;
pub use lower::{LoweredAcirCircuit, lower_program};
pub use witness::WitnessMap;

/// Backend lowering semantics version, baked into the circuit hash so that any
/// change to the lowering layer changes the resulting circuit identity.
pub const LOWERING_VERSION: u32 = 1;

/// Stable identifier for the proving system the lowered circuit is intended for.
pub const PROVING_SYSTEM: &str = "groth16";

/// Stable identifier for the curve all field elements live on.
pub const CURVE: &str = "bn254";
