//! Public input extraction and ordering.

use ark_bn254::Fr;

use crate::artifact::{NoirArtifact, WitnessIndex};
use crate::error::BackendError;
use crate::witness::WitnessMap;

/// Pull public input values out of a witness map in the exact order declared by
/// the circuit. Returns a [`BackendError::MissingWitness`] for any public input
/// not present in the witness.
pub fn extract_public_inputs(
    artifact: &NoirArtifact,
    witness: &WitnessMap<Fr>,
) -> Result<Vec<Fr>, BackendError> {
    let mut out = Vec::with_capacity(artifact.public_inputs.len());
    for idx in &artifact.public_inputs {
        match witness.get(idx) {
            Some(v) => out.push(*v),
            None => return Err(BackendError::missing_witness(*idx)),
        }
    }
    Ok(out)
}

/// The ordered public input indices for an artifact.
pub fn public_input_indices(artifact: &NoirArtifact) -> &[WitnessIndex] {
    &artifact.public_inputs
}
