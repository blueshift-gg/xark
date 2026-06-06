//! Proof bundle (proof + public inputs) helpers.

use std::path::Path;

use ark_bn254::{Bn254, Fr};
use ark_groth16::Proof;

use crate::serialization::{canonical_read_from_file, canonical_write_to_file};

/// A proof together with the ordered public inputs that produced it.
pub struct ProofBundle {
    pub proof: Proof<Bn254>,
    pub public_inputs: Vec<Fr>,
}

impl ProofBundle {
    pub fn write_proof(&self, path: &Path) -> std::io::Result<()> {
        canonical_write_to_file(&self.proof, path)
    }

    pub fn read_proof(path: &Path) -> std::io::Result<Proof<Bn254>> {
        canonical_read_from_file::<Proof<Bn254>>(path)
    }
}
