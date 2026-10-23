//! Proof bundle (proof + public inputs) helpers.

use std::path::Path;

use ark_bn254::{Bn254, Fr};
use xark_groth16::Proof;

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

    /// A proof file in either form: compressed (128 bytes, as `xark prove` writes
    /// it) or on-chain (256 bytes, as an exported Solana verifier and a client's
    /// `proof.toBytes()` have it).
    pub fn read_proof(path: &Path) -> std::io::Result<Proof<Bn254>> {
        if std::fs::metadata(path)?.len() == xark_groth16::solana::PROOF_BYTES as u64 {
            let bytes = std::fs::read(path)?;
            return xark_groth16::solana::decode_proof_le(&bytes)
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e));
        }
        canonical_read_from_file::<Proof<Bn254>>(path)
    }
}
