//! Proving and verifying key bundles.

use ark_bn254::Bn254;
use ark_groth16::{ProvingKey, VerifyingKey};
use serde::{Deserialize, Serialize};
use std::path::Path;

use crate::serialization::canonical_read_from_file;
use crate::serialization::canonical_write_to_file;

/// Bundle of Arkworks Groth16 keys for BN254.
pub struct Groth16Keys {
    pub proving_key: ProvingKey<Bn254>,
    pub verifying_key: VerifyingKey<Bn254>,
}

impl Groth16Keys {
    pub fn write_proving_key(&self, path: &Path) -> std::io::Result<()> {
        canonical_write_to_file(&self.proving_key, path)
    }

    pub fn write_verifying_key(&self, path: &Path) -> std::io::Result<()> {
        canonical_write_to_file(&self.verifying_key, path)
    }

    pub fn read_proving_key(path: &Path) -> std::io::Result<ProvingKey<Bn254>> {
        canonical_read_from_file::<ProvingKey<Bn254>>(path)
    }

    pub fn read_verifying_key(path: &Path) -> std::io::Result<VerifyingKey<Bn254>> {
        canonical_read_from_file::<VerifyingKey<Bn254>>(path)
    }
}

/// Metadata written alongside the keys so the user (and later, audits) can
/// trace which circuit and backend the keys came from.
///
/// Advisory sidecar, not bound to the key bytes: the `export`/`prove` guards
/// catch honest misconfiguration, not a forged sidecar.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KeyMetadata {
    pub protocol: String,
    pub curve: String,
    pub setup_mode: String,
    pub production_safe: bool,
    pub circuit_hash: String,
    pub backend_version: String,
    pub created_at: String,
    pub num_public_inputs: usize,
    pub num_constraints: usize,
    /// The fixed `ChaCha20Rng` seed used to drive Groth16 setup when the
    /// caller explicitly requested reproducible artifacts. `None` indicates
    /// the OS RNG was used. Populated on the `--insecure-dev-mode
    /// --deterministic-rng <seed>` path; absent otherwise. Production
    /// (ceremony-based) setup never sets this field.
    #[serde(default)]
    pub deterministic_rng_seed: Option<u64>,
    /// Filename (or short identifier) of the Powers-of-Tau transcript these
    /// keys were derived from. `None` for dev-mode keys. Populated by the
    /// ptau-driven setup path. Forward-compat: dev-mode metadata
    /// today writes `null` here, so adding this field doesn't break older
    /// readers that ignore unknown fields.
    #[serde(default)]
    pub ptau_source: Option<String>,
    /// SHA-256 (hex) of the phase-2 randomness seed used to derive the
    /// circuit-specific γ, δ. **NOT** the seed itself — the seed must be
    /// discarded immediately after setup, per the soundness argument in
    /// the Groth16 paper. `None` for dev-mode keys.
    #[serde(default)]
    pub phase2_seed_hash: Option<String>,
}

impl KeyMetadata {
    pub fn new_dev(
        circuit_hash: String,
        num_public_inputs: usize,
        num_constraints: usize,
    ) -> Self {
        Self {
            protocol: "groth16".into(),
            curve: "bn254".into(),
            setup_mode: "insecure-dev-mode".into(),
            production_safe: false,
            circuit_hash,
            backend_version: env!("CARGO_PKG_VERSION").into(),
            created_at: chrono::Utc::now().to_rfc3339(),
            num_public_inputs,
            num_constraints,
            deterministic_rng_seed: None,
            ptau_source: None,
            phase2_seed_hash: None,
        }
    }
}
