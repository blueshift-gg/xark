//! Proving and verifying key bundles.

use ark_bn254::{Bn254, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_groth16::{ProvingKey, VerifyingKey};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::path::Path;

use crate::serialization::{canonical_read_from_file, canonical_write_to_file};

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

    /// Load the proving key with **parallel** point deserialization. arkworks'
    /// `deserialize_with_mode` decompresses + subgroup-checks every point
    /// *sequentially*, and for a large key that (a per-point modular sqrt +
    /// scalar-mul) dominated `xark prove`. A Groth16 proving key is mostly five
    /// `Vec`s of independent points, so we parse the struct layout and fan the
    /// per-point decompress+validate across cores — keeping the key compressed
    /// (small on disk) and fully validated, just fast.
    pub fn read_proving_key(path: &Path) -> std::io::Result<ProvingKey<Bn254>> {
        let bytes = std::fs::read(path)?;
        read_proving_key_parallel(&bytes).map_err(|e| std::io::Error::other(e.to_string()))
    }

    pub fn read_verifying_key(path: &Path) -> std::io::Result<VerifyingKey<Bn254>> {
        canonical_read_from_file::<VerifyingKey<Bn254>>(path)
    }
}

/// Parse the `CanonicalSerialize` layout of `ProvingKey<Bn254>` — `vk`,
/// `beta_g1`, `delta_g1`, then the five point vectors (field order matches
/// ark-groth16's `ProvingKey`) — deserializing each vector's points in parallel.
/// Compressed + validated, just fanned across cores.
fn read_proving_key_parallel(
    bytes: &[u8],
) -> Result<ProvingKey<Bn254>, ark_serialize::SerializationError> {
    let (c, v) = (Compress::Yes, Validate::Yes);
    let mut cur: &[u8] = bytes;
    // The header (verifying key + two points) is small — deserialize sequentially.
    let vk = VerifyingKey::<Bn254>::deserialize_with_mode(&mut cur, c, v)?;
    let beta_g1 = G1Affine::deserialize_with_mode(&mut cur, c, v)?;
    let delta_g1 = G1Affine::deserialize_with_mode(&mut cur, c, v)?;
    // The bulk: five point vectors, each read in parallel.
    let a_query = read_point_vec_par::<G1Affine>(&mut cur, c, v)?;
    let b_g1_query = read_point_vec_par::<G1Affine>(&mut cur, c, v)?;
    let b_g2_query = read_point_vec_par::<G2Affine>(&mut cur, c, v)?;
    let h_query = read_point_vec_par::<G1Affine>(&mut cur, c, v)?;
    let l_query = read_point_vec_par::<G1Affine>(&mut cur, c, v)?;
    Ok(ProvingKey {
        vk,
        beta_g1,
        delta_g1,
        a_query,
        b_g1_query,
        b_g2_query,
        h_query,
        l_query,
    })
}

/// Read a `Vec<G>` in the arkworks layout — a `u64` length then `len`
/// fixed-size points — deserializing (decompress + subgroup-check) the points
/// across rayon's thread pool.
fn read_point_vec_par<G>(
    cur: &mut &[u8],
    compress: Compress,
    validate: Validate,
) -> Result<Vec<G>, ark_serialize::SerializationError>
where
    G: AffineRepr + CanonicalDeserialize + CanonicalSerialize + Send,
{
    // A `Vec`'s length is serialized as a `u64` (independent of point mode).
    let len = u64::deserialize_with_mode(&mut *cur, compress, validate)? as usize;
    let sz = G::generator().serialized_size(compress);
    let total = len
        .checked_mul(sz)
        .ok_or(ark_serialize::SerializationError::InvalidData)?;
    if cur.len() < total {
        return Err(ark_serialize::SerializationError::NotEnoughSpace);
    }
    let (chunk, rest) = cur.split_at(total);
    *cur = rest;
    chunk
        .par_chunks(sz)
        .map(|bytes| G::deserialize_with_mode(bytes, compress, validate))
        .collect()
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
    pub fn new_dev(circuit_hash: String, num_public_inputs: usize, num_constraints: usize) -> Self {
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
