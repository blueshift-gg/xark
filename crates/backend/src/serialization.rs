//! Arkworks canonical (binary) serialization helpers.

use std::fs;
use std::path::Path;

use ark_bn254::Fr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};

pub fn canonical_write_to_file<T: CanonicalSerialize>(
    value: &T,
    path: &Path,
) -> std::io::Result<()> {
    let mut buf = Vec::with_capacity(value.serialized_size(Compress::Yes));
    value
        .serialize_with_mode(&mut buf, Compress::Yes)
        .map_err(|e| std::io::Error::other(e.to_string()))?;
    fs::write(path, buf)
}

pub fn canonical_read_from_file<T: CanonicalDeserialize>(path: &Path) -> std::io::Result<T> {
    let bytes = fs::read(path)?;
    T::deserialize_with_mode(bytes.as_slice(), Compress::Yes, Validate::Yes)
        .map_err(|e| std::io::Error::other(e.to_string()))
}

// -- Public input binary ------------------------------------------------------

/// Read public inputs from canonical binary.
pub fn read_public_inputs(path: &Path) -> std::io::Result<Vec<Fr>> {
    canonical_read_from_file(path)
}

/// Write public inputs as canonical binary.
pub fn write_public_inputs(inputs: &[Fr], path: &Path) -> std::io::Result<()> {
    canonical_write_to_file(&inputs.to_vec(), path)
}
