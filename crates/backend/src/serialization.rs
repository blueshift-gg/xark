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

/// The largest verifying key, proof or public-input file read: room for two million
/// public inputs (32 bytes each, and a verifying key's point per input), far more
/// than any circuit has. A larger file isn't one of these, and reading it whole
/// could exhaust memory.
pub const MAX_ARTIFACT_BYTES: u64 = 64 << 20;

/// Decode a verifying key, proof or public inputs straight from the file: one over
/// [`MAX_ARTIFACT_BYTES`] is refused before it's read, and one of the wrong kind
/// fails at its first bad bytes. (A sequence's declared length doesn't pre-allocate:
/// arkworks collects it element by element.)
pub fn canonical_read_from_file<T: CanonicalDeserialize>(path: &Path) -> std::io::Result<T> {
    let file = fs::File::open(path)?;
    let len = file.metadata()?.len();
    if len > MAX_ARTIFACT_BYTES {
        return Err(std::io::Error::other(format!(
            "{len} bytes, more than a verifying key, proof or public inputs can be \
             ({MAX_ARTIFACT_BYTES} at most)"
        )));
    }
    let file = std::io::BufReader::new(file);
    T::deserialize_with_mode(file, Compress::Yes, Validate::Yes)
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
