//! Re-encode a proving key with **uncompressed** points, from a stream.
//!
//! A compressed key is half the size on the wire and on disk, but every point
//! must be decompressed (a field square root) each time it is read — in WASM that
//! is ~95% of the witness MSMs. Transcoding once, then proving from the
//! uncompressed key, pays that cost once per device instead of once per proof.
//! The output is a standard `pk.bin` (`XKPK` header, uncompressed mode) every
//! reader accepts. Decompression runs in parallel locally, or on an
//! [`Accelerator`] (e.g. a WASM worker pool).

use ark_bn254::{G1Affine, G2Affine};
use ark_serialize::{CanonicalSerialize, Compress};
use rayon::prelude::*;

use crate::accel::Accelerator;
use crate::keystream::{KeyEvent, KeyStream, KeyStreamError};
use crate::pk::KeyVector;

/// Push compressed (or already uncompressed) key bytes in, take uncompressed key
/// bytes out. See the module docs.
pub struct KeyTranscoder {
    ks: KeyStream,
    out: Vec<u8>,
}

/// Decode `bytes` (compressed points) and re-encode them uncompressed, in parallel.
pub fn decompress_points(g2: bool, bytes: &[u8]) -> Result<Vec<u8>, String> {
    fn go<A: crate::decode::Decode + CanonicalSerialize + Default + Send>(
        bytes: &[u8],
    ) -> Result<Vec<u8>, String> {
        let (csz, usz) = (
            A::default().serialized_size(Compress::Yes),
            A::default().serialized_size(Compress::No),
        );
        let n = bytes.len() / csz;
        let mut out = vec![0u8; n * usz];
        out.par_chunks_mut(usz)
            .zip(bytes.par_chunks(csz))
            .try_for_each(|(o, b)| {
                let p = A::decode_compressed(b).map_err(|e| format!("proving key point: {e}"))?;
                p.serialize_uncompressed(o)
                    .map_err(|e| format!("re-encoding point: {e}"))
            })?;
        Ok(out)
    }
    if g2 {
        go::<G2Affine>(bytes)
    } else {
        go::<G1Affine>(bytes)
    }
}

impl KeyTranscoder {
    /// `chunk`: points decompressed per batch (bounds memory).
    pub fn new(chunk: usize) -> Self {
        KeyTranscoder {
            ks: KeyStream::new(chunk),
            out: Vec::new(),
        }
    }

    /// Feed the next input bytes (any chunking).
    pub fn push(&mut self, bytes: &[u8], accel: &mut dyn Accelerator) -> Result<(), String> {
        let out = &mut self.out;
        self.ks
            .push(bytes, &mut |e| -> Result<(), String> {
                match e {
                    KeyEvent::Header {
                        vk,
                        beta_g1,
                        delta_g1,
                        domain,
                        ..
                    } => {
                        out.extend_from_slice(&crate::pk::KeyFormat::header(false, domain));
                        let enc = |o: &mut Vec<u8>, v: &dyn Fn(&mut Vec<u8>) -> Result<(), ark_serialize::SerializationError>| {
                            v(o).map_err(|e| format!("re-encoding header: {e}"))
                        };
                        enc(out, &|o| vk.serialize_uncompressed(o))?;
                        enc(out, &|o| beta_g1.serialize_uncompressed(o))?;
                        enc(out, &|o| delta_g1.serialize_uncompressed(o))?;
                    }
                    KeyEvent::Len { len, .. } => out.extend_from_slice(&(len as u64).to_le_bytes()),
                    KeyEvent::Points {
                        v,
                        bytes,
                        compressed,
                        ..
                    } => {
                        let g2 = v == KeyVector::BG2;
                        if !compressed {
                            out.extend_from_slice(bytes);
                        } else if let Some(u) = accel.decompress(g2, bytes) {
                            out.extend_from_slice(&u);
                        } else {
                            out.extend_from_slice(&decompress_points(g2, bytes)?);
                        }
                    }
                }
                Ok(())
            })
            .map_err(|e| match e {
                KeyStreamError::Malformed(m) => m,
                KeyStreamError::Handler(m) => m,
            })
    }

    /// Output produced so far (and not yet taken).
    pub fn take_output(&mut self) -> Vec<u8> {
        std::mem::take(&mut self.out)
    }

    /// Whether the whole key has been read.
    pub fn is_complete(&self) -> bool {
        self.ks.is_complete()
    }

    /// Input bytes consumed so far.
    pub fn received(&self) -> u64 {
        self.ks.received()
    }
}
