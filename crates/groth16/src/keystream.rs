//! Push-driven parsing of a serialized proving key (`pk.bin`): feed bytes in any
//! chunking, get events — the header, each vector's length, and point chunks of
//! at most a fixed size — in file order. Shared by [`PushProver`] (folds chunks
//! into MSMs) and [`KeyTranscoder`] (re-encodes them uncompressed).
//!
//! [`PushProver`]: crate::push::PushProver
//! [`KeyTranscoder`]: crate::transcode::KeyTranscoder

use crate::types::VerifyingKey;
use ark_bn254::{Bn254, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};

use crate::pk::{KeyFormat, KeyVector};

/// File order of the point vectors.
pub const ORDER: [KeyVector; 5] = [
    KeyVector::A,
    KeyVector::BG1,
    KeyVector::BG2,
    KeyVector::H,
    KeyVector::L,
];

/// What the parser found.
pub enum KeyEvent<'a> {
    /// The fixed part: `vk`, `β₁`, `δ₁`, the point encoding, and the QAP domain
    /// size if the header states it ([`KeyFormat`] v2).
    Header {
        vk: &'a VerifyingKey<Bn254>,
        beta_g1: G1Affine,
        delta_g1: G1Affine,
        compressed: bool,
        domain: Option<usize>,
    },
    /// The next vector and its point count.
    Len { v: KeyVector, len: usize },
    /// Points `[offset, offset + n)` of vector `v`, still serialized.
    Points {
        v: KeyVector,
        offset: usize,
        bytes: &'a [u8],
        compressed: bool,
    },
}

/// A parse failure, or an error the event handler returned.
#[derive(Debug)]
pub enum KeyStreamError<E> {
    Malformed(String),
    Handler(E),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Stage {
    Header,
    Len(usize),
    Points { i: usize, len: usize, done: usize },
    Done,
}

/// The parser state. See the module docs.
pub struct KeyStream {
    stage: Stage,
    buf: Vec<u8>,
    compress: Compress,
    chunk: usize,
    received: u64,
}

impl KeyStream {
    /// `chunk`: the most points delivered per [`KeyEvent::Points`].
    pub fn new(chunk: usize) -> Self {
        KeyStream {
            stage: Stage::Header,
            buf: Vec::new(),
            compress: Compress::Yes,
            chunk: chunk.max(1),
            received: 0,
        }
    }

    pub fn received(&self) -> u64 {
        self.received
    }

    pub fn is_complete(&self) -> bool {
        self.stage == Stage::Done
    }

    fn point_size(&self, i: usize) -> usize {
        if ORDER[i] == KeyVector::BG2 {
            G2Affine::generator().serialized_size(self.compress)
        } else {
            G1Affine::generator().serialized_size(self.compress)
        }
    }

    /// Feed the next bytes; `f` sees every event they complete, in order.
    pub fn push<E>(
        &mut self,
        bytes: &[u8],
        f: &mut dyn FnMut(KeyEvent) -> Result<(), E>,
    ) -> Result<(), KeyStreamError<E>> {
        self.received += bytes.len() as u64;
        if self.stage == Stage::Header {
            self.buf.extend_from_slice(bytes);
            let rest = match self.try_header(f)? {
                None => return Ok(()),
                Some(rest) => rest,
            };
            return self.body(&rest, f);
        }
        self.body(bytes, f)
    }

    fn try_header<E>(
        &mut self,
        f: &mut dyn FnMut(KeyEvent) -> Result<(), E>,
    ) -> Result<Option<Vec<u8>>, KeyStreamError<E>> {
        let b = &self.buf;
        let fmt = match KeyFormat::parse(b, false) {
            Ok(Some(f)) => f,
            Ok(None) => return Ok(None),
            Err(e) => return Err(KeyStreamError::Malformed(e.to_string())),
        };
        let compress = fmt.compress();
        let mut cur = &b[fmt.header_len..];
        let v = Validate::No;
        let parsed = (|| {
            let vk = VerifyingKey::<Bn254>::deserialize_with_mode(&mut cur, compress, v)?;
            let beta = G1Affine::deserialize_with_mode(&mut cur, compress, v)?;
            let delta = G1Affine::deserialize_with_mode(&mut cur, compress, v)?;
            Ok::<_, ark_serialize::SerializationError>((vk, beta, delta))
        })();
        match parsed {
            Ok((vk, beta_g1, delta_g1)) => {
                let rest = cur.to_vec();
                self.compress = compress;
                self.buf.clear();
                self.stage = Stage::Len(0);
                f(KeyEvent::Header {
                    vk: &vk,
                    beta_g1,
                    delta_g1,
                    compressed: matches!(compress, Compress::Yes),
                    domain: fmt.domain,
                })
                .map_err(KeyStreamError::Handler)?;
                Ok(Some(rest))
            }
            // Too short so far (the header is a few KB at most).
            Err(_) if self.buf.len() < (1 << 24) => Ok(None),
            Err(e) => Err(KeyStreamError::Malformed(format!(
                "proving key header: {e}"
            ))),
        }
    }

    fn body<E>(
        &mut self,
        mut bytes: &[u8],
        f: &mut dyn FnMut(KeyEvent) -> Result<(), E>,
    ) -> Result<(), KeyStreamError<E>> {
        loop {
            match self.stage {
                Stage::Done => {
                    return if bytes.is_empty() {
                        Ok(())
                    } else {
                        Err(KeyStreamError::Malformed(
                            "bytes after the end of the proving key".into(),
                        ))
                    };
                }
                Stage::Header => unreachable!("header handled in push"),
                Stage::Len(i) => {
                    let take = (8 - self.buf.len()).min(bytes.len());
                    self.buf.extend_from_slice(&bytes[..take]);
                    bytes = &bytes[take..];
                    if self.buf.len() < 8 {
                        return Ok(());
                    }
                    let len = u64::from_le_bytes(self.buf[..8].try_into().unwrap()) as usize;
                    self.buf.clear();
                    f(KeyEvent::Len { v: ORDER[i], len }).map_err(KeyStreamError::Handler)?;
                    self.stage = Stage::Points { i, len, done: 0 };
                }
                Stage::Points { i, len, done } => {
                    if done == len {
                        self.stage = if i < 4 {
                            Stage::Len(i + 1)
                        } else {
                            Stage::Done
                        };
                        continue;
                    }
                    if bytes.is_empty() {
                        return Ok(());
                    }
                    let psz = self.point_size(i);
                    let n = self.chunk.min(len - done);
                    let take = (n * psz - self.buf.len()).min(bytes.len());
                    self.buf.extend_from_slice(&bytes[..take]);
                    bytes = &bytes[take..];
                    if self.buf.len() < n * psz {
                        return Ok(());
                    }
                    f(KeyEvent::Points {
                        v: ORDER[i],
                        offset: done,
                        bytes: &self.buf,
                        compressed: matches!(self.compress, Compress::Yes),
                    })
                    .map_err(KeyStreamError::Handler)?;
                    self.buf.clear();
                    self.stage = Stage::Points {
                        i,
                        len,
                        done: done + n,
                    };
                }
            }
        }
    }
}
