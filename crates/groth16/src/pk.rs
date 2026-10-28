//! Proving-key access in chunks.
//!
//! The prover pulls each key vector as a sequence of point chunks, folds each into
//! an MSM, and releases it — so a multi-hundred-MB key never has to be resident.
//! [`SerializedPk`] reads the standard `pk.bin` layout (optional `XKPK` header —
//! see [`KeyFormat`] — then ark-groth16's `CanonicalSerialize` order) from any `Read + Seek` — a file
//! on disk or bytes already in memory (the WASM case, where decompressing the whole
//! key would more than double it) — decompressing one chunk at a time.
//! [`InMemoryPk`] adapts an already-loaded `ProvingKey` (zero-copy slices).

use std::fs::File;
use std::io::{BufReader, Cursor, Read, Seek, SeekFrom};
use std::path::Path;

use crate::types::{ProvingKey, VerifyingKey};
use ark_bn254::{Bn254, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, Compress, Validate};
use rayon::prelude::*;

/// Errors reading a proving key.
#[derive(Debug)]
pub enum PkError {
    Io(std::io::Error),
    Deserialize(ark_serialize::SerializationError),
    /// An `XKPK` header this reader doesn't understand.
    Header(String),
}

/// The `pk.bin` container header, before ark-groth16's serialized key:
///
/// * v2 — `XKPK`, `0x02`, mode, then the QAP domain size as a little-endian
///   `u64` (14 bytes). Written by every current setup.
/// * v1 — `XKPK`, `0x01`, mode (6 bytes): a radix-2 domain.
/// * none — a legacy compressed key.
///
/// Mode `0` = compressed points, `1` = uncompressed. The domain size lets a
/// streaming prover compute `h` from the first bytes of the key, before the `H`
/// vector (whose length also implies it) arrives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct KeyFormat {
    pub compressed: bool,
    /// QAP domain size (v2 only).
    pub domain: Option<usize>,
    /// Bytes of header before the key body.
    pub header_len: usize,
}

/// The longest header [`KeyFormat::parse`] may need.
pub const MAX_HEADER_LEN: usize = 14;

impl KeyFormat {
    /// Parse the header at the start of `b`. `Ok(None)`: too few bytes to tell
    /// (at most [`MAX_HEADER_LEN`] are needed; a shorter key is legacy).
    pub fn parse(b: &[u8], at_eof: bool) -> Result<Option<Self>, PkError> {
        let legacy = KeyFormat {
            compressed: true,
            domain: None,
            header_len: 0,
        };
        if b.len() < 4 {
            return Ok(at_eof.then_some(legacy));
        }
        if &b[..4] != PK_MAGIC {
            return Ok(Some(legacy));
        }
        let need = match b.get(4) {
            Some(1) => 6,
            Some(2) => MAX_HEADER_LEN,
            Some(v) => {
                return Err(PkError::Header(format!(
                    "proving key header version {v} is newer than this reader (re-run `xark setup`, or update xark)"
                )));
            }
            None => 6,
        };
        if b.len() < need {
            return if at_eof {
                Err(PkError::Header("truncated proving key header".into()))
            } else {
                Ok(None)
            };
        }
        let mode = match b[5] {
            0 => true,
            1 => false,
            m => return Err(PkError::Header(format!("unknown point mode {m}"))),
        };
        let domain = (need == MAX_HEADER_LEN)
            .then(|| u64::from_le_bytes(b[6..14].try_into().unwrap()) as usize);
        Ok(Some(KeyFormat {
            compressed: mode,
            domain,
            header_len: need,
        }))
    }

    /// The header bytes: v2 with a known domain, else v1.
    pub fn header(compressed: bool, domain: Option<usize>) -> Vec<u8> {
        let mut out = PK_MAGIC.to_vec();
        out.push(if domain.is_some() { 2 } else { 1 });
        out.push(!compressed as u8);
        if let Some(n) = domain {
            out.extend_from_slice(&(n as u64).to_le_bytes());
        }
        out
    }

    pub fn compress(&self) -> Compress {
        if self.compressed {
            Compress::Yes
        } else {
            Compress::No
        }
    }
}

impl std::fmt::Display for PkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PkError::Io(e) => write!(f, "reading proving key: {e}"),
            PkError::Deserialize(e) => write!(f, "parsing proving key: {e}"),
            PkError::Header(m) => write!(f, "proving key: {m}"),
        }
    }
}

impl std::error::Error for PkError {}

impl From<std::io::Error> for PkError {
    fn from(e: std::io::Error) -> Self {
        PkError::Io(e)
    }
}

impl From<ark_serialize::SerializationError> for PkError {
    fn from(e: ark_serialize::SerializationError) -> Self {
        PkError::Deserialize(e)
    }
}

/// The G1 query vectors of a Groth16 proving key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum G1Query {
    A,
    BG1,
    H,
    L,
}

/// The small, always-resident part of a proving key plus each vector's length.
#[derive(Clone, Debug, PartialEq)]
pub struct PkHeader {
    pub vk: VerifyingKey<Bn254>,
    pub beta_g1: G1Affine,
    pub delta_g1: G1Affine,
    pub a_len: usize,
    pub b_g1_len: usize,
    pub b_g2_len: usize,
    pub h_len: usize,
    pub l_len: usize,
    /// QAP domain size, if the key's header states it (v2); otherwise implied by
    /// `h_len`.
    pub domain: Option<usize>,
}

impl PkHeader {}

/// Chunked, in-order access to a proving key's point vectors.
pub trait PkSource {
    fn header(&self) -> &PkHeader;
    /// Visit G1 vector `q` as consecutive chunks of ≤ `chunk` points:
    /// `f(offset, points)`.
    fn stream_g1(
        &mut self,
        q: G1Query,
        chunk: usize,
        f: &mut dyn FnMut(usize, &[G1Affine]),
    ) -> Result<(), PkError>;
    /// Visit the G2 `b` vector the same way.
    fn stream_g2(
        &mut self,
        chunk: usize,
        f: &mut dyn FnMut(usize, &[G2Affine]),
    ) -> Result<(), PkError>;
    /// Visit vector `v` as raw serialized chunks, `f(offset, bytes, compressed)` —
    /// for handing undecoded points to an accelerator. Returns `Ok(false)` if this
    /// source has no serialized form (the caller falls back to decoded chunks).
    fn stream_raw(
        &mut self,
        _v: KeyVector,
        _chunk: usize,
        _f: &mut dyn FnMut(usize, &[u8], bool),
    ) -> Result<bool, PkError> {
        Ok(false)
    }
}

/// Any of the five point vectors (G1 except [`KeyVector::BG2`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeyVector {
    A,
    BG1,
    BG2,
    H,
    L,
}

impl KeyVector {
    fn index(self) -> usize {
        match self {
            KeyVector::A => 0,
            KeyVector::BG1 => 1,
            KeyVector::BG2 => 2,
            KeyVector::H => 3,
            KeyVector::L => 4,
        }
    }
}

impl From<G1Query> for KeyVector {
    fn from(q: G1Query) -> Self {
        match q {
            G1Query::A => KeyVector::A,
            G1Query::BG1 => KeyVector::BG1,
            G1Query::H => KeyVector::H,
            G1Query::L => KeyVector::L,
        }
    }
}

/// A fully-loaded `ProvingKey` (chunks are borrowed slices; nothing is copied).
pub struct InMemoryPk<'a> {
    pk: &'a ProvingKey<Bn254>,
    header: PkHeader,
}

impl<'a> InMemoryPk<'a> {
    pub fn new(pk: &'a ProvingKey<Bn254>) -> Self {
        InMemoryPk {
            header: PkHeader {
                vk: pk.vk.clone(),
                beta_g1: pk.beta_g1,
                delta_g1: pk.delta_g1,
                a_len: pk.a_query.len(),
                b_g1_len: pk.b_g1_query.len(),
                b_g2_len: pk.b_g2_query.len(),
                h_len: pk.h_query.len(),
                l_len: pk.l_query.len(),
                domain: None,
            },
            pk,
        }
    }
}

impl PkSource for InMemoryPk<'_> {
    fn header(&self) -> &PkHeader {
        &self.header
    }
    fn stream_g1(
        &mut self,
        q: G1Query,
        chunk: usize,
        f: &mut dyn FnMut(usize, &[G1Affine]),
    ) -> Result<(), PkError> {
        let v = match q {
            G1Query::A => &self.pk.a_query,
            G1Query::BG1 => &self.pk.b_g1_query,
            G1Query::H => &self.pk.h_query,
            G1Query::L => &self.pk.l_query,
        };
        for (i, c) in v.chunks(chunk.max(1)).enumerate() {
            f(i * chunk.max(1), c);
        }
        Ok(())
    }
    fn stream_g2(
        &mut self,
        chunk: usize,
        f: &mut dyn FnMut(usize, &[G2Affine]),
    ) -> Result<(), PkError> {
        for (i, c) in self.pk.b_g2_query.chunks(chunk.max(1)).enumerate() {
            f(i * chunk.max(1), c);
        }
        Ok(())
    }
}

const PK_MAGIC: &[u8; 4] = b"XKPK";

/// A serialized `pk.bin`, decoded chunk-by-chunk on demand.
pub struct SerializedPk<R: Read + Seek> {
    r: R,
    compress: Compress,
    header: PkHeader,
    /// Byte offset of each vector's first point: a, b_g1, b_g2, h, l.
    offsets: [u64; 5],
    bytes: Vec<u8>,
    tee: Option<Tee>,
}

/// Re-encodes the decoded points, uncompressed, as the prover reads them.
struct Tee {
    w: Box<dyn std::io::Write>,
    /// The next vector (file order) it expects; any other order disables it.
    next: usize,
    ok: bool,
}

impl SerializedPk<BufReader<File>> {
    /// Stream a proving key from disk.
    pub fn open(path: &Path) -> Result<Self, PkError> {
        Self::new(BufReader::with_capacity(1 << 20, File::open(path)?))
    }
}

impl<'a> SerializedPk<Cursor<&'a [u8]>> {
    /// Stream a proving key already in memory as serialized bytes.
    pub fn from_bytes(bytes: &'a [u8]) -> Result<Self, PkError> {
        Self::new(Cursor::new(bytes))
    }
}

fn point_size<A: AffineRepr>(c: Compress) -> usize {
    A::generator().serialized_size(c)
}

impl<R: Read + Seek> SerializedPk<R> {
    /// Parse the header and record each vector's offset (seeks past the point
    /// data; nothing but lengths is read).
    pub fn new(mut r: R) -> Result<Self, PkError> {
        let mut head = [0u8; MAX_HEADER_LEN];
        let n = read_up_to(&mut r, &mut head)?;
        let fmt = KeyFormat::parse(&head[..n], true)?.expect("parse at EOF always decides");
        let compress = fmt.compress();
        r.seek(SeekFrom::Start(fmt.header_len as u64))?;
        let v = Validate::No;
        let vk = VerifyingKey::<Bn254>::deserialize_with_mode(&mut r, compress, v)?;
        let beta_g1 = G1Affine::deserialize_with_mode(&mut r, compress, v)?;
        let delta_g1 = G1Affine::deserialize_with_mode(&mut r, compress, v)?;
        let (g1, g2) = (
            point_size::<G1Affine>(compress) as u64,
            point_size::<G2Affine>(compress) as u64,
        );
        let mut offsets = [0u64; 5];
        let mut lens = [0usize; 5];
        for (i, sz) in [g1, g1, g2, g1, g1].into_iter().enumerate() {
            let len = u64::deserialize_with_mode(&mut r, compress, v)?;
            offsets[i] = r.stream_position()?;
            lens[i] = len as usize;
            r.seek(SeekFrom::Current((len * sz) as i64))?;
        }
        Ok(SerializedPk {
            r,
            compress,
            header: PkHeader {
                vk,
                beta_g1,
                delta_g1,
                a_len: lens[0],
                b_g1_len: lens[1],
                b_g2_len: lens[2],
                h_len: lens[3],
                l_len: lens[4],
                domain: fmt.domain,
            },
            offsets,
            bytes: Vec::new(),
            tee: None,
        })
    }

    /// Whether the points are stored compressed.
    pub fn is_compressed(&self) -> bool {
        matches!(self.compress, Compress::Yes)
    }

    /// While proving, also write an **uncompressed** copy of this key to `w` (the
    /// points are decoded anyway), so later proofs can skip decompression. The
    /// copy is only complete if every vector is read in file order — check with
    /// [`finish_tee`](Self::finish_tee).
    pub fn tee_uncompressed(&mut self, mut w: Box<dyn std::io::Write>) -> std::io::Result<()> {
        use ark_serialize::CanonicalSerialize;
        let io = |e: ark_serialize::SerializationError| std::io::Error::other(e.to_string());
        w.write_all(&KeyFormat::header(false, self.header.domain))?;
        self.header.vk.serialize_uncompressed(&mut w).map_err(io)?;
        self.header
            .beta_g1
            .serialize_uncompressed(&mut w)
            .map_err(io)?;
        self.header
            .delta_g1
            .serialize_uncompressed(&mut w)
            .map_err(io)?;
        self.tee = Some(Tee {
            w,
            next: 0,
            ok: true,
        });
        Ok(())
    }

    /// Flush the uncompressed copy; `true` if it is a complete key.
    pub fn finish_tee(&mut self) -> std::io::Result<bool> {
        match self.tee.take() {
            Some(mut t) => {
                t.w.flush()?;
                Ok(t.ok && t.next == 5)
            }
            None => Ok(false),
        }
    }

    fn lens(&self) -> [usize; 5] {
        let h = &self.header;
        [h.a_len, h.b_g1_len, h.b_g2_len, h.h_len, h.l_len]
    }

    /// Read vector `v` in chunks of raw bytes: `f(offset, bytes)`.
    #[allow(clippy::type_complexity)]
    fn stream_bytes(
        &mut self,
        v: KeyVector,
        chunk: usize,
        f: &mut dyn FnMut(usize, &[u8]) -> Result<(), PkError>,
    ) -> Result<(), PkError> {
        let sz = if v == KeyVector::BG2 {
            point_size::<G2Affine>(self.compress)
        } else {
            point_size::<G1Affine>(self.compress)
        };
        let len = self.lens()[v.index()];
        let chunk = chunk.max(1);
        self.r.seek(SeekFrom::Start(self.offsets[v.index()]))?;
        let mut bytes = std::mem::take(&mut self.bytes);
        let mut i = 0;
        while i < len {
            let this = chunk.min(len - i);
            bytes.resize(this * sz, 0);
            self.r.read_exact(&mut bytes)?;
            f(i, &bytes)?;
            i += this;
        }
        self.bytes = bytes;
        Ok(())
    }

    fn stream<A: AffineRepr + crate::decode::Decode + Send>(
        &mut self,
        v: KeyVector,
        chunk: usize,
        f: &mut dyn FnMut(usize, &[A]),
    ) -> Result<(), PkError> {
        let c = self.compress;
        let sz = point_size::<A>(c);
        let mut pts: Vec<A> = Vec::new();
        let mut tee = self.tee.take();
        if let Some(t) = tee.as_mut() {
            t.ok &= t.next == v.index();
            if t.ok {
                let len = self.lens()[v.index()] as u64;
                t.ok = t.w.write_all(&len.to_le_bytes()).is_ok();
            }
        }
        let res = self.stream_bytes(v, chunk, &mut |off, bytes| {
            pts.clear();
            // `Validate::No`: the proving key is our own setup output; a corrupt
            // point can only yield a proof that fails verification (and point
            // decompression still rejects off-curve x).
            pts.try_par_extend(
                bytes
                    .par_chunks(sz)
                    .map(|b| crate::decode::point::<A>(b, c)),
            )
            .map_err(PkError::Deserialize)?;
            if let Some(t) = tee.as_mut().filter(|t| t.ok) {
                for p in &pts {
                    if p.serialize_uncompressed(&mut t.w).is_err() {
                        t.ok = false;
                        break;
                    }
                }
            }
            f(off, &pts);
            Ok(())
        });
        if let Some(t) = tee.as_mut() {
            t.next += 1;
        }
        self.tee = tee;
        res
    }
}

/// `par_extend` from a fallible iterator, keeping the first error.
trait ParExtendResult<T> {
    fn try_par_extend<I>(&mut self, it: I) -> Result<(), ark_serialize::SerializationError>
    where
        I: IndexedParallelIterator<Item = Result<T, ark_serialize::SerializationError>>;
}

impl<T: Send> ParExtendResult<T> for Vec<T> {
    fn try_par_extend<I>(&mut self, it: I) -> Result<(), ark_serialize::SerializationError>
    where
        I: IndexedParallelIterator<Item = Result<T, ark_serialize::SerializationError>>,
    {
        let v: Result<Vec<T>, _> = it.collect();
        self.extend(v?);
        Ok(())
    }
}

fn read_up_to<R: Read>(r: &mut R, buf: &mut [u8]) -> std::io::Result<usize> {
    let mut n = 0;
    while n < buf.len() {
        match r.read(&mut buf[n..])? {
            0 => break,
            k => n += k,
        }
    }
    Ok(n)
}

impl<R: Read + Seek> PkSource for SerializedPk<R> {
    fn header(&self) -> &PkHeader {
        &self.header
    }
    fn stream_g1(
        &mut self,
        q: G1Query,
        chunk: usize,
        f: &mut dyn FnMut(usize, &[G1Affine]),
    ) -> Result<(), PkError> {
        self.stream(q.into(), chunk, f)
    }
    fn stream_g2(
        &mut self,
        chunk: usize,
        f: &mut dyn FnMut(usize, &[G2Affine]),
    ) -> Result<(), PkError> {
        self.stream(KeyVector::BG2, chunk, f)
    }
    fn stream_raw(
        &mut self,
        v: KeyVector,
        chunk: usize,
        f: &mut dyn FnMut(usize, &[u8], bool),
    ) -> Result<bool, PkError> {
        let compressed = matches!(self.compress, Compress::Yes);
        if let Some(t) = self.tee.as_mut() {
            t.ok = false; // raw chunks go to an accelerator undecoded
        }
        self.stream_bytes(v, chunk, &mut |off, b| {
            f(off, b, compressed);
            Ok(())
        })?;
        Ok(true)
    }
}
