//! Binary "bytecode" form of a [`PrimitiveProgram`] — a compact,
//! offset-addressed instruction stream that round-trips to the exact same
//! program.
//!
//! # Why
//!
//! `circuit.json` is the human-/tool-readable circuit artifact. This bytecode is
//! its compact sibling (`circuit.xbc`): every constraint and every
//! witness-generation (hint) op becomes a single *opcode* whose operands are
//! **witness offsets** (`VarId`s — indices into the witness vector) plus
//! immediates (field constants, small widths). It is the foundation for a
//! parallel-expandable circuit format.
//!
//! # The parallelism affordance
//!
//! The container carries an **opcode index**: one entry per opcode giving its
//! byte offset in the opcode stream plus the witness/constraint offsets it
//! produces. Because each opcode fully embeds the `VarId`s it writes and (for a
//! constraint) the constraint slot it fills, opcode `K` can be decoded and
//! expanded *in isolation* — seek to `index[K].byte_offset`, decode, done — with
//! no need to process opcodes `0..K` first. That is the property that later lets
//! expansion run in parallel; the layout is designed for it now.
//!
//! # Binary layout (little-endian throughout)
//!
//! ```text
//! header:
//!   magic            : [u8; 4]  = b"XBC\0" (version-neutral; the u16 carries the version)
//!   version          : u16      = 1
//!   flags            : u16      = 0 (reserved)
//!   field_name       : str      (u32 len + utf8 bytes)
//!   field_modulus    : str      (decimal modulus)
//!   n_vars           : u32
//!   n_constraints    : u32
//!   n_opcodes        : u32
//! vars section:        n_vars × { id: u32, role: u8, name: str }
//! opcode index:        n_opcodes × { offset: u32, base: u32 }   (8 bytes each)
//! opcode stream:       n_opcodes × { tag: u8, payload… }
//! ```
//!
//! Each index entry is **64 bits**: `offset` is the opcode's byte position in
//! the stream (relative to its start; ≤ 4 GiB), and `base` is the single output
//! coordinate the opcode produces — a constraint opcode's constraint index, or a
//! witness op's first output `VarId`. Which one it is follows from the opcode's
//! tag byte at `offset` (read in O(1), no predecessor scan), so the two were
//! collapsed from the earlier 128-bit `{u64, witness_base, constraint_base}`
//! entry (they are mutually exclusive: one was always the `NO_BASE` sentinel).
//! `base == NO_BASE` marks an opcode with no output (e.g. an empty `Bits`).
//!
//! The opcode stream is emitted constraints-first (one [`OP_CONSTRAINT`] per
//! constraint, in order) then witness-gen ops (one opcode per [`WitnessGen`]
//! kind, in order), so [`expand`] rebuilds the two ordered vectors exactly.
//!
//! Field constants are stored as a sign byte + little-endian magnitude bytes
//! (via `BigInt`), which is both compact (32 bytes for a 254-bit constant vs.
//! ~78 decimal digits) and exactly round-trips the canonical decimal we always
//! store.

use std::collections::BTreeMap;

use num_bigint::{BigInt, Sign};

use crate::circuit::R1csRow;
use crate::field::FieldConst;
use crate::linear_combination::{LinearCombination, Term, VarId};
use crate::primitive::WitnessGen;

/// Container magic: `XBC` ("Xark ByteCode") + a reserved `\0` byte. Version-neutral
/// — the format version lives in the following `u16`, not the magic.
pub const MAGIC: [u8; 4] = *b"XBC\0";

// Item tags in a looped stream.
const ITEM_OP: u8 = 0;
const ITEM_REPEAT: u8 = 1;

// Note-rule tags in a looped [`Repeat`].
const NOTE_NOCHANGE: u8 = 0;
const NOTE_TEMPLATE: u8 = 1;

/// Sentinel in the opcode index `base` field meaning "this opcode produces no
/// output witness var / no constraint".
pub const NO_BASE: u32 = u32::MAX;

// Opcode tags. One per constraint plus one per `WitnessGen` kind.
pub const OP_CONSTRAINT: u8 = 0;
pub const OP_PRODUCT: u8 = 1;
pub const OP_LINEAR: u8 = 2;
pub const OP_XOR: u8 = 3;
pub const OP_OR: u8 = 4;
pub const OP_INVERSE: u8 = 5;
pub const OP_INVERSE_OR_ZERO: u8 = 6;
pub const OP_BIT: u8 = 7;
pub const OP_BITS: u8 = 8;
pub const OP_DIVREM: u8 = 9;
pub const OP_MULMOD_DIVMOD: u8 = 10;
pub const OP_MODINVERSE: u8 = 11;
pub const OP_SUB2: u8 = 12;

/// A single decoded instruction: either a constraint or a witness-gen op.
///
/// This is the in-memory opcode model. At the byte level each `Witness` variant
/// is encoded under its own opcode tag (`OP_PRODUCT`, `OP_BIT`, …), so the wire
/// format is genuinely "one opcode per `WitnessGen` kind, plus a
/// constraint-carrying opcode".
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Opcode {
    /// An R1CS `a · b = c` constraint (fills one constraint slot).
    Constraint(R1csRow),
    /// A witness-generation op (writes its output `VarId`s).
    Witness(WitnessGen),
}

/// Errors from decoding a malformed or unsupported bytecode container.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BytecodeError {
    BadMagic,
    UnsupportedVersion(u16),
    /// Ran off the end of the buffer while decoding.
    Truncated,
    /// A string field was not valid UTF-8.
    BadUtf8,
    /// Unknown opcode / role / sign tag.
    BadTag(u8),
}

impl core::fmt::Display for BytecodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BytecodeError::BadMagic => write!(f, "bad magic (not an XBC container)"),
            BytecodeError::UnsupportedVersion(v) => write!(f, "unsupported bytecode version {v}"),
            BytecodeError::Truncated => write!(f, "truncated bytecode buffer"),
            BytecodeError::BadUtf8 => write!(f, "invalid UTF-8 in a string field"),
            BytecodeError::BadTag(t) => write!(f, "unknown tag byte {t}"),
        }
    }
}

impl std::error::Error for BytecodeError {}

// ===========================================================================
// Encoding
// ===========================================================================

fn put_u32(buf: &mut Vec<u8>, v: u32) {
    buf.extend_from_slice(&v.to_le_bytes());
}
fn put_i64(buf: &mut Vec<u8>, v: i64) {
    buf.extend_from_slice(&v.to_le_bytes());
}
/// LEB128 unsigned varint — 1 byte for values < 128 (the common case for var
/// ids, term counts, and small immediates), growing 7 bits at a time.
fn put_varint(buf: &mut Vec<u8>, mut v: u64) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            buf.push(byte);
            break;
        }
        buf.push(byte | 0x80);
    }
}
/// A `u32` value (var id / length / small immediate) as a varint.
fn put_vu32(buf: &mut Vec<u8>, v: u32) {
    put_varint(buf, u64::from(v));
}
fn put_str(buf: &mut Vec<u8>, s: &str) {
    put_varint(buf, s.len() as u64);
    buf.extend_from_slice(s.as_bytes());
}
fn put_opt_str(buf: &mut Vec<u8>, s: &Option<String>) {
    match s {
        Some(s) => {
            buf.push(1);
            put_str(buf, s);
        }
        None => buf.push(0),
    }
}

// Field-constant tag bytes. The overwhelmingly common coefficients (`1`, `-1`,
// `0`) and small integers cost one tag byte (+ a short varint), instead of the
// old `sign + 4-byte length + magnitude` (6 bytes for `1`).
const FC_ZERO: u8 = 0;
const FC_ONE: u8 = 1;
const FC_NEG_ONE: u8 = 2;
const FC_SMALL_POS: u8 = 3; // + varint value (fits u64)
const FC_SMALL_NEG: u8 = 4; // + varint |value| (fits u64)
const FC_BIG: u8 = 5; // + sign byte + varint len + LE magnitude

/// Encode a field constant with a leading tag: `0`/`1`/`-1` in a single byte,
/// other u64-sized values as tag + varint, and full field-sized values as
/// tag + sign + varint length + LE magnitude.
fn put_fieldconst(buf: &mut Vec<u8>, fc: &FieldConst) {
    let b: BigInt = fc.decimal().parse().unwrap_or_else(|_| BigInt::from(0));
    if b.sign() == Sign::NoSign {
        buf.push(FC_ZERO);
        return;
    }
    if b == BigInt::from(1) {
        buf.push(FC_ONE);
        return;
    }
    if b == BigInt::from(-1) {
        buf.push(FC_NEG_ONE);
        return;
    }
    let (sign, mag) = b.to_bytes_le();
    // Small path: magnitude fits in a u64 → tag + varint.
    if mag.len() <= 8 {
        let mut v = 0u64;
        for (i, byte) in mag.iter().enumerate() {
            v |= u64::from(*byte) << (8 * i);
        }
        buf.push(if sign == Sign::Minus {
            FC_SMALL_NEG
        } else {
            FC_SMALL_POS
        });
        put_varint(buf, v);
        return;
    }
    buf.push(FC_BIG);
    buf.push(if sign == Sign::Minus { 2 } else { 1 });
    put_varint(buf, mag.len() as u64);
    buf.extend_from_slice(&mag);
}

fn put_lc(buf: &mut Vec<u8>, lc: &LinearCombination) {
    put_fieldconst(buf, &lc.constant);
    put_varint(buf, lc.terms.len() as u64);
    for t in &lc.terms {
        put_fieldconst(buf, &t.coeff);
        put_vu32(buf, t.var);
    }
}

fn put_var_ids(buf: &mut Vec<u8>, ids: &[VarId]) {
    put_varint(buf, ids.len() as u64);
    for &id in ids {
        put_vu32(buf, id);
    }
}

fn put_lcs(buf: &mut Vec<u8>, lcs: &[LinearCombination]) {
    put_varint(buf, lcs.len() as u64);
    for lc in lcs {
        put_lc(buf, lc);
    }
}

/// Encode an R1CS row `a · b = c` — three linear combinations plus the debug
/// note.
fn put_r1csrow(buf: &mut Vec<u8>, r: &R1csRow) {
    put_lc(buf, &r.a);
    put_lc(buf, &r.b);
    put_lc(buf, &r.c);
    put_opt_str(buf, &r.note);
}

/// Encode one witness-gen op into `stream`, returning its `witness_base` (the
/// first output `VarId` it writes). Public so the DAG-compact function encoder
/// (`lower_mir`) can reuse the exact same witness wire format.
pub fn put_witness(stream: &mut Vec<u8>, w: &WitnessGen) -> u32 {
    match w {
        WitnessGen::Product { out, left, right } => {
            stream.push(OP_PRODUCT);
            put_vu32(stream, *out);
            put_lc(stream, left);
            put_lc(stream, right);
            *out
        }
        WitnessGen::Linear { out, lc } => {
            stream.push(OP_LINEAR);
            put_vu32(stream, *out);
            put_lc(stream, lc);
            *out
        }
        WitnessGen::Xor { out, a, b } => {
            stream.push(OP_XOR);
            put_vu32(stream, *out);
            put_lc(stream, a);
            put_lc(stream, b);
            *out
        }
        WitnessGen::Or { out, a, b } => {
            stream.push(OP_OR);
            put_vu32(stream, *out);
            put_lc(stream, a);
            put_lc(stream, b);
            *out
        }
        WitnessGen::Inverse { out, input } => {
            stream.push(OP_INVERSE);
            put_vu32(stream, *out);
            put_lc(stream, input);
            *out
        }
        WitnessGen::InverseOrZero { out, input } => {
            stream.push(OP_INVERSE_OR_ZERO);
            put_vu32(stream, *out);
            put_lc(stream, input);
            *out
        }
        WitnessGen::Bit { out, input, index } => {
            stream.push(OP_BIT);
            put_vu32(stream, *out);
            put_lc(stream, input);
            put_vu32(stream, *index);
            *out
        }
        WitnessGen::Bits { outs, input } => {
            stream.push(OP_BITS);
            put_var_ids(stream, outs);
            put_lc(stream, input);
            outs.first().copied().unwrap_or(NO_BASE)
        }
        WitnessGen::DivRem { q, r, num, den } => {
            stream.push(OP_DIVREM);
            put_vu32(stream, *q);
            put_vu32(stream, *r);
            put_lc(stream, num);
            put_lc(stream, den);
            *q
        }
        WitnessGen::MulModDivMod {
            q,
            r,
            a,
            b,
            modulus,
            limb_bits,
        } => {
            stream.push(OP_MULMOD_DIVMOD);
            put_var_ids(stream, q);
            put_var_ids(stream, r);
            put_lcs(stream, a);
            put_lcs(stream, b);
            put_lcs(stream, modulus);
            put_vu32(stream, *limb_bits);
            q.first().copied().unwrap_or(NO_BASE)
        }
        WitnessGen::ModInverse {
            out,
            a,
            modulus,
            limb_bits,
        } => {
            stream.push(OP_MODINVERSE);
            put_var_ids(stream, out);
            put_lcs(stream, a);
            put_lcs(stream, modulus);
            put_vu32(stream, *limb_bits);
            out.first().copied().unwrap_or(NO_BASE)
        }
        WitnessGen::Sub2 {
            qabs,
            r,
            a,
            b,
            c,
            modulus,
            limb_bits,
        } => {
            stream.push(OP_SUB2);
            put_vu32(stream, *qabs);
            put_var_ids(stream, r);
            put_lcs(stream, a);
            put_lcs(stream, b);
            put_lcs(stream, c);
            put_lcs(stream, modulus);
            put_vu32(stream, *limb_bits);
            *qabs
        }
    }
}

/// Encode one in-memory [`Opcode`] (its tag byte + payload) into `stream`. This
/// is the single encoder shared by the flat v2 stream and the v3 item stream.
fn put_opcode(stream: &mut Vec<u8>, op: &Opcode) {
    match op {
        Opcode::Constraint(r) => {
            stream.push(OP_CONSTRAINT);
            put_r1csrow(stream, r);
        }
        Opcode::Witness(w) => {
            put_witness(stream, w);
        }
    }
}

// ===========================================================================
// Decoding
// ===========================================================================

/// A minimal forward cursor over the byte buffer.
struct Cursor<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Cursor { buf, pos: 0 }
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], BytecodeError> {
        let end = self.pos.checked_add(n).ok_or(BytecodeError::Truncated)?;
        let slice = self
            .buf
            .get(self.pos..end)
            .ok_or(BytecodeError::Truncated)?;
        self.pos = end;
        Ok(slice)
    }

    fn u8(&mut self) -> Result<u8, BytecodeError> {
        Ok(self.take(1)?[0])
    }
    fn u32(&mut self) -> Result<u32, BytecodeError> {
        let b = self.take(4)?;
        Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }
    fn i64(&mut self) -> Result<i64, BytecodeError> {
        let b = self.take(8)?;
        Ok(i64::from_le_bytes([
            b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
        ]))
    }
    /// LEB128 unsigned varint (paired with [`put_varint`]).
    fn varint(&mut self) -> Result<u64, BytecodeError> {
        let mut v = 0u64;
        let mut shift = 0u32;
        loop {
            let byte = self.u8()?;
            v |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return Ok(v);
            }
            shift += 7;
            if shift >= 64 {
                return Err(BytecodeError::Truncated);
            }
        }
    }
    fn vu32(&mut self) -> Result<u32, BytecodeError> {
        Ok(self.varint()? as u32)
    }
    fn string(&mut self) -> Result<String, BytecodeError> {
        let len = self.varint()? as usize;
        let bytes = self.take(len)?;
        core::str::from_utf8(bytes)
            .map(|s| s.to_string())
            .map_err(|_| BytecodeError::BadUtf8)
    }
    fn opt_string(&mut self) -> Result<Option<String>, BytecodeError> {
        match self.u8()? {
            0 => Ok(None),
            _ => Ok(Some(self.string()?)),
        }
    }
    fn fieldconst(&mut self) -> Result<FieldConst, BytecodeError> {
        let decimal = match self.u8()? {
            FC_ZERO => "0".to_string(),
            FC_ONE => "1".to_string(),
            FC_NEG_ONE => "-1".to_string(),
            FC_SMALL_POS => self.varint()?.to_string(),
            FC_SMALL_NEG => format!("-{}", self.varint()?),
            FC_BIG => {
                let sign = match self.u8()? {
                    1 => Sign::Plus,
                    2 => Sign::Minus,
                    t => return Err(BytecodeError::BadTag(t)),
                };
                let len = self.varint()? as usize;
                let mag = self.take(len)?;
                BigInt::from_bytes_le(sign, mag).to_string()
            }
            t => return Err(BytecodeError::BadTag(t)),
        };
        Ok(FieldConst::from(decimal))
    }
    fn lc(&mut self) -> Result<LinearCombination, BytecodeError> {
        let constant = self.fieldconst()?;
        let n = self.varint()? as usize;
        let mut terms = Vec::with_capacity(n);
        for _ in 0..n {
            let coeff = self.fieldconst()?;
            let var = self.vu32()?;
            terms.push(Term { coeff, var });
        }
        Ok(LinearCombination { constant, terms })
    }
    fn var_ids(&mut self) -> Result<Vec<VarId>, BytecodeError> {
        let n = self.varint()? as usize;
        let mut ids = Vec::with_capacity(n);
        for _ in 0..n {
            ids.push(self.vu32()?);
        }
        Ok(ids)
    }
    fn lcs(&mut self) -> Result<Vec<LinearCombination>, BytecodeError> {
        let n = self.varint()? as usize;
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            out.push(self.lc()?);
        }
        Ok(out)
    }
    fn r1csrow(&mut self) -> Result<R1csRow, BytecodeError> {
        let a = self.lc()?;
        let b = self.lc()?;
        let c = self.lc()?;
        let note = self.opt_string()?;
        Ok(R1csRow { a, b, c, note })
    }

    fn opcode(&mut self) -> Result<Opcode, BytecodeError> {
        let tag = self.u8()?;
        let op = match tag {
            OP_CONSTRAINT => Opcode::Constraint(self.r1csrow()?),
            OP_PRODUCT => {
                let out = self.vu32()?;
                let left = self.lc()?;
                let right = self.lc()?;
                Opcode::Witness(WitnessGen::Product { out, left, right })
            }
            OP_LINEAR => {
                let out = self.vu32()?;
                let lc = self.lc()?;
                Opcode::Witness(WitnessGen::Linear { out, lc })
            }
            OP_XOR => {
                let out = self.vu32()?;
                let a = self.lc()?;
                let b = self.lc()?;
                Opcode::Witness(WitnessGen::Xor { out, a, b })
            }
            OP_OR => {
                let out = self.vu32()?;
                let a = self.lc()?;
                let b = self.lc()?;
                Opcode::Witness(WitnessGen::Or { out, a, b })
            }
            OP_INVERSE => {
                let out = self.vu32()?;
                let input = self.lc()?;
                Opcode::Witness(WitnessGen::Inverse { out, input })
            }
            OP_INVERSE_OR_ZERO => {
                let out = self.vu32()?;
                let input = self.lc()?;
                Opcode::Witness(WitnessGen::InverseOrZero { out, input })
            }
            OP_BIT => {
                let out = self.vu32()?;
                let input = self.lc()?;
                let index = self.vu32()?;
                Opcode::Witness(WitnessGen::Bit { out, input, index })
            }
            OP_BITS => {
                let outs = self.var_ids()?;
                let input = self.lc()?;
                Opcode::Witness(WitnessGen::Bits { outs, input })
            }
            OP_DIVREM => {
                let q = self.vu32()?;
                let r = self.vu32()?;
                let num = self.lc()?;
                let den = self.lc()?;
                Opcode::Witness(WitnessGen::DivRem { q, r, num, den })
            }
            OP_MULMOD_DIVMOD => {
                let q = self.var_ids()?;
                let r = self.var_ids()?;
                let a = self.lcs()?;
                let b = self.lcs()?;
                let modulus = self.lcs()?;
                let limb_bits = self.vu32()?;
                Opcode::Witness(WitnessGen::MulModDivMod {
                    q,
                    r,
                    a,
                    b,
                    modulus,
                    limb_bits,
                })
            }
            OP_MODINVERSE => {
                let out = self.var_ids()?;
                let a = self.lcs()?;
                let modulus = self.lcs()?;
                let limb_bits = self.vu32()?;
                Opcode::Witness(WitnessGen::ModInverse {
                    out,
                    a,
                    modulus,
                    limb_bits,
                })
            }
            OP_SUB2 => {
                let qabs = self.vu32()?;
                let r = self.var_ids()?;
                let a = self.lcs()?;
                let b = self.lcs()?;
                let c = self.lcs()?;
                let modulus = self.lcs()?;
                let limb_bits = self.vu32()?;
                Opcode::Witness(WitnessGen::Sub2 {
                    qabs,
                    r,
                    a,
                    b,
                    c,
                    modulus,
                    limb_bits,
                })
            }
            other => return Err(BytecodeError::BadTag(other)),
        };
        Ok(op)
    }
}

// ===========================================================================
// Loop rolling (v5): REPEAT opcodes
// ===========================================================================
//
// The unrolled opcode stream is highly periodic: a 254-bit scalar ladder, a
// bit-decomposition, or a hash round repeats the *same* opcode sub-sequence with
// every witness offset (`VarId`) and every affine immediate shifted by a fixed
// per-iteration stride. `roll_loops` collapses each such run into a single
// [`Repeat`] item — the body stored **once**, plus a `count` and a per-operand
// affine rule — so N near-identical iterations shrink to one body. It is pure
// lossless compression: [`expand`] replays the body `count` times to reproduce
// the exact same [`PrimitiveProgram`], byte for byte.
//
// ## The affine rule (`imm_rule`)
//
// Every varying quantity in an opcode is either **constant** across iterations
// or **linear** (`base + i·step`):
//
// * Every operand — output `VarId`s, linear-combination term vars, and the
//   `Bit`/index immediate — carries a per-slot `step` (0 = constant, i.e. a fixed
//   input referenced every iteration; nonzero = the witness/immediate stride).
//   The body stores iteration 0's values; iteration `i` adds `i·step`.
// * Debug `note` strings (constraints only) carry a per-note rule: unchanged, or
//   a template whose embedded decimal integers advance by fixed steps (e.g. the
//   var index in `b12 = xor`).
//
// A run is collapsed only after **verifying** every iteration reproduces exactly
// under the rule (structure, operands, and notes); anything that doesn't fit —
// a per-iteration round-constant table, a coefficient that scales rather than
// shifts — is left flat. Partial collapse is fine: we loop what we safely can.
//
// ## Nesting
//
// Rolling runs as repeated **passes**: pass 1 collapses the innermost (smallest-
// period) runs into [`Repeat`] items; a later pass sees the outer pattern
// (`[Repeat, ops…]` repeated) and collapses *that*, nesting the inner `Repeat`
// inside the outer body. Because an item's operands recurse through nested
// bodies, the outer affine stride shifts the inner loop's bases while the inner
// loop keeps its own steps — the two compose exactly.

/// One item in a rolled (v3) stream: a single opcode, or a loop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    /// A single flat opcode (constraint or witness op).
    Op(Opcode),
    /// A periodic run collapsed into one body + affine rule.
    Repeat(Repeat),
}

/// A collapsed periodic run: replay `body` `count` times, shifting operand slot
/// `s` by `i·steps[s]` and note slot `n` by `notes[n]` on iteration `i`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Repeat {
    /// Number of iterations (`≥ 2`).
    pub count: u32,
    /// The opcode sub-sequence, stored once (iteration 0's values). May itself
    /// contain nested [`Repeat`]s.
    pub body: Vec<Item>,
    /// Per-operand affine step, in `body`'s operand-traversal order (see
    /// [`item_operands`]). `witness_stride`/`constraint_stride` are just the
    /// dominant nonzero values here; storing per-slot steps lets a loop reference
    /// both iteration-local vars (nonzero step) and fixed inputs (step 0).
    pub steps: Vec<i64>,
    /// Per-note affine rule, in `body`'s note-traversal order (see [`item_notes`]).
    pub notes: Vec<NoteRule>,
}

/// How a constraint's debug `note` evolves across a [`Repeat`]'s iterations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NoteRule {
    /// The note is identical on every iteration (covers `None` and a constant
    /// `Some`).
    NoChange,
    /// The note is `Some` with a fixed token structure; the listed decimal runs
    /// (by their index among the string's maximal digit runs) advance by `step`
    /// each iteration. Iteration `i`'s note is iteration 0's with `i·step` added
    /// to each listed run.
    Template(Vec<(u32, i64)>),
}

// --- operand / note / structure traversal ---------------------------------
//
// Three traversals drive rolling and expansion; they MUST visit operands and
// notes in one canonical order so `steps`/`notes` line up between rolling (which
// builds them) and expansion (which applies them).

/// Visit every operand `u32` of an opcode — output vars, linear-combination term
/// vars, and the `Bit` index — in canonical order, allowing mutation.
fn visit_opcode_operands(op: &mut Opcode, f: &mut impl FnMut(&mut u32)) {
    fn lc(lc: &mut LinearCombination, f: &mut impl FnMut(&mut u32)) {
        for t in &mut lc.terms {
            f(&mut t.var);
        }
    }
    fn lcs(v: &mut [LinearCombination], f: &mut impl FnMut(&mut u32)) {
        for x in v {
            lc(x, f);
        }
    }
    match op {
        Opcode::Constraint(r) => {
            lc(&mut r.a, f);
            lc(&mut r.b, f);
            lc(&mut r.c, f);
        }
        Opcode::Witness(w) => match w {
            WitnessGen::Product { out, left, right } => {
                f(out);
                lc(left, f);
                lc(right, f);
            }
            WitnessGen::Linear { out, lc: l } => {
                f(out);
                lc(l, f);
            }
            WitnessGen::Xor { out, a, b } | WitnessGen::Or { out, a, b } => {
                f(out);
                lc(a, f);
                lc(b, f);
            }
            WitnessGen::Inverse { out, input } | WitnessGen::InverseOrZero { out, input } => {
                f(out);
                lc(input, f);
            }
            WitnessGen::Bit { out, input, index } => {
                f(out);
                lc(input, f);
                f(index);
            }
            WitnessGen::Bits { outs, input } => {
                for o in outs {
                    f(o);
                }
                lc(input, f);
            }
            WitnessGen::DivRem { q, r, num, den } => {
                f(q);
                f(r);
                lc(num, f);
                lc(den, f);
            }
            WitnessGen::MulModDivMod {
                q,
                r,
                a,
                b,
                modulus,
                ..
            } => {
                for x in q {
                    f(x);
                }
                for x in r {
                    f(x);
                }
                lcs(a, f);
                lcs(b, f);
                lcs(modulus, f);
            }
            WitnessGen::ModInverse {
                out, a, modulus, ..
            } => {
                for x in out {
                    f(x);
                }
                lcs(a, f);
                lcs(modulus, f);
            }
            WitnessGen::Sub2 {
                qabs,
                r,
                a,
                b,
                c,
                modulus,
                ..
            } => {
                f(qabs);
                for x in r {
                    f(x);
                }
                lcs(a, f);
                lcs(b, f);
                lcs(c, f);
                lcs(modulus, f);
            }
        },
    }
}

/// The note of an opcode (only constraints carry one), for mutation.
fn opcode_note_mut(op: &mut Opcode) -> Option<&mut Option<String>> {
    match op {
        Opcode::Constraint(r) => Some(&mut r.note),
        Opcode::Witness(_) => None,
    }
}

/// Append an item's operand values (recursing through nested [`Repeat`] bodies),
/// in canonical order. Nested loop `count`s/`steps` are NOT operands — only the
/// stored iteration-0 base values are.
fn item_operands(item: &Item, out: &mut Vec<u32>) {
    match item {
        Item::Op(op) => {
            // Read via the mutable visitor on a throwaway clone-free path: we only
            // read, so use a local copy of each slot.
            let mut op2 = op.clone();
            visit_opcode_operands(&mut op2, &mut |x| out.push(*x));
        }
        Item::Repeat(r) => {
            for it in &r.body {
                item_operands(it, out);
            }
        }
    }
}

/// Append an item's constraint notes (recursing through nested bodies), in
/// canonical order.
fn item_notes(item: &Item, out: &mut Vec<Option<String>>) {
    match item {
        Item::Op(Opcode::Constraint(r)) => out.push(r.note.clone()),
        Item::Op(Opcode::Witness(_)) => {}
        Item::Repeat(r) => {
            for it in &r.body {
                item_notes(it, out);
            }
        }
    }
}

/// Add `k·step` to each of `item`'s operand slots, in canonical order, pulling
/// steps from `steps[*idx]`.
fn shift_item_operands(item: &mut Item, k: i64, steps: &[i64], idx: &mut usize) {
    match item {
        Item::Op(op) => {
            visit_opcode_operands(op, &mut |x| {
                let step = steps[*idx];
                *idx += 1;
                if step != 0 {
                    *x = (i64::from(*x) + k * step) as u32;
                }
            });
        }
        Item::Repeat(r) => {
            for it in &mut r.body {
                shift_item_operands(it, k, steps, idx);
            }
        }
    }
}

/// Apply note rules for iteration `k` to each of `item`'s constraint notes.
fn shift_item_notes(item: &mut Item, k: i64, notes: &[NoteRule], idx: &mut usize) {
    match item {
        Item::Op(op) => {
            if let Some(note) = opcode_note_mut(op) {
                let rule = &notes[*idx];
                *idx += 1;
                if let (NoteRule::Template(runs), Some(s)) = (rule, note.as_ref()) {
                    *note = Some(apply_note_template(s, k, runs));
                }
            }
        }
        Item::Repeat(r) => {
            for it in &mut r.body {
                shift_item_notes(it, k, notes, idx);
            }
        }
    }
}

/// Canonical **structural** bytes of an item: its shape with all operand values
/// zeroed and all note digit-runs blanked, so two items are structurally equal
/// iff they differ only in operand bases and note integers (exactly what a
/// [`Repeat`] can express). Recurses through nested bodies (including a nested
/// `Repeat`'s `count`/`steps`/note-rule kinds, which must match for the outer
/// loop to be valid).
/// Serialize an LC into *structural* bytes: its constant and per-term coefficients
/// but with every var written as `0` (operands are what a `Repeat` steps, so they
/// must not distinguish structurally-equal blocks). Clone-free — the previous
/// impl cloned the whole opcode just to zero these, which was the dominant encode
/// cost on large circuits.
fn put_lc_struct(buf: &mut Vec<u8>, lc: &LinearCombination) {
    put_fieldconst(buf, &lc.constant);
    put_varint(buf, lc.terms.len() as u64);
    for t in &lc.terms {
        put_fieldconst(buf, &t.coeff);
        put_vu32(buf, 0);
    }
}
fn put_lcs_struct(buf: &mut Vec<u8>, lcs: &[LinearCombination]) {
    put_varint(buf, lcs.len() as u64);
    for lc in lcs {
        put_lc_struct(buf, lc);
    }
}
/// Var-id array as structural bytes: length preserved, ids zeroed (they're operands).
fn put_var_ids_struct(buf: &mut Vec<u8>, ids: &[VarId]) {
    put_varint(buf, ids.len() as u64);
    for _ in ids {
        put_vu32(buf, 0);
    }
}
/// Structural bytes of an opcode: same tags/shape as [`put_opcode`], but every
/// operand var is `0` and notes have their digit-runs blanked. Mirrors
/// [`put_witness`] and [`visit_opcode_operands`] — the set of zeroed fields must
/// match `visit_opcode_operands` exactly (only `limb_bits` is structural). Any
/// drift changes which blocks roll together and is caught by the snapshot suite.
fn put_opcode_struct(buf: &mut Vec<u8>, op: &Opcode) {
    match op {
        Opcode::Constraint(r) => {
            buf.push(OP_CONSTRAINT);
            put_lc_struct(buf, &r.a);
            put_lc_struct(buf, &r.b);
            put_lc_struct(buf, &r.c);
            match &r.note {
                Some(s) => put_opt_str(buf, &Some(blank_digits(s))),
                None => put_opt_str(buf, &None),
            }
        }
        Opcode::Witness(w) => match w {
            WitnessGen::Product { left, right, .. } => {
                buf.push(OP_PRODUCT);
                put_vu32(buf, 0);
                put_lc_struct(buf, left);
                put_lc_struct(buf, right);
            }
            WitnessGen::Linear { lc, .. } => {
                buf.push(OP_LINEAR);
                put_vu32(buf, 0);
                put_lc_struct(buf, lc);
            }
            WitnessGen::Xor { a, b, .. } => {
                buf.push(OP_XOR);
                put_vu32(buf, 0);
                put_lc_struct(buf, a);
                put_lc_struct(buf, b);
            }
            WitnessGen::Or { a, b, .. } => {
                buf.push(OP_OR);
                put_vu32(buf, 0);
                put_lc_struct(buf, a);
                put_lc_struct(buf, b);
            }
            WitnessGen::Inverse { input, .. } => {
                buf.push(OP_INVERSE);
                put_vu32(buf, 0);
                put_lc_struct(buf, input);
            }
            WitnessGen::InverseOrZero { input, .. } => {
                buf.push(OP_INVERSE_OR_ZERO);
                put_vu32(buf, 0);
                put_lc_struct(buf, input);
            }
            WitnessGen::Bit { input, .. } => {
                buf.push(OP_BIT);
                put_vu32(buf, 0);
                put_lc_struct(buf, input);
                put_vu32(buf, 0); // index is an operand
            }
            WitnessGen::Bits { outs, input } => {
                buf.push(OP_BITS);
                put_var_ids_struct(buf, outs);
                put_lc_struct(buf, input);
            }
            WitnessGen::DivRem { num, den, .. } => {
                buf.push(OP_DIVREM);
                put_vu32(buf, 0);
                put_vu32(buf, 0);
                put_lc_struct(buf, num);
                put_lc_struct(buf, den);
            }
            WitnessGen::MulModDivMod {
                q,
                r,
                a,
                b,
                modulus,
                limb_bits,
            } => {
                buf.push(OP_MULMOD_DIVMOD);
                put_var_ids_struct(buf, q);
                put_var_ids_struct(buf, r);
                put_lcs_struct(buf, a);
                put_lcs_struct(buf, b);
                put_lcs_struct(buf, modulus);
                put_vu32(buf, *limb_bits); // structural
            }
            WitnessGen::ModInverse {
                out,
                a,
                modulus,
                limb_bits,
            } => {
                buf.push(OP_MODINVERSE);
                put_var_ids_struct(buf, out);
                put_lcs_struct(buf, a);
                put_lcs_struct(buf, modulus);
                put_vu32(buf, *limb_bits); // structural
            }
            WitnessGen::Sub2 {
                r,
                a,
                b,
                c,
                modulus,
                limb_bits,
                ..
            } => {
                buf.push(OP_SUB2);
                put_vu32(buf, 0); // qabs
                put_var_ids_struct(buf, r);
                put_lcs_struct(buf, a);
                put_lcs_struct(buf, b);
                put_lcs_struct(buf, c);
                put_lcs_struct(buf, modulus);
                put_vu32(buf, *limb_bits); // structural
            }
        },
    }
}

fn item_struct_bytes(item: &Item, buf: &mut Vec<u8>) {
    match item {
        Item::Op(op) => {
            buf.push(ITEM_OP);
            put_opcode_struct(buf, op);
        }
        Item::Repeat(r) => {
            buf.push(ITEM_REPEAT);
            put_u32(buf, r.count);
            for s in &r.steps {
                put_i64(buf, *s);
            }
            buf.push(0xff); // separator
            for nr in &r.notes {
                match nr {
                    NoteRule::NoChange => buf.push(NOTE_NOCHANGE),
                    NoteRule::Template(runs) => {
                        buf.push(NOTE_TEMPLATE);
                        for (ri, st) in runs {
                            put_u32(buf, *ri);
                            put_i64(buf, *st);
                        }
                    }
                }
            }
            buf.push(0xfe); // separator
            for it in &r.body {
                item_struct_bytes(it, buf);
            }
        }
    }
}

/// Deterministic FNV-1a hash of an item's structural bytes (fast candidate
/// matching; exact structural equality is re-checked before any collapse).
fn item_hash(item: &Item) -> u64 {
    let mut buf = Vec::new();
    item_struct_bytes(item, &mut buf);
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in &buf {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

// --- note-string templating ------------------------------------------------

/// Replace every maximal ASCII-digit run with a single `#`, collapsing notes that
/// differ only in embedded integers to one structural form.
fn blank_digits(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut in_digits = false;
    for ch in s.chars() {
        if ch.is_ascii_digit() {
            if !in_digits {
                out.push('#');
                in_digits = true;
            }
        } else {
            out.push(ch);
            in_digits = false;
        }
    }
    out
}

/// Split into alternating (non-digit, digit) segments, returned as
/// `(text, is_digit)` in order. Concatenating the texts rebuilds the string.
fn tokenize_runs(s: &str) -> Vec<(String, bool)> {
    let mut runs: Vec<(String, bool)> = Vec::new();
    for ch in s.chars() {
        let d = ch.is_ascii_digit();
        match runs.last_mut() {
            Some((seg, last_d)) if *last_d == d => seg.push(ch),
            _ => runs.push((ch.to_string(), d)),
        }
    }
    runs
}

/// Apply a note [`NoteRule::Template`] to iteration-0 string `s` for iteration
/// `k`: add `k·step` to each listed digit run (by full-run index) and reassemble.
pub fn apply_note_template(s: &str, k: i64, runs: &[(u32, i64)]) -> String {
    let mut toks = tokenize_runs(s);
    for (ri, step) in runs {
        if let Some((seg, true)) = toks.get_mut(*ri as usize) {
            let base: i128 = seg.parse().unwrap_or(0);
            let v = base + i128::from(k) * i128::from(*step);
            *seg = v.to_string();
        }
    }
    toks.into_iter().map(|(seg, _)| seg).collect()
}

/// Derive the note rule taking iteration-0 `a` to iteration-1 `b`, or `None` if
/// the pair can't be expressed (differing structure / `Some`↔`None`).
pub fn derive_note_rule(a: &Option<String>, b: &Option<String>) -> Option<NoteRule> {
    match (a, b) {
        _ if a == b => Some(NoteRule::NoChange),
        (Some(a), Some(b)) => {
            let ta = tokenize_runs(a);
            let tb = tokenize_runs(b);
            if ta.len() != tb.len() {
                return None;
            }
            let mut runs = Vec::new();
            for (i, ((sa, da), (sb, db))) in ta.iter().zip(tb.iter()).enumerate() {
                if da != db {
                    return None;
                }
                if *da {
                    let va: i128 = sa.parse().ok()?;
                    let vb: i128 = sb.parse().ok()?;
                    if va != vb {
                        let step = i64::try_from(vb - va).ok()?;
                        runs.push((i as u32, step));
                    }
                } else if sa != sb {
                    return None; // non-digit text must match exactly
                }
            }
            // Verify the derived template reproduces `b` exactly (guards against
            // leading zeros / formatting surprises).
            if apply_note_template(a, 1, &runs) == *b {
                Some(NoteRule::Template(runs))
            } else {
                None
            }
        }
        _ => None,
    }
}

// --- rolling ----------------------------------------------------------------

/// Caps that keep detection near-linear on huge, heavily-repeated streams (the
/// exact per-iteration verification guarantees correctness regardless): distinct
/// candidate periods tried per position, opcodes hash-compared per candidate
/// block, and rolling passes (one per nesting level plus a few).
const MAX_PERIOD_TRIES: usize = 8;
const HASH_CHECK_CAP: usize = 32;
const MAX_ROLL_PASSES: usize = 64;

/// O(n log n)-build / O(1)-query range-minimum over a slice (half-open `[l, r)`).
/// Drives the "is a finer run nested inside this one?" test cheaply.
struct SparseMin {
    // table[k][i] = min of `data[i .. i + 2^k]`.
    table: Vec<Vec<usize>>,
}

impl SparseMin {
    fn new(data: &[usize]) -> Self {
        let n = data.len();
        let mut table = vec![data.to_vec()];
        let mut k = 1;
        while (1 << k) <= n {
            let len = 1 << k;
            let half = len >> 1;
            let prev = &table[k - 1];
            let row: Vec<usize> = (0..=n - len).map(|i| prev[i].min(prev[i + half])).collect();
            table.push(row);
            k += 1;
        }
        SparseMin { table }
    }

    /// Minimum of `[l, r)`; `usize::MAX` if empty.
    fn min(&self, l: usize, r: usize) -> usize {
        if l >= r {
            return usize::MAX;
        }
        let len = r - l;
        let k = (usize::BITS - 1 - len.leading_zeros()) as usize; // floor(log2(len))
        let row = &self.table[k];
        row[l].min(row[r - (1 << k)])
    }
}

/// Roll a single ordered opcode stream (all constraints, or all witness ops)
/// into loop items, applying passes until stable so inner loops nest inside
/// outer ones.
fn roll_stream(ops: Vec<Opcode>) -> Vec<Item> {
    let mut items: Vec<Item> = ops.into_iter().map(Item::Op).collect();
    // Carry each item's hash across passes: un-rolled items (the bulk, on every
    // pass) keep their hash, so only newly-built `Repeat`s are hashed. Re-hashing
    // every item every pass was the dominant cost of encoding large circuits
    // (ed25519's ~33s bytecode encode walks ~100k item LCs up to 64×).
    let mut hashes: Vec<u64> = items.iter().map(item_hash).collect();
    for _ in 0..MAX_ROLL_PASSES {
        let (next, next_hashes, changed) = roll_pass(items, hashes);
        items = next;
        hashes = next_hashes;
        if !changed {
            break;
        }
    }
    items
}

/// One top-level rolling pass. At each position it collapses the smallest-period
/// run *unless* a finer (smaller-period) run starts inside that run's first
/// block — in which case it defers, emitting the item flat so the finer run rolls
/// first and this one nests in a later pass. That deferral is what turns
/// `[bits…][mix][bits…][mix]` into an outer loop over `[Repeat(bits), mix]`.
fn roll_pass(items: Vec<Item>, hashes: Vec<u64>) -> (Vec<Item>, Vec<u64>, bool) {
    let n = items.len();
    if n < 2 {
        return (items, hashes, false);
    }

    // next_same[i] = next index j>i with hashes[j]==hashes[i] (candidate periods).
    let mut next_same: Vec<Option<usize>> = vec![None; n];
    let mut last: BTreeMap<u64, usize> = BTreeMap::new();
    for i in (0..n).rev() {
        next_same[i] = last.get(&hashes[i]).copied();
        last.insert(hashes[i], i);
    }

    // Smallest candidate period whose first block hash-matches (capped check),
    // per position; `usize::MAX` = no repeat starts here.
    let block_hashes_match = |i: usize, p: usize| -> bool {
        if p == 0 || i + 2 * p > n {
            return false;
        }
        (0..p.min(HASH_CHECK_CAP)).all(|j| hashes[i + j] == hashes[i + p + j])
    };
    let cand: Vec<usize> = (0..n)
        .map(|i| {
            let mut c = next_same[i];
            let mut tries = 0;
            while let Some(j) = c {
                if tries >= MAX_PERIOD_TRIES {
                    break;
                }
                tries += 1;
                if block_hashes_match(i, j - i) {
                    return j - i;
                }
                c = next_same[j];
            }
            usize::MAX
        })
        .collect();
    let rmq = SparseMin::new(&cand);

    let mut out: Vec<Item> = Vec::new();
    let mut out_hashes: Vec<u64> = Vec::new();
    let mut changed = false;
    let mut i = 0;
    while i < n {
        let mut rolled = false;
        let p = cand[i];
        if p != usize::MAX {
            // Defer if a strictly finer run starts inside the first block.
            let finer_inside = rmq.min(i + 1, i + p) < p;
            if !finer_inside {
                if let Some(rep) = try_build_repeat(&items, &hashes, i, p, n) {
                    let span = p * rep.count as usize;
                    let item = Item::Repeat(rep);
                    out_hashes.push(item_hash(&item));
                    out.push(item);
                    i += span;
                    changed = true;
                    rolled = true;
                }
            }
        }
        if !rolled {
            out_hashes.push(hashes[i]);
            out.push(items[i].clone());
            i += 1;
        }
    }
    (out, out_hashes, changed)
}

/// Attempt to collapse the run of period `p` starting at `start` into a
/// [`Repeat`], verifying structure + operand + note affinity iteration by
/// iteration. Returns the maximal valid `Repeat` (`count ≥ 2`), or `None`.
fn try_build_repeat(
    items: &[Item],
    hashes: &[u64],
    start: usize,
    p: usize,
    n: usize,
) -> Option<Repeat> {
    if p == 0 || start + 2 * p > n {
        return None;
    }

    // Fast reject: block hashes must line up for at least one repeat.
    for j in 0..p {
        if hashes[start + j] != hashes[start + p + j] {
            return None;
        }
    }

    // Structural bytes of one block, in order — reused to test each candidate
    // iteration for exact structural equality.
    let block_struct = |base: usize| -> Vec<u8> {
        let mut buf = Vec::new();
        for j in 0..p {
            item_struct_bytes(&items[base + j], &mut buf);
        }
        buf
    };
    let block_operands = |base: usize| -> Vec<u32> {
        let mut v = Vec::new();
        for j in 0..p {
            item_operands(&items[base + j], &mut v);
        }
        v
    };
    let block_notes = |base: usize| -> Vec<Option<String>> {
        let mut v = Vec::new();
        for j in 0..p {
            item_notes(&items[base + j], &mut v);
        }
        v
    };

    let s0 = block_struct(start);
    let o0 = block_operands(start);
    let o1 = block_operands(start + p);
    if o0.len() != o1.len() || block_struct(start + p) != s0 {
        return None;
    }
    // Per-operand steps (iteration 0 → 1).
    let steps: Vec<i64> = o0
        .iter()
        .zip(o1.iter())
        .map(|(a, b)| i64::from(*b) - i64::from(*a))
        .collect();

    // Per-note rules (iteration 0 → 1).
    let n0 = block_notes(start);
    let n1 = block_notes(start + p);
    if n0.len() != n1.len() {
        return None;
    }
    let mut note_rules = Vec::with_capacity(n0.len());
    for (a, b) in n0.iter().zip(n1.iter()) {
        note_rules.push(derive_note_rule(a, b)?);
    }

    // Extend the count while each further block reproduces exactly under the
    // rule. Scratch buffers are reused across iterations (filled then cleared) to
    // avoid millions of short-lived allocations — the dominant encode cost on
    // large circuits (ed25519: ~3.7M items verified here).
    let mut count = 2usize;
    let mut sbuf: Vec<u8> = Vec::with_capacity(s0.len());
    let mut obuf: Vec<u32> = Vec::with_capacity(o0.len());
    let mut nbuf: Vec<Option<String>> = Vec::with_capacity(n0.len());
    while start + (count + 1) * p <= n {
        let base = start + count * p;
        // Structure must match iteration 0 exactly.
        sbuf.clear();
        for j in 0..p {
            item_struct_bytes(&items[base + j], &mut sbuf);
        }
        if sbuf != s0 {
            break;
        }
        // Operands must be o0 + count·steps.
        obuf.clear();
        for j in 0..p {
            item_operands(&items[base + j], &mut obuf);
        }
        if obuf.len() != o0.len() {
            break;
        }
        let k = count as i64;
        let operands_ok = o0
            .iter()
            .zip(steps.iter())
            .zip(obuf.iter())
            .all(|((base0, step), actual)| i64::from(*base0) + k * step == i64::from(*actual));
        if !operands_ok {
            break;
        }
        // Notes must reproduce exactly. (Structural bytes blank digits, so this
        // exact check is still required even for `NoChange` rules.)
        nbuf.clear();
        for j in 0..p {
            item_notes(&items[base + j], &mut nbuf);
        }
        let notes_ok =
            n0.iter()
                .zip(note_rules.iter())
                .zip(nbuf.iter())
                .all(|((base_note, rule), actual)| match (rule, base_note) {
                    (NoteRule::NoChange, _) => actual == base_note,
                    (NoteRule::Template(runs), Some(s)) => {
                        Some(apply_note_template(s, k, runs)) == *actual
                    }
                    (NoteRule::Template(_), None) => false,
                });
        if !notes_ok {
            break;
        }
        count += 1;
    }

    Some(Repeat {
        count: count as u32,
        body: items[start..start + p].to_vec(),
        steps,
        notes: note_rules,
    })
}

/// Compress a homogeneous opcode run (all `Constraint`, or all `Witness`) with the
/// same periodic-run rolling as [`roll_loops`], serialized standalone as
/// `u32(item_count)` followed by the items. This lets the v8 function container
/// embed loop compression for runs of inline (non-function) rows, so a single
/// container format need not carry unrolled primitive loops. Round-trips exactly
/// via [`decode_and_expand_ops`].
pub fn roll_and_encode_ops(ops: Vec<Opcode>) -> Vec<u8> {
    let items = roll_stream(ops);
    let mut buf = Vec::new();
    put_u32(&mut buf, items.len() as u32);
    for it in &items {
        put_item(&mut buf, it);
    }
    buf
}

/// Inverse of [`roll_and_encode_ops`]: decode a standalone rolled-op blob back to
/// flat constraints and/or witness ops. A homogeneous blob yields only one of the
/// two vectors (the other stays empty).
pub fn decode_and_expand_ops(
    bytes: &[u8],
) -> Result<(Vec<R1csRow>, Vec<WitnessGen>), BytecodeError> {
    let mut c = Cursor::new(bytes);
    let n = c.u32()? as usize;
    let mut cons = Vec::new();
    let mut wit = Vec::new();
    for _ in 0..n {
        let it = c.item()?;
        emit_item(&it, &mut cons, &mut wit);
    }
    Ok((cons, wit))
}

fn put_item(buf: &mut Vec<u8>, item: &Item) {
    match item {
        Item::Op(op) => {
            buf.push(ITEM_OP);
            put_opcode(buf, op);
        }
        Item::Repeat(r) => {
            buf.push(ITEM_REPEAT);
            put_u32(buf, r.count);
            put_u32(buf, r.body.len() as u32);
            for it in &r.body {
                put_item(buf, it);
            }
            put_u32(buf, r.steps.len() as u32);
            for s in &r.steps {
                put_i64(buf, *s);
            }
            put_u32(buf, r.notes.len() as u32);
            for nr in &r.notes {
                match nr {
                    NoteRule::NoChange => buf.push(NOTE_NOCHANGE),
                    NoteRule::Template(runs) => {
                        buf.push(NOTE_TEMPLATE);
                        put_u32(buf, runs.len() as u32);
                        for (ri, st) in runs {
                            put_u32(buf, *ri);
                            put_i64(buf, *st);
                        }
                    }
                }
            }
        }
    }
}

impl Cursor<'_> {
    fn item(&mut self) -> Result<Item, BytecodeError> {
        match self.u8()? {
            ITEM_OP => Ok(Item::Op(self.opcode()?)),
            ITEM_REPEAT => {
                let count = self.u32()?;
                let n_body = self.u32()? as usize;
                let mut body = Vec::with_capacity(n_body);
                for _ in 0..n_body {
                    body.push(self.item()?);
                }
                let n_steps = self.u32()? as usize;
                let mut steps = Vec::with_capacity(n_steps);
                for _ in 0..n_steps {
                    steps.push(self.i64()?);
                }
                let n_notes = self.u32()? as usize;
                let mut notes = Vec::with_capacity(n_notes);
                for _ in 0..n_notes {
                    notes.push(match self.u8()? {
                        NOTE_NOCHANGE => NoteRule::NoChange,
                        NOTE_TEMPLATE => {
                            let nr = self.u32()? as usize;
                            let mut runs = Vec::with_capacity(nr);
                            for _ in 0..nr {
                                let ri = self.u32()?;
                                let st = self.i64()?;
                                runs.push((ri, st));
                            }
                            NoteRule::Template(runs)
                        }
                        t => return Err(BytecodeError::BadTag(t)),
                    });
                }
                Ok(Item::Repeat(Repeat {
                    count,
                    body,
                    steps,
                    notes,
                }))
            }
            t => Err(BytecodeError::BadTag(t)),
        }
    }
}

/// Materialize one item into the constraint/witness output vectors (sequential;
/// a [`Repeat`] replays its body `count` times under the affine rule).
fn emit_item(item: &Item, cons: &mut Vec<R1csRow>, wit: &mut Vec<WitnessGen>) {
    match item {
        Item::Op(Opcode::Constraint(r)) => cons.push(r.clone()),
        Item::Op(Opcode::Witness(w)) => wit.push(w.clone()),
        Item::Repeat(r) => {
            for k in 0..r.count {
                emit_repeat_iter(r, k, cons, wit);
            }
        }
    }
}

/// Materialize iteration `k` of a [`Repeat`]: clone the body, apply the operand
/// and note shifts, then emit each (possibly-nested) item.
fn emit_repeat_iter(r: &Repeat, k: u32, cons: &mut Vec<R1csRow>, wit: &mut Vec<WitnessGen>) {
    let ki = k as i64;
    let mut op_idx = 0usize;
    let mut note_idx = 0usize;
    for it in &r.body {
        match it {
            // Flat opcode (the common case — an innermost loop body): clone it
            // ONCE, apply the operand + note shifts directly to that clone, and
            // move it into the output. The old code cloned the whole body, shifted
            // it, then `emit_item` cloned every opcode a second time — doubling the
            // allocation traffic that dominates load.
            Item::Op(op) => {
                let mut op2 = op.clone();
                visit_opcode_operands(&mut op2, &mut |x| {
                    let step = r.steps[op_idx];
                    op_idx += 1;
                    if step != 0 {
                        *x = (i64::from(*x) + ki * step) as u32;
                    }
                });
                if let Some(note) = opcode_note_mut(&mut op2) {
                    let rule = &r.notes[note_idx];
                    note_idx += 1;
                    if let (NoteRule::Template(runs), Some(s)) = (rule, note.as_ref()) {
                        *note = Some(apply_note_template(s, ki, runs));
                    }
                }
                match op2 {
                    Opcode::Constraint(row) => cons.push(row),
                    Opcode::Witness(w) => wit.push(w),
                }
            }
            // Nested loop: clone it, shift all its (recursive) bases/notes under
            // the outer rule, then emit — the nested loop then applies its own
            // per-iteration steps. Nested loops are the rare minority, so the
            // extra clone here is not on the hot path.
            Item::Repeat(_) => {
                let mut nested = it.clone();
                shift_item_operands(&mut nested, ki, &r.steps, &mut op_idx);
                shift_item_notes(&mut nested, ki, &r.notes, &mut note_idx);
                emit_item(&nested, cons, wit);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::CircuitProgram;
    use crate::linear_combination::LinearCombination;
    use crate::primitive::{self, Var, VarRole};

    fn var(v: VarId) -> LinearCombination {
        LinearCombination::var(v)
    }
    /// `v · v = v`, the booleanity row (`v ∈ {0,1}`).
    fn bool_row(v: VarId, note: Option<String>) -> R1csRow {
        R1csRow {
            a: var(v),
            b: var(v),
            c: var(v),
            note,
        }
    }

    // --- loop rolling (v5) --------------------------------------------------

    /// A bit-decomposition-shaped periodic program: `n` `Bit` witness ops (output
    /// var + bit index both advance by 1, the decomposed input is a fixed var) and
    /// `n` booleanity rows with an advancing var index in the note.
    fn periodic_program(n: u32) -> CircuitProgram {
        let vars = (0..(2 + n))
            .map(|id| Var {
                id,
                name: format!("v{id}"),
                role: VarRole::Derived,
            })
            .collect();
        let mut constraints = Vec::new();
        let mut witness_gen = Vec::new();
        for i in 0..n {
            let v = 2 + i;
            witness_gen.push(WitnessGen::Bit {
                out: v,
                input: LinearCombination::var(0),
                index: i,
            });
            constraints.push(bool_row(v, Some(format!("b{v} in {{0,1}}"))));
        }
        CircuitProgram {
            field: primitive::FieldSpec::bn254(),
            vars,
            constraints,
            witness_gen,
        }
    }

    /// The standalone rolled-op blob (embedded in the v8 function container)
    /// round-trips exactly for both a constraint run and a witness run, and a
    /// large periodic run compresses to a handful of bytes.
    #[test]
    fn roll_and_encode_ops_round_trips_and_compresses() {
        for n in [1u32, 2, 8, 64, 254] {
            let prim = periodic_program(n);
            let cops: Vec<Opcode> = prim
                .constraints
                .iter()
                .cloned()
                .map(Opcode::Constraint)
                .collect();
            let (cons, wit) = decode_and_expand_ops(&roll_and_encode_ops(cops)).unwrap();
            assert_eq!(cons, prim.constraints, "n={n} constraint round-trip");
            assert!(wit.is_empty(), "n={n} constraint blob has no witness");

            let wops: Vec<Opcode> = prim
                .witness_gen
                .iter()
                .cloned()
                .map(Opcode::Witness)
                .collect();
            let (cons, wit) = decode_and_expand_ops(&roll_and_encode_ops(wops)).unwrap();
            assert_eq!(wit, prim.witness_gen, "n={n} witness round-trip");
            assert!(cons.is_empty(), "n={n} witness blob has no constraints");
        }
        // A 1000-iteration run collapses to a single Repeat (a few dozen bytes).
        let big = periodic_program(1000);
        let cops: Vec<Opcode> = big
            .constraints
            .iter()
            .cloned()
            .map(Opcode::Constraint)
            .collect();
        let rolled = roll_and_encode_ops(cops);
        assert!(
            rolled.len() < 200,
            "expected tiny rolled blob, got {}",
            rolled.len()
        );
        let (cons, _) = decode_and_expand_ops(&rolled).unwrap();
        assert_eq!(cons, big.constraints, "1000-run round-trip");
    }
}
