//! Groth16 BN254 verifier core (little-endian wire format).
//!
//! # Wire format
//!
//! The Solana `alt_bn128` group-op syscall has explicit little-endian
//! variants (selected with the `0x80` flag). This crate's wire format is LE
//! end-to-end: every `Fq` and `Fr` element is encoded as a 32-byte
//! little-endian limb, so the bytes go straight to the syscall without
//! conversion. All curve arithmetic is delegated to [`solana_nostd_alt_bn128`].
//!
//! ```text
//! vk_bytes : alpha (G1, 64 B)
//! | beta (G2, 128 B)
//! | gamma (G2, 128 B)
//! | delta (G2, 128 B)
//! | (N+1) * G1 (64 B each) // IC; count implied by length
//! proof_bytes : A (G1, 64 B) | B (G2, 128 B) | C (G1, 64 B) (256 B)
//! public_inputs: num_inputs * Fr (32 B LE each)
//! ```
//!
//! * G1 = `x || y` where each coord is 32 B LE Fq.
//! * G2 = `x.c0 || x.c1 || y.c0 || y.c1` where each Fq is 32 B LE.
//! * `proof.A` is pre-negated by the exporter so the program doesn't have
//!   to do a modular subtraction inside the syscall path.
//!
//! # Public-input linear combination
//!
//! `vk_x = ic[0] + Σ inputs[i] · ic[i+1]`, computed via the G1 mul + add
//! syscalls. Final pairing check:
//!
//! ```text
//! e(-A, B) · e(α, β) · e(vk_x, γ) · e(C, δ) == 1
//! ```
//!
//! evaluated as a single multi-pair call with 4 × 192 = 768 input bytes.
//!
//! # BN254 backend
//!
//! All curve arithmetic goes through [`solana_nostd_alt_bn128`], whose
//! `G1Point` / `G2Point` operators and [`pairing`] resolve to the
//! `alt_bn128` syscalls on `target_os = "solana"` and to an Arkworks
//! reference implementation off-chain. The same [`verify_groth16`] code
//! therefore runs unchanged in host tests and on-chain — no backend
//! abstraction, and nothing but `core` is linked into the SBF build.

use solana_nostd_alt_bn128::{AltBn128Error, G1Point, G2Point, pairing};
use solana_program_error::ProgramError;

// -- byte-layout constants ----------------------------------------------------

/// Width of a G1 point on the wire.
pub const G1_BYTES: usize = 64;
/// Width of a G2 point on the wire.
pub const G2_BYTES: usize = 128;
/// Width of an Fr scalar on the wire.
pub const FR_BYTES: usize = 32;
/// Width of a single pairing operand `(G1, G2)`.
pub const PAIRING_PAIR_BYTES: usize = G1_BYTES + G2_BYTES;
/// Width of the proof: `A || B || C`.
pub const PROOF_BYTES: usize = G1_BYTES + G2_BYTES + G1_BYTES;
/// Fixed-size prefix of the VK: `alpha || beta || gamma || delta`.
pub const VK_FIXED_PREFIX_BYTES: usize = G1_BYTES + 3 * G2_BYTES;

/// BN254 scalar field order `r`, little-endian
/// (`0x30644e72…f0000001`). Public-input scalars must be *canonical* —
/// strictly less than `r`.
///
/// Without this check the encodings `v`, `v + r`, `v + 2r`, … all reduce to
/// the same field element and so verify against the same proof. A caller could
/// then present one proof under several distinct 32-byte public-input values;
/// a program that reads a public input as an integer (nullifier, amount, root,
/// …) would see a different value than the proof actually attests to. So we
/// reject any non-canonical public input up front.
const FR_MODULUS_LE: [u8; FR_BYTES] = [
    0x01, 0x00, 0x00, 0xf0, 0x93, 0xf5, 0xe1, 0x43, 0x91, 0x70, 0xb9, 0x79, 0x48, 0xe8, 0x33, 0x28,
    0x5d, 0x58, 0x81, 0x81, 0xb6, 0x45, 0x50, 0xb8, 0x29, 0xa0, 0x31, 0xe1, 0x72, 0x4e, 0x64, 0x30,
];

/// BN254 base field order `q`, little-endian (`0x30644e72…d87cfd47`). Every
/// G1/G2 coordinate is an `Fq` element; a *canonical* encoding is `< q`, which
/// also forces the two unused top bits of the 32-byte limb to zero.
///
/// The `alt_bn128` syscall (and its Arkworks host reference) **mask** those top
/// bits when decoding a point — so without an explicit check, the encodings
/// `c`, `c + q`, … and any value with the unused top bits flipped all decode to
/// the *same* point and verify against the same proof. That is proof/VK
/// encoding malleability: a third party can mangle a valid proof's bytes and it
/// still verifies. The `*_strict` entry points reject it.
const FQ_MODULUS_LE: [u8; FR_BYTES] = [
    0x47, 0xfd, 0x7c, 0xd8, 0x16, 0x8c, 0x20, 0x3c, 0x8d, 0xca, 0x71, 0x68, 0x91, 0x6a, 0x81, 0x97,
    0x5d, 0x58, 0x81, 0x81, 0xb6, 0x45, 0x50, 0xb8, 0x29, 0xa0, 0x31, 0xe1, 0x72, 0x4e, 0x64, 0x30,
];

/// `true` iff little-endian `a < m`.
#[inline]
fn le_lt(a: &[u8; FR_BYTES], m: &[u8; FR_BYTES]) -> bool {
    // Compare most-significant byte first (index 31 in little-endian).
    let mut i = FR_BYTES;
    while i > 0 {
        i -= 1;
        if a[i] != m[i] {
            return a[i] < m[i];
        }
    }
    false // a == m is not `<`
}

/// `true` iff the 32-byte little-endian scalar is a canonical `Fr` value
/// (`< r`).
pub(crate) fn scalar_is_canonical(s: &[u8; FR_BYTES]) -> bool {
    le_lt(s, &FR_MODULUS_LE)
}

/// `true` iff the 32-byte little-endian value is a canonical `Fq` coordinate
/// (`< q`).
pub(crate) fn fq_is_canonical(c: &[u8; FR_BYTES]) -> bool {
    le_lt(c, &FQ_MODULUS_LE)
}

/// `true` iff every 32-byte little-endian field element in `bytes` is a
/// canonical `Fq` coordinate (`< q`). `bytes` is a concatenation of 32-byte
/// coordinates — a single G1/G2 point, or a whole VK/proof blob, every byte of
/// which is part of some coordinate. A trailing partial chunk (a malformed,
/// non-multiple-of-32 length) is ignored here and caught by the structural
/// checks in [`verify_groth16`].
pub(crate) fn coords_canonical(bytes: &[u8]) -> bool {
    let mut c = [0u8; FR_BYTES];
    for chunk in bytes.chunks_exact(FR_BYTES) {
        c.copy_from_slice(chunk);
        if !fq_is_canonical(&c) {
            return false;
        }
    }
    true
}

// -- error type ---------------------------------------------------------------

/// Reasons `verify_groth16` may reject an input. Most are structural /
/// arity checks performed *before* any curve arithmetic; [`Syscall`] wraps
/// a failure from the BN254 backend (a malformed point the `alt_bn128`
/// syscall rejects, or a pairing-input error).
///
/// [`Syscall`]: VerifierError::Syscall
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerifierError {
    /// `vk_bytes` is shorter than the fixed prefix + one IC element.
    TruncatedVk { expected: usize, actual: usize },
    /// The IC region (`vk_bytes` past the fixed prefix) is not a whole
    /// number of 64-byte G1 points.
    IcLengthMismatch { expected: usize, actual: usize },
    /// `proof_bytes` is not exactly [`PROOF_BYTES`].
    ProofLength { expected: usize, actual: usize },
    /// `public_inputs` length is not a multiple of [`FR_BYTES`].
    PublicInputsLength {
        fr: usize,
        expected: usize,
        actual: usize,
    },
    /// The number of public inputs does not equal `ic_count - 1`.
    InputArityMismatch {
        ic_count: u32,
        expected_inputs: u32,
        actual_inputs: u32,
    },
    /// A public-input scalar is not canonical — its 32-byte little-endian
    /// value is `>= r`, the BN254 scalar field order. Rejected to prevent
    /// public-input encoding malleability.
    NonCanonicalPublicInput { index: u32 },
    /// A G1/G2 coordinate in the VK or proof is not a canonical `Fq` encoding
    /// (its 32-byte little-endian value is `>= q`, e.g. one of the unused top
    /// bits is set). Only the `*_strict` entry points reject this; it prevents
    /// proof/VK encoding malleability, since the syscall masks those bits.
    NonCanonicalCoordinate,
    /// The BN254 backend (an `alt_bn128` syscall, or its host reference)
    /// rejected an operand or pairing input.
    Syscall,
}

impl core::fmt::Display for VerifierError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            VerifierError::TruncatedVk { expected, actual } => write!(
                f,
                "vk_bytes shorter than the fixed prefix + one IC element ({expected} B): got {actual} B"
            ),
            VerifierError::IcLengthMismatch { expected, actual } => write!(
                f,
                "vk IC region is not a whole number of 64-byte G1 points: rounded to {expected} B, got {actual} B"
            ),
            VerifierError::ProofLength { expected, actual } => {
                write!(f, "proof_bytes must be exactly {expected} B; got {actual}")
            }
            VerifierError::PublicInputsLength {
                fr,
                expected,
                actual,
            } => write!(
                f,
                "public_inputs must be {expected} B (num_inputs * {fr}); got {actual}"
            ),
            VerifierError::InputArityMismatch {
                ic_count,
                expected_inputs,
                actual_inputs,
            } => write!(
                f,
                "public-input arity mismatch: vk has ic_count={ic_count} (=> {expected_inputs} inputs), got {actual_inputs}"
            ),
            VerifierError::NonCanonicalPublicInput { index } => write!(
                f,
                "public input #{index} is not canonical (>= the BN254 scalar field order r)"
            ),
            VerifierError::NonCanonicalCoordinate => f.write_str(
                "a VK or proof coordinate is not a canonical Fq encoding (>= the base field order q)",
            ),
            VerifierError::Syscall => f.write_str("alt_bn128 backend rejected an operand"),
        }
    }
}

impl From<VerifierError> for ProgramError {
    fn from(_e: VerifierError) -> Self {
        ProgramError::InvalidInstructionData
    }
}

impl From<AltBn128Error> for VerifierError {
    fn from(_e: AltBn128Error) -> Self {
        VerifierError::Syscall
    }
}

// -- point readers ------------------------------------------------------------

/// Read a G1 point (`x || y`, 64 B LE) from `buf` at `off`. `buf[off..]`
/// must already be known to hold at least [`G1_BYTES`].
#[inline]
fn g1_at(buf: &[u8], off: usize) -> G1Point {
    let mut bytes = [0u8; G1_BYTES];
    bytes.copy_from_slice(&buf[off..off + G1_BYTES]);
    G1Point::from_le_bytes(bytes)
}

/// Read a G2 point (128 B LE) from `buf` at `off`. `buf[off..]` must already
/// be known to hold at least [`G2_BYTES`].
#[inline]
fn g2_at(buf: &[u8], off: usize) -> G2Point {
    let mut bytes = [0u8; G2_BYTES];
    bytes.copy_from_slice(&buf[off..off + G2_BYTES]);
    G2Point::from_le_bytes(bytes)
}

// -- core verifier ------------------------------------------------------------

/// Verify a Groth16 proof. The curve arithmetic resolves to the `alt_bn128`
/// syscalls on `target_os = "solana"` and to the Arkworks reference path
/// off-chain (see [`solana_nostd_alt_bn128`]), so this same function backs
/// both the deployed program and host tests.
pub fn verify_groth16(
    vk_bytes: &[u8],
    proof_bytes: &[u8],
    public_inputs: &[u8],
) -> Result<bool, VerifierError> {
    // ---- Parse VK ----------------------------------------------------------
    // VK = alpha(G1) | beta(G2) | gamma(G2) | delta(G2) | (N+1) × G1 (IC).
    // The IC count is *implied by length* — there is no ic_count field on the
    // wire — so it can never disagree with the actual bytes.
    if vk_bytes.len() < VK_FIXED_PREFIX_BYTES + G1_BYTES {
        return Err(VerifierError::TruncatedVk {
            expected: VK_FIXED_PREFIX_BYTES + G1_BYTES,
            actual: vk_bytes.len(),
        });
    }
    let alpha = g1_at(vk_bytes, 0);
    let beta = g2_at(vk_bytes, G1_BYTES);
    let gamma = g2_at(vk_bytes, G1_BYTES + G2_BYTES);
    let delta = g2_at(vk_bytes, G1_BYTES + 2 * G2_BYTES);

    let ic_slice = &vk_bytes[VK_FIXED_PREFIX_BYTES..];
    if ic_slice.len() % G1_BYTES != 0 {
        return Err(VerifierError::IcLengthMismatch {
            expected: (ic_slice.len() / G1_BYTES) * G1_BYTES,
            actual: ic_slice.len(),
        });
    }
    let ic_count = (ic_slice.len() / G1_BYTES) as u32;

    // ---- Parse proof -------------------------------------------------------
    if proof_bytes.len() != PROOF_BYTES {
        return Err(VerifierError::ProofLength {
            expected: PROOF_BYTES,
            actual: proof_bytes.len(),
        });
    }
    // `proof.A` is pre-negated by the exporter, so it feeds the pairing as-is.
    let proof_a = g1_at(proof_bytes, 0);
    let proof_b = g2_at(proof_bytes, G1_BYTES);
    let proof_c = g1_at(proof_bytes, G1_BYTES + G2_BYTES);

    // ---- Parse public inputs ----------------------------------------------
    if public_inputs.len() % FR_BYTES != 0 {
        return Err(VerifierError::PublicInputsLength {
            fr: FR_BYTES,
            expected: (public_inputs.len() / FR_BYTES) * FR_BYTES,
            actual: public_inputs.len(),
        });
    }
    let num_inputs = (public_inputs.len() / FR_BYTES) as u32;
    if ic_count != num_inputs + 1 {
        return Err(VerifierError::InputArityMismatch {
            ic_count,
            expected_inputs: ic_count.saturating_sub(1),
            actual_inputs: num_inputs,
        });
    }

    // ---- Compute vk_x = ic[0] + Σ inputs[i] · ic[i+1] ----------------------
    let mut acc = g1_at(ic_slice, 0);
    for i in 0..num_inputs as usize {
        let ic_i = g1_at(ic_slice, (i + 1) * G1_BYTES);
        let mut scalar = [0u8; FR_BYTES];
        scalar.copy_from_slice(&public_inputs[i * FR_BYTES..(i + 1) * FR_BYTES]);
        if !scalar_is_canonical(&scalar) {
            return Err(VerifierError::NonCanonicalPublicInput { index: i as u32 });
        }
        let term = (ic_i * scalar)?;
        acc = (acc + term)?;
    }

    // ---- Pairing check -----------------------------------------------------
    groth16_pairing_check(proof_a, proof_b, alpha, beta, acc, gamma, proof_c, delta)
}

/// The final Groth16 pairing check, shared by the byte-slice
/// [`verify_groth16`] and the typed [`Verifier`](crate::Verifier)
/// path:
///
/// ```text
/// e(-A, B) · e(α, β) · e(vk_x, γ) · e(C, δ) == 1
/// ```
///
/// `a` is the *already-negated* proof A (the exporter pre-negates it).
// Eight operands = the four pairing pairs; grouping them into structs would
// obscure the equation, not clarify it.
#[allow(clippy::too_many_arguments)]
pub(crate) fn groth16_pairing_check(
    a: G1Point,
    b: G2Point,
    alpha: G1Point,
    beta: G2Point,
    vk_x: G1Point,
    gamma: G2Point,
    c: G1Point,
    delta: G2Point,
) -> Result<bool, VerifierError> {
    let result = pairing(&[(a, b), (alpha, beta), (vk_x, gamma), (c, delta)])?;
    // The pairing scalar is a 32-byte LE u256: identity in GT iff it equals 1.
    Ok(result[0] == 1 && result[1..].iter().all(|b| *b == 0))
}

/// Verify a proof against a *pre-baked* VK with a compact instruction
/// data layout: `proof_bytes (256 B) || public_inputs (N × 32 B)`. The
/// generated per-circuit verifier crate uses this so the VK is embedded in
/// program code, not transmitted with every call.
pub fn verify_proof_only(vk_bytes: &[u8], instruction_data: &[u8]) -> Result<bool, VerifierError> {
    if instruction_data.len() < PROOF_BYTES {
        return Err(VerifierError::ProofLength {
            expected: PROOF_BYTES,
            actual: instruction_data.len(),
        });
    }
    let (proof, public_inputs) = instruction_data.split_at(PROOF_BYTES);
    verify_groth16(vk_bytes, proof, public_inputs)
}

/// Strict variant of [`verify_groth16`]: additionally rejects any VK or proof
/// coordinate whose 32-byte LE encoding is non-canonical (`>= q`, e.g. an
/// unused top bit set) with [`VerifierError::NonCanonicalCoordinate`].
///
/// The `alt_bn128` syscall **masks** those bits, so a plain [`verify_groth16`]
/// accepts byte-distinct encodings of the same point — i.e. a third party can
/// mutate a valid proof's bytes and it still verifies. Use this when the
/// *exact bytes* must be canonical: when a proof's bytes are hashed, signed, or
/// used as a replay/dedup key. (Public inputs are `Fr` and are already rejected
/// when non-canonical by both variants — see [`VerifierError::NonCanonicalPublicInput`].)
pub fn verify_groth16_strict(
    vk_bytes: &[u8],
    proof_bytes: &[u8],
    public_inputs: &[u8],
) -> Result<bool, VerifierError> {
    if !coords_canonical(vk_bytes) || !coords_canonical(proof_bytes) {
        return Err(VerifierError::NonCanonicalCoordinate);
    }
    verify_groth16(vk_bytes, proof_bytes, public_inputs)
}

/// Strict variant of [`verify_proof_only`]; see [`verify_groth16_strict`] for
/// what "strict" rejects and why.
pub fn verify_proof_only_strict(
    vk_bytes: &[u8],
    instruction_data: &[u8],
) -> Result<bool, VerifierError> {
    if instruction_data.len() < PROOF_BYTES {
        return Err(VerifierError::ProofLength {
            expected: PROOF_BYTES,
            actual: instruction_data.len(),
        });
    }
    let (proof, public_inputs) = instruction_data.split_at(PROOF_BYTES);
    verify_groth16_strict(vk_bytes, proof, public_inputs)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `scalar_is_canonical` boundary behaviour: `0` and `r-1` are canonical,
    /// `r` and `2^256-1` are not. (Fixture-backed verification tests live in
    /// the `xark-verifier-tests` crate, which embeds the committed circuits.)
    #[test]
    fn scalar_canonicity_boundaries() {
        assert!(scalar_is_canonical(&[0u8; FR_BYTES]), "0 is canonical");
        let mut r_minus_1 = FR_MODULUS_LE;
        r_minus_1[0] -= 1; // r ends in 0x01 (LE byte 0), so r-1 is borrow-free
        assert!(
            scalar_is_canonical(&r_minus_1),
            "r-1 is the max canonical value"
        );
        assert!(
            !scalar_is_canonical(&FR_MODULUS_LE),
            "r itself is non-canonical"
        );
        assert!(
            !scalar_is_canonical(&[0xFF; FR_BYTES]),
            "2^256-1 is non-canonical"
        );
    }

    /// `fq_is_canonical` boundary behaviour: `0` and `q-1` are canonical; `q`
    /// itself, an unused-top-bit-set encoding, and `2^256-1` are not.
    #[test]
    fn fq_canonicity_boundaries() {
        assert!(fq_is_canonical(&[0u8; FR_BYTES]), "0 is canonical");
        let mut q_minus_1 = FQ_MODULUS_LE;
        q_minus_1[0] -= 1; // q ends in 0x47 (LE byte 0), so q-1 is borrow-free
        assert!(
            fq_is_canonical(&q_minus_1),
            "q-1 is the max canonical value"
        );
        assert!(
            !fq_is_canonical(&FQ_MODULUS_LE),
            "q itself is non-canonical"
        );
        assert!(
            !fq_is_canonical(&[0xFF; FR_BYTES]),
            "2^256-1 is non-canonical"
        );

        // The malleability bit: take a valid small coordinate and set bit 255
        // (the top unused flag bit). The value jumps to ~2^255 > q, so it must
        // be rejected even though the syscall would mask the bit back off.
        let mut flagged = [0u8; FR_BYTES];
        flagged[0] = 0x21;
        assert!(fq_is_canonical(&flagged), "0x21 is canonical");
        flagged[FR_BYTES - 1] |= 0x80; // set bit 255
        assert!(
            !fq_is_canonical(&flagged),
            "an encoding with the top flag bit set is non-canonical"
        );
    }

    /// `coords_canonical` walks every 32-byte chunk and rejects on the first
    /// non-canonical one; it ignores a trailing partial chunk.
    #[test]
    fn coords_canonical_scans_all_chunks() {
        let mut buf = [0u8; 3 * FR_BYTES]; // three canonical (zero) coordinates
        assert!(coords_canonical(&buf));
        buf[2 * FR_BYTES + (FR_BYTES - 1)] = 0xFF; // make the 3rd chunk >= q
        assert!(!coords_canonical(&buf));
    }
}
