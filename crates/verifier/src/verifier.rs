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

// -- curve-op wrappers (Kani stub seam) ---------------------------------------
//
// Thin `#[inline(always)]` wrappers around the BN254 backend's `Mul` / `Add`
// / `pairing` calls. Production code is identical post-inlining (LLVM erases
// the wrappers), but they give Kani a stable, nominal function path to swap
// via `#[kani::stub(super::g1_scalar_mul, …)]`. Without them, stubbing the
// trait-method / const-generic callsites is awkward.

#[inline(always)]
fn g1_scalar_mul(p: G1Point, s: &[u8; FR_BYTES]) -> Result<G1Point, AltBn128Error> {
    p * *s
}

#[inline(always)]
fn g1_add(a: G1Point, b: G1Point) -> Result<G1Point, AltBn128Error> {
    a + b
}

#[inline(always)]
fn g16_pairing(pairs: &[(G1Point, G2Point); 4]) -> Result<[u8; 32], AltBn128Error> {
    pairing(pairs)
}

/// Pure assembly of the Groth16 final-check operand array, in the canonical
/// order `[(−A, B), (α, β), (vk_x, γ), (C, δ)]`. Split out so a Kani harness
/// can verify the *order* (operand-assembly rewrite check) by inspecting the
/// assembled array directly, without needing to stub the pairing itself.
///
/// `a` is the *already-negated* proof A (the exporter pre-negates).
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn g16_assemble_pairs(
    a: G1Point,
    b: G2Point,
    alpha: G1Point,
    beta: G2Point,
    vk_x: G1Point,
    gamma: G2Point,
    c: G1Point,
    delta: G2Point,
) -> [(G1Point, G2Point); 4] {
    [(a, b), (alpha, beta), (vk_x, gamma), (c, delta)]
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
        let term = g1_scalar_mul(ic_i, &scalar)?;
        acc = g1_add(acc, term)?;
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
    let pairs = g16_assemble_pairs(a, b, alpha, beta, vk_x, gamma, c, delta);
    let result = g16_pairing(&pairs)?;
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

/// Formal-verification harnesses (Kani bounded model checker). Run with
/// `cargo kani`. These discharge the canonicality lemmas over **all**
/// inputs — the all-input guarantee the finite-sample unit / fuzz tests
/// can't give. Compiled only under `cfg(kani)`, so they're inert in normal
/// builds.
#[cfg(kani)]
mod proofs {
    use super::*;

    /// Trusted reference: interpret a 32-byte LE buffer as a 256-bit integer
    /// (low/high `u128` halves) and compare. `le_lt` must agree with this for
    /// every input.
    fn u256_lt_le(a: &[u8; FR_BYTES], b: &[u8; FR_BYTES]) -> bool {
        let a_lo = u128::from_le_bytes(a[..16].try_into().unwrap());
        let a_hi = u128::from_le_bytes(a[16..].try_into().unwrap());
        let b_lo = u128::from_le_bytes(b[..16].try_into().unwrap());
        let b_hi = u128::from_le_bytes(b[16..].try_into().unwrap());
        a_hi < b_hi || (a_hi == b_hi && a_lo < b_lo)
    }

    /// `le_lt` is a correct unsigned 256-bit little-endian comparison for ALL
    /// inputs (and never panics — Kani checks the harness is panic-free).
    #[kani::proof]
    fn le_lt_is_correct_u256_compare() {
        let a: [u8; FR_BYTES] = kani::any();
        let m: [u8; FR_BYTES] = kani::any();
        assert_eq!(le_lt(&a, &m), u256_lt_le(&a, &m));
    }

    /// `scalar_is_canonical(s) ⇔ s < r`, for ALL `s` — the public-input
    /// canonicality property.
    #[kani::proof]
    fn scalar_is_canonical_iff_lt_r() {
        let s: [u8; FR_BYTES] = kani::any();
        assert_eq!(scalar_is_canonical(&s), u256_lt_le(&s, &FR_MODULUS_LE));
    }

    /// `fq_is_canonical(c) ⇔ c < q`, for ALL `c` — the coordinate canonicality
    /// property behind non-malleability: any encoding with an unused top bit set
    /// is `>= q`, hence rejected by the `*_strict` path.
    #[kani::proof]
    fn fq_is_canonical_iff_lt_q() {
        let c: [u8; FR_BYTES] = kani::any();
        assert_eq!(fq_is_canonical(&c), u256_lt_le(&c, &FQ_MODULUS_LE));
    }

    /// `coords_canonical` is the conjunction of the per-coordinate check, for ALL
    /// inputs. Bounded to two 32-byte chunks; the loop body is identical for any
    /// length, so two chunks exercise both the "rejects on a bad chunk" and
    /// "accepts when all good" paths.
    #[kani::proof]
    fn coords_canonical_is_conjunction() {
        let buf: [u8; 2 * FR_BYTES] = kani::any();
        let c0: [u8; FR_BYTES] = buf[..FR_BYTES].try_into().unwrap();
        let c1: [u8; FR_BYTES] = buf[FR_BYTES..].try_into().unwrap();
        assert_eq!(
            coords_canonical(&buf),
            fq_is_canonical(&c0) && fq_is_canonical(&c1)
        );
    }

    // -------------------------------------------------------------------------
    // Fail-closed, strict non-malleability, arity.
    //
    // These harnesses exercise the parse path of `verify_groth16` /
    // `verify_groth16_strict` and rely on the fact that every structural error
    // path early-exits *before* any `alt_bn128` curve operation runs. That lets
    // us prove them without stubbing the BN254 backend: the curve ops are
    // unreachable on the error paths these harnesses cover.
    //
    // Totality over the *full* `verify_groth16` body (i.e. proving
    // no panic for an *accepted* input — where the curve ops *do* run) is
    // discharged separately by the `verify_groth16_totality_n{0,1,2}` and
    // `totality_verify_groth16` / `totality_verify_proof_only` harnesses
    // below, which stub `g1_scalar_mul` / `g1_add` / `g16_pairing` so Kani
    // doesn't have to symbolically execute the BN254 pairing/scalar-mul.
    //
    // All harnesses bound `N` (= public-input count) to a small concrete value
    // so Kani's enumeration stays tractable. The verifier code is uniform in
    // `N`, so each bounded harness witnesses the general property.
    // -------------------------------------------------------------------------

    /// **Fail-closed: a `proof_bytes` length other than 256 always returns
    /// `Err(ProofLength)`.** Curve ops are not reached because the parse path
    /// errors out before the IC scan. (`vk_bytes` is chosen large enough that
    /// the `TruncatedVk` check does not fire first, so the failure is forced
    /// onto the `ProofLength` path.)
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn proof_wrong_length_rejected() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES] = kani::any();
        let proof: [u8; 100] = kani::any(); // != PROOF_BYTES (256)
        let pi: [u8; FR_BYTES] = kani::any();
        let r = verify_groth16(&vk, &proof, &pi);
        assert!(matches!(r, Err(VerifierError::ProofLength { .. })));
    }

    /// **Fail-closed: a `vk_bytes` shorter than the fixed prefix + one IC point
    /// always returns `Err(TruncatedVk)`.** The function returns at the first
    /// length guard, before any byte decode.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn vk_truncated_rejected() {
        // Exactly one byte short of the minimum.
        let vk: [u8; VK_FIXED_PREFIX_BYTES + G1_BYTES - 1] = kani::any();
        let proof: [u8; PROOF_BYTES] = kani::any();
        let pi: [u8; FR_BYTES] = kani::any();
        let r = verify_groth16(&vk, &proof, &pi);
        assert!(matches!(r, Err(VerifierError::TruncatedVk { .. })));
    }

    /// **Fail-closed: a `vk_bytes` whose IC region is not a whole number of
    /// 64-byte G1 points always returns `Err(IcLengthMismatch)`.** Bounded to
    /// `VK_FIXED_PREFIX_BYTES + G1_BYTES + 1` (one byte past two complete IC
    /// points → the IC slice has length `65`, not a multiple of `G1_BYTES`).
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn vk_ic_unaligned_rejected() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + G1_BYTES + 1] = kani::any();
        let proof: [u8; PROOF_BYTES] = kani::any();
        let pi: [u8; FR_BYTES] = kani::any();
        let r = verify_groth16(&vk, &proof, &pi);
        assert!(matches!(r, Err(VerifierError::IcLengthMismatch { .. })));
    }

    /// **Fail-closed: a `public_inputs` length that is not a multiple of 32
    /// always returns `Err(PublicInputsLength)`.** vk and proof are chosen
    /// valid in shape so the failure is forced onto the PI-length path.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn pi_unaligned_rejected() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES] = kani::any();
        let proof: [u8; PROOF_BYTES] = kani::any();
        let pi: [u8; FR_BYTES + 1] = kani::any(); // 33 B, not a multiple of 32
        let r = verify_groth16(&vk, &proof, &pi);
        assert!(matches!(r, Err(VerifierError::PublicInputsLength { .. })));
    }

    /// **Arity / fail-closed: `ic_count - 1 != num_inputs` always returns
    /// `Err(InputArityMismatch)`.** Here vk encodes `ic_count = 2`
    /// (`VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES`), so the verifier expects exactly
    /// `1` public input; we hand it `0` instead.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn arity_mismatch_rejected_ic2_pi0() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES] = kani::any();
        let proof: [u8; PROOF_BYTES] = kani::any();
        let pi: [u8; 0] = []; // 0 inputs, but vk expects 1
        let r = verify_groth16(&vk, &proof, &pi);
        assert!(matches!(r, Err(VerifierError::InputArityMismatch { .. })));
    }

    /// **Arity / fail-closed: same as above with `ic_count = 2, num_inputs = 2`
    /// (one too many).** Together with the previous harness this exhausts the
    /// off-by-one neighbourhood of the accepted arity at `N = 1`.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn arity_mismatch_rejected_ic2_pi2() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES] = kani::any();
        let proof: [u8; PROOF_BYTES] = kani::any();
        let pi: [u8; 2 * FR_BYTES] = kani::any(); // 2 inputs, but vk expects 1
        let r = verify_groth16(&vk, &proof, &pi);
        assert!(matches!(r, Err(VerifierError::InputArityMismatch { .. })));
    }

    /// **Fail-closed: a non-canonical public-input scalar (`>= r`) always
    /// returns `Err(NonCanonicalPublicInput)`.** vk/proof are valid in shape
    /// and arity. The IC point reads via `g1_at` are pure byte copies (no
    /// panic, no curve op); the failure fires on the `scalar_is_canonical`
    /// check before the curve mul.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn noncanonical_pi_rejected() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES] = kani::any();
        let proof: [u8; PROOF_BYTES] = kani::any();
        let mut pi: [u8; FR_BYTES] = kani::any();
        // Force pi >= r by saturating the top limb. Combined with `>= r`,
        // setting the top byte to 0xFF makes the value > r for sure
        // (r's top byte is 0x30).
        pi[FR_BYTES - 1] = 0xFF;
        let r = verify_groth16(&vk, &proof, &pi);
        assert!(matches!(
            r,
            Err(VerifierError::NonCanonicalPublicInput { .. })
        ));
    }

    /// **Strict non-malleability (#4): `verify_groth16_strict` rejects any
    /// `vk_bytes` with a non-canonical `Fq` coordinate.** Here we set the top
    /// (unused-flag) bit of byte 31 of `vk_bytes[0..32]` (the first coordinate
    /// of `alpha`). The resulting 32-byte value is `>= 2^255 > q`, hence
    /// non-canonical, and the strict path must reject with
    /// `Err(NonCanonicalCoordinate)`. Note that the non-strict path *would*
    /// silently accept this (the syscall masks the bit) — that is the
    /// malleability path the strict variant exists to close.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn strict_rejects_top_bit_set_in_vk() {
        let mut vk: [u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES] = kani::any();
        // Set bit 255 of the first 32-byte coordinate (alpha.x).
        vk[FR_BYTES - 1] |= 0x80;
        let proof: [u8; PROOF_BYTES] = kani::any();
        let pi: [u8; FR_BYTES] = kani::any();
        let r = verify_groth16_strict(&vk, &proof, &pi);
        assert!(matches!(r, Err(VerifierError::NonCanonicalCoordinate)));
    }

    /// **Strict non-malleability (#4): same, but the top bit is set inside
    /// `proof_bytes`.** Targets `proof.A.x` (the first 32 bytes of the proof);
    /// the strict path must reject before any curve op runs.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn strict_rejects_top_bit_set_in_proof() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES] = kani::any();
        let mut proof: [u8; PROOF_BYTES] = kani::any();
        proof[FR_BYTES - 1] |= 0x80; // top bit of proof.A.x
        let pi: [u8; FR_BYTES] = kani::any();
        let r = verify_groth16_strict(&vk, &proof, &pi);
        assert!(matches!(r, Err(VerifierError::NonCanonicalCoordinate)));
    }

    /// **`verify_proof_only` shares the same structural-error contract as
    /// `verify_groth16`.** Specifically, a too-short `instruction_data`
    /// (less than `PROOF_BYTES`) must return `Err(ProofLength)`.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn proof_only_too_short_rejected() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + G1_BYTES] = kani::any();
        let data: [u8; PROOF_BYTES - 1] = kani::any();
        let r = verify_proof_only(&vk, &data);
        assert!(matches!(r, Err(VerifierError::ProofLength { .. })));
    }

    // -------------------------------------------------------------------------
    // Totality (no panic) over the FULL verify_groth16 body,
    // including the curve ops, with kani::stub replacing the BN254 operators.
    //
    // The curve ops (G1Point::Mul, G1Point::Add, pairing) resolve to the
    // alt_bn128 syscall on-chain and the Arkworks fallback off-chain — neither
    // is symbolically executable inside Kani's budget. The harnesses route
    // every call site through three #[inline(always)] wrappers
    // (g1_scalar_mul, g1_add, g16_pairing, defined above) and swap them out
    // with kani::stub replacements that return unconstrained
    // Result<_, AltBn128Error>. Production codegen is byte-identical.
    //
    // What this proves: panic freedom of the Rust around the curve ops on any
    // backend behaviour. What it does NOT prove: anything about the *value* of
    // the boolean return (Layer C — Groth16 soundness — out of scope), nor
    // that successful curve ops produce on-curve points (orthogonal to panic
    // freedom).
    //
    // N (= public-input count) is bounded to {0, 1, 2}. The body is uniform
    // in N (the only N-dependent path is the IC accumulator loop, whose body
    // is identical per iteration), so the three values witness {empty,
    // single-iter, multi-iter} loop patterns.
    // -------------------------------------------------------------------------

    /// Stub replacement for `g1_scalar_mul`. Returns an unconstrained Result:
    /// either an arbitrary-bytes G1 point or a backend error. Kani then
    /// explores both branches of the `?` operator at every call site.
    fn stub_g1_scalar_mul(_p: G1Point, _s: &[u8; FR_BYTES]) -> Result<G1Point, AltBn128Error> {
        if kani::any() {
            let bytes: [u8; G1_BYTES] = kani::any();
            Ok(G1Point(bytes))
        } else {
            Err(AltBn128Error::GroupError)
        }
    }

    fn stub_g1_add(_a: G1Point, _b: G1Point) -> Result<G1Point, AltBn128Error> {
        if kani::any() {
            let bytes: [u8; G1_BYTES] = kani::any();
            Ok(G1Point(bytes))
        } else {
            Err(AltBn128Error::GroupError)
        }
    }

    fn stub_g16_pairing(_pairs: &[(G1Point, G2Point); 4]) -> Result<[u8; 32], AltBn128Error> {
        if kani::any() {
            let bytes: [u8; 32] = kani::any();
            Ok(bytes)
        } else {
            Err(AltBn128Error::GroupError)
        }
    }

    /// Totality (no panic) for `verify_groth16` with N = 0 public inputs.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn verify_groth16_totality_n0() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + G1_BYTES] = kani::any();
        let proof: [u8; PROOF_BYTES] = kani::any();
        let pi: [u8; 0] = [];
        let _ = verify_groth16(&vk, &proof, &pi);
    }

    /// Totality for `verify_groth16` with N = 1 (one loop iter).
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn verify_groth16_totality_n1() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES] = kani::any();
        let proof: [u8; PROOF_BYTES] = kani::any();
        let pi: [u8; FR_BYTES] = kani::any();
        let _ = verify_groth16(&vk, &proof, &pi);
    }

    /// Totality for `verify_groth16` with N = 2 (multi-iter).
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn verify_groth16_totality_n2() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + 3 * G1_BYTES] = kani::any();
        let proof: [u8; PROOF_BYTES] = kani::any();
        let pi: [u8; 2 * FR_BYTES] = kani::any();
        let _ = verify_groth16(&vk, &proof, &pi);
    }

    /// Totality for `verify_groth16_strict` with N = 0. Adds the
    /// `coords_canonical` scan over vk + proof bytes.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn verify_groth16_strict_totality_n0() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + G1_BYTES] = kani::any();
        let proof: [u8; PROOF_BYTES] = kani::any();
        let pi: [u8; 0] = [];
        let _ = verify_groth16_strict(&vk, &proof, &pi);
    }

    /// Totality for `verify_groth16_strict` with N = 1.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn verify_groth16_strict_totality_n1() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES] = kani::any();
        let proof: [u8; PROOF_BYTES] = kani::any();
        let pi: [u8; FR_BYTES] = kani::any();
        let _ = verify_groth16_strict(&vk, &proof, &pi);
    }

    /// Totality for `verify_groth16_strict` with N = 2.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn verify_groth16_strict_totality_n2() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + 3 * G1_BYTES] = kani::any();
        let proof: [u8; PROOF_BYTES] = kani::any();
        let pi: [u8; 2 * FR_BYTES] = kani::any();
        let _ = verify_groth16_strict(&vk, &proof, &pi);
    }

    /// **Pairing operand-assembly order.** Proves over all
    /// symbolic inputs that `g16_assemble_pairs` produces the canonical
    /// `[(−A, B), (α, β), (vk_x, γ), (C, δ)]` order. The exporter pre-negates
    /// A, so the "−A" slot literally receives the caller's `a` argument.
    /// Discharged directly without a stub by virtue of the assembly being a
    /// pure helper.
    #[kani::proof]
    fn pairing_operand_assembly_order() {
        let a_bytes: [u8; G1_BYTES] = kani::any();
        let b_bytes: [u8; G2_BYTES] = kani::any();
        let alpha_bytes: [u8; G1_BYTES] = kani::any();
        let beta_bytes: [u8; G2_BYTES] = kani::any();
        let vk_x_bytes: [u8; G1_BYTES] = kani::any();
        let gamma_bytes: [u8; G2_BYTES] = kani::any();
        let c_bytes: [u8; G1_BYTES] = kani::any();
        let delta_bytes: [u8; G2_BYTES] = kani::any();

        let a = G1Point(a_bytes);
        let b = G2Point(b_bytes);
        let alpha = G1Point(alpha_bytes);
        let beta = G2Point(beta_bytes);
        let vk_x = G1Point(vk_x_bytes);
        let gamma = G2Point(gamma_bytes);
        let c = G1Point(c_bytes);
        let delta = G2Point(delta_bytes);

        let pairs = g16_assemble_pairs(a, b, alpha, beta, vk_x, gamma, c, delta);

        assert!(pairs[0].0.0 == a_bytes && pairs[0].1.0 == b_bytes);
        assert!(pairs[1].0.0 == alpha_bytes && pairs[1].1.0 == beta_bytes);
        assert!(pairs[2].0.0 == vk_x_bytes && pairs[2].1.0 == gamma_bytes);
        assert!(pairs[3].0.0 == c_bytes && pairs[3].1.0 == delta_bytes);
    }

    // -------------------------------------------------------------------------
    // Named aliases for totality and operand assembly.
    //
    // The N-parameterised totality harnesses above (verify_groth16_totality_n0/
    // n1/n2 and the strict variants) discharge totality for verify_groth16
    // and verify_groth16_strict. The three harnesses below provide the
    // single-entry-point names:
    //
    //   * totality_verify_groth16     — totality of the public verify_groth16
    //                                   entry point on accepted-input shape.
    //   * totality_verify_proof_only  — totality of verify_proof_only's split
    //                                   wrapper plus its downstream verify_groth16.
    //   * pairing_operand_assembly    — byte-level concatenation check that the
    //                                   buffer presented to the alt_bn128_pairing
    //                                   syscall equals
    //                                   neg(A) || B || α || β || vk_x || γ || C || δ.
    //
    // All three use the same g1_scalar_mul / g1_add / g16_pairing stubs as the
    // N-parameterised totality block above.
    // -------------------------------------------------------------------------

    /// **Totality of `verify_groth16` over an accepted-input
    /// shape.** The vk/proof/public-inputs are unconstrained 8-bit-symbolic
    /// arrays, sized so the structural checks accept them; the curve-op
    /// wrappers are stubbed so the harness exercises the *post-canonicality*
    /// path that reaches `g1_scalar_mul`, `g1_add`, and `g16_pairing`. Proves
    /// no panic / no OOB / no overflow over the full body.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn totality_verify_groth16() {
        // ic_count = 2  ⇒  expects exactly 1 public input. Both branches of
        // the IC accumulator loop's `?` (Ok / Err) are explored via the stubs.
        let vk: [u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES] = kani::any();
        let proof: [u8; PROOF_BYTES] = kani::any();
        let pi: [u8; FR_BYTES] = kani::any();
        let _ = verify_groth16(&vk, &proof, &pi);
    }

    /// **Totality of `verify_proof_only`.** Covers the split
    /// wrapper that peels off `PROOF_BYTES` from a single `instruction_data`
    /// blob, then delegates to `verify_groth16`. Same stubbing as
    /// `totality_verify_groth16`.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing, stub_g16_pairing)]
    fn totality_verify_proof_only() {
        // ic_count = 2  ⇒  expects exactly 1 public input  ⇒  instruction_data
        // is exactly `PROOF_BYTES + FR_BYTES` long.
        let vk: [u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES] = kani::any();
        let instr: [u8; PROOF_BYTES + FR_BYTES] = kani::any();
        let _ = verify_proof_only(&vk, &instr);
    }

    /// **Operand-assembly rewrite check.** The pairing syscall takes a
    /// contiguous `[G1 || G2]`-per-pair byte buffer (see the on-chain branch of
    /// `solana_nostd_alt_bn128::pairing`). This harness proves that the byte
    /// concatenation of the `g16_assemble_pairs` result equals the canonical
    /// `neg(A) || B || α || β || vk_x || γ || C || δ` — i.e. the algebraic
    /// equation `e(−A,B)·e(α,β)·e(vk_x,γ)·e(C,δ) = 1` is what the assembled
    /// operand list literally encodes. `a` is the already-negated proof A
    /// (the exporter pre-negates), so the "neg(A)" slot is `a` itself.
    #[kani::proof]
    fn pairing_operand_assembly() {
        let a_bytes: [u8; G1_BYTES] = kani::any();
        let b_bytes: [u8; G2_BYTES] = kani::any();
        let alpha_bytes: [u8; G1_BYTES] = kani::any();
        let beta_bytes: [u8; G2_BYTES] = kani::any();
        let vk_x_bytes: [u8; G1_BYTES] = kani::any();
        let gamma_bytes: [u8; G2_BYTES] = kani::any();
        let c_bytes: [u8; G1_BYTES] = kani::any();
        let delta_bytes: [u8; G2_BYTES] = kani::any();

        let pairs = g16_assemble_pairs(
            G1Point(a_bytes),
            G2Point(b_bytes),
            G1Point(alpha_bytes),
            G2Point(beta_bytes),
            G1Point(vk_x_bytes),
            G2Point(gamma_bytes),
            G1Point(c_bytes),
            G2Point(delta_bytes),
        );

        // Flatten exactly as `solana_nostd_alt_bn128::pairing` does on-chain:
        // a contiguous `[[u8; PAIRING_PAIR_BYTES]; 4]` of `G1 || G2` per pair.
        // This is the byte buffer the `alt_bn128` syscall actually receives.
        let mut buffer = [[0u8; PAIRING_PAIR_BYTES]; 4];
        for (slot, (g1, g2)) in buffer.iter_mut().zip(pairs.iter()) {
            slot[..G1_BYTES].copy_from_slice(&g1.0);
            slot[G1_BYTES..].copy_from_slice(&g2.0);
        }

        // Canonical expected layout: neg(A) || B || α || β || vk_x || γ || C || δ.
        // (`a_bytes` is the pre-negated proof A; see the doc comment above.)
        let mut expected = [0u8; 4 * PAIRING_PAIR_BYTES];
        let mut off = 0;
        let mut put_g1 =
            |dst: &mut [u8; 4 * PAIRING_PAIR_BYTES], off: &mut usize, src: &[u8; G1_BYTES]| {
                dst[*off..*off + G1_BYTES].copy_from_slice(src);
                *off += G1_BYTES;
            };
        let mut put_g2 =
            |dst: &mut [u8; 4 * PAIRING_PAIR_BYTES], off: &mut usize, src: &[u8; G2_BYTES]| {
                dst[*off..*off + G2_BYTES].copy_from_slice(src);
                *off += G2_BYTES;
            };
        put_g1(&mut expected, &mut off, &a_bytes);
        put_g2(&mut expected, &mut off, &b_bytes);
        put_g1(&mut expected, &mut off, &alpha_bytes);
        put_g2(&mut expected, &mut off, &beta_bytes);
        put_g1(&mut expected, &mut off, &vk_x_bytes);
        put_g2(&mut expected, &mut off, &gamma_bytes);
        put_g1(&mut expected, &mut off, &c_bytes);
        put_g2(&mut expected, &mut off, &delta_bytes);
        assert!(off == 4 * PAIRING_PAIR_BYTES);

        // Flatten the per-pair buffer for a single byte-equality check.
        let mut flat = [0u8; 4 * PAIRING_PAIR_BYTES];
        for (i, slot) in buffer.iter().enumerate() {
            flat[i * PAIRING_PAIR_BYTES..(i + 1) * PAIRING_PAIR_BYTES].copy_from_slice(slot);
        }
        assert!(flat == expected);
    }
}
