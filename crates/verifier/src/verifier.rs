//! Groth16 BN254 verifier core (little-endian wire format).
//!
//! # Wire format
//!
//! LE end-to-end: every `Fq`/`Fr` element is a 32-byte little-endian limb, so
//! bytes go straight to the Solana `alt_bn128` group-op syscall (LE variant,
//! `0x80` flag) without conversion. Curve arithmetic is delegated to
//! [`solana_nostd_alt_bn128`].
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
//! * `proof.A` is pre-negated by the exporter to avoid a modular subtraction
//!   inside the syscall path.
//!
//! # Public-input linear combination
//!
//! `vk_x = ic[0] + Σ inputs[i] · ic[i+1]`, via the G1 mul + add syscalls.
//! Final pairing check:
//!
//! ```text
//! e(-A, B) · e(α, β) · e(vk_x, γ) · e(C, δ) == 1
//! ```
//!
//! evaluated as a single multi-pair call (4 × 192 = 768 input bytes).
//!
//! # BN254 backend
//!
//! [`solana_nostd_alt_bn128`]'s `G1Point`/`G2Point` operators and [`pairing`]
//! resolve to the `alt_bn128` syscalls on `target_os = "solana"` and to an
//! Arkworks reference off-chain, so the same [`verify_groth16`] runs unchanged
//! in host tests and on-chain; only `core` is linked into the SBF build.

use solana_nostd_alt_bn128::{AltBn128Error, G1Point, G2Point, pairing, pairing_bytes};
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

/// BN254 scalar field order `r`, little-endian (`0x30644e72…f0000001`).
/// Public-input scalars must be *canonical* — strictly less than `r`.
///
/// Without this check `v`, `v + r`, `v + 2r`, … all reduce to the same field
/// element and verify against the same proof, so a caller could present one
/// proof under several distinct 32-byte public-input values. A program reading
/// a public input as an integer (nullifier, amount, root, …) would then see a
/// different value than the proof attests to. Reject non-canonical inputs up
/// front.
const FR_MODULUS_LE: [u8; FR_BYTES] = [
    0x01, 0x00, 0x00, 0xf0, 0x93, 0xf5, 0xe1, 0x43, 0x91, 0x70, 0xb9, 0x79, 0x48, 0xe8, 0x33, 0x28,
    0x5d, 0x58, 0x81, 0x81, 0xb6, 0x45, 0x50, 0xb8, 0x29, 0xa0, 0x31, 0xe1, 0x72, 0x4e, 0x64, 0x30,
];

/// BN254 base field order `q`, little-endian (`0x30644e72…d87cfd47`). Every
/// G1/G2 coordinate is an `Fq` element; a *canonical* encoding is `< q`, which
/// also forces the two unused top bits of the 32-byte limb to zero.
///
/// The `alt_bn128` syscall (and its Arkworks host reference) **mask** those top
/// bits when decoding, so without an explicit check `c`, `c + q`, … and any
/// value with the unused top bits flipped all decode to the *same* point and
/// verify against the same proof — proof/VK encoding malleability, where a
/// third party mangles a valid proof's bytes and it still verifies. The
/// `*_strict` entry points reject it (encoding only: proofs stay re-randomizable).
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
/// coordinates (a G1/G2 point or a whole VK/proof blob). A trailing partial
/// chunk (a malformed non-multiple-of-32 length) is ignored here and caught by
/// the structural checks in [`verify_groth16`].
pub(crate) fn coords_canonical(bytes: &[u8]) -> bool {
    let mut c = [0u8; FR_BYTES];
    for chunk in bytes.as_chunks::<FR_BYTES>().0 {
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
    /// A batch for [`verify_groth16_batch`] is empty, or not a whole number of
    /// `proof || public_inputs` entries of `entry` bytes each.
    BatchLength { entry: usize, actual: usize },
    /// The `scratch` given to [`verify_groth16_batch`] holds fewer than `M + 3`
    /// pairing operands for a batch of `M` proofs.
    ScratchTooSmall { expected: usize, actual: usize },
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
            VerifierError::BatchLength { entry, actual } => write!(
                f,
                "batch must be one or more {entry}-byte proof || public_inputs entries; got {actual} B"
            ),
            VerifierError::ScratchTooSmall { expected, actual } => write!(
                f,
                "batch scratch must hold at least {expected} pairing operands; got {actual}"
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
// Thin `#[inline(always)]` wrappers around the BN254 backend's `Mul`/`Add`/
// `pairing`. LLVM erases them post-inlining (production codegen is identical),
// but they give Kani a stable nominal path to swap via `#[kani::stub(...)]`;
// stubbing the trait-method / const-generic callsites directly is awkward.

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

// -- small-scalar fast path ---------------------------------------------------
//
// The `alt_bn128` syscalls are fixed-price: the runtime charges the same for
// `1 · P` as for a full 254-bit scalar mul. Measured all-in (mollusk-svm,
// sbpf v3, LE syscalls, `overflow-checks` + `lto = "fat"`), five inputs:
//
// ```text
// g1_add          539 CU
// g1_scalar_mul 4,016 CU     -> one mul is worth 7.45 adds
// ```
//
// Three scalars are therefore overpaying, and each substitution below is a
// group identity rather than an approximation:
//
// ```text
// k == 0   0·P is the identity and acc + identity == acc   -> skip both ops
// k == 1   1·P == P                                        -> skip the mul
// k small  double-and-add costs (add_count(k) + 1) adds    -> skip the mul
// ```
//
// A Rust-derived circuit hits this constantly: `bool` flags, enum
// discriminants, loop counts and array indices all reach the verifier as
// public inputs equal to 0, 1, or a single digit.

/// Largest number of group additions the double-and-add substitution may spend
/// before the mul syscall becomes the cheaper option.
///
/// One mul-path input costs `g1_scalar_mul + g1_add`; one addition-path input
/// costs `add_count(k) + 1` `g1_add`s. Measured over five inputs, against
/// 22,773 CU for the mul path:
///
/// ```text
/// add_count = 7  (k = 128)   20,780 CU   -> win by 1,993
/// add_count = 8  (k = 192)   23,165 CU   -> loss by 392
/// ```
const MAX_ADDS: u32 = 7;

/// Largest scalar the fast path accepts.
///
/// `add_count(k) >= msb(k)`, so `add_count(k) <= MAX_ADDS` already implies
/// `k <= 2^MAX_ADDS`. Naming the bound separately lets [`mul_small`] iterate
/// over a *compile-time* number of bit positions, which keeps the loop
/// statically bounded for Kani's unwinding.
const MAX_SMALL_SCALAR: u64 = 1 << MAX_ADDS;

/// Group additions left-to-right double-and-add needs for `k >= 1`: one
/// doubling per bit position below the MSB, plus one add per set bit below the
/// MSB. Returns `0` for `k == 0`, which the caller never passes.
#[inline(always)]
const fn add_count(k: u64) -> u32 {
    if k == 0 {
        return 0;
    }
    let msb = 63 - k.leading_zeros();
    msb + (k.count_ones() - 1)
}

/// `Some(k)` when the 32-byte LE scalar encodes exactly the integer `k`, and
/// double-and-add is cheaper for it than the mul syscall. `None` means "use
/// `g1_scalar_mul`".
///
/// The `Some` case asserts the scalar's *whole* 32 bytes are the LE encoding of
/// `k` — the fast path must never fire on a scalar that merely looks small in
/// its low limb.
#[inline(always)]
fn small_scalar(s: &[u8; FR_BYTES]) -> Option<u64> {
    // Everything at or above 2^64 is far past the break-even. Bail before the
    // limb read so the common (large-scalar) case exits after one byte.
    let mut i = 8;
    while i < FR_BYTES {
        if s[i] != 0 {
            return None;
        }
        i += 1;
    }
    let mut limb = [0u8; 8];
    limb.copy_from_slice(&s[..8]);
    let k = u64::from_le_bytes(limb);
    if k == 0 || k > MAX_SMALL_SCALAR || add_count(k) > MAX_ADDS {
        return None;
    }
    Some(k)
}

/// `k · p` by left-to-right double-and-add, for `1 <= k <= MAX_SMALL_SCALAR`.
///
/// The bit loop runs over the fixed range `MAX_ADDS-1 ..= 0` and skips
/// positions at or above the MSB, so it performs exactly `msb(k)` doublings
/// while keeping its trip count a compile-time constant.
///
/// `k >= 1` means `acc` starts at `p` and is never the identity, so the only
/// unusual operand pattern is the doubling `acc + acc`, which the `alt_bn128`
/// addition handles.
#[inline]
fn mul_small(p: G1Point, k: u64) -> Result<G1Point, AltBn128Error> {
    let msb = 63 - k.leading_zeros();
    let mut acc = p;
    let mut bit = MAX_ADDS;
    while bit > 0 {
        bit -= 1;
        if bit >= msb {
            continue; // above the MSB: contributes nothing
        }
        acc = g1_add(acc, acc)?;
        if (k >> bit) & 1 == 1 {
            acc = g1_add(acc, p)?;
        }
    }
    Ok(acc)
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
    let vk = parse_vk(vk_bytes)?;

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

    let vk_x = vk_x(vk.ic, public_inputs)?;

    // ---- Pairing check -----------------------------------------------------
    groth16_pairing_check(
        proof_a, proof_b, vk.alpha, vk.beta, vk_x, vk.gamma, proof_c, vk.delta,
    )
}

/// A VK's parts, borrowed from its wire bytes.
struct VkParts<'a> {
    alpha: G1Point,
    beta: G2Point,
    gamma: G2Point,
    delta: G2Point,
    /// The IC region: `ic_count` G1 points.
    ic: &'a [u8],
}

/// Split a VK into its parts, checking its length.
#[inline(always)]
fn parse_vk(vk_bytes: &[u8]) -> Result<VkParts<'_>, VerifierError> {
    // VK = alpha(G1) | beta(G2) | gamma(G2) | delta(G2) | (N+1) × G1 (IC).
    // The IC count is *implied by length* — there is no ic_count field on the
    // wire — so it can never disagree with the actual bytes.
    if vk_bytes.len() < VK_FIXED_PREFIX_BYTES + G1_BYTES {
        return Err(VerifierError::TruncatedVk {
            expected: VK_FIXED_PREFIX_BYTES + G1_BYTES,
            actual: vk_bytes.len(),
        });
    }
    let ic = &vk_bytes[VK_FIXED_PREFIX_BYTES..];
    if !ic.len().is_multiple_of(G1_BYTES) {
        return Err(VerifierError::IcLengthMismatch {
            expected: (ic.len() / G1_BYTES) * G1_BYTES,
            actual: ic.len(),
        });
    }
    Ok(VkParts {
        alpha: g1_at(vk_bytes, 0),
        beta: g2_at(vk_bytes, G1_BYTES),
        gamma: g2_at(vk_bytes, G1_BYTES + G2_BYTES),
        delta: g2_at(vk_bytes, G1_BYTES + 2 * G2_BYTES),
        ic,
    })
}

/// `vk_x = ic[0] + Σ inputs[i] · ic[i+1]`, after checking the inputs' length,
/// arity and canonicity. `ic` is a whole number of G1 points ([`parse_vk`]).
#[inline(always)]
fn vk_x(ic: &[u8], public_inputs: &[u8]) -> Result<G1Point, VerifierError> {
    let ic_count = (ic.len() / G1_BYTES) as u32;
    if !public_inputs.len().is_multiple_of(FR_BYTES) {
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

    let mut acc = g1_at(ic, 0);
    for i in 0..num_inputs as usize {
        let mut scalar = [0u8; FR_BYTES];
        scalar.copy_from_slice(&public_inputs[i * FR_BYTES..(i + 1) * FR_BYTES]);
        if !scalar_is_canonical(&scalar) {
            return Err(VerifierError::NonCanonicalPublicInput { index: i as u32 });
        }
        // 0 · ic[i+1] is the identity and acc + identity == acc, so the whole
        // term drops out. This also skips the mul syscall's incidental on-curve
        // check of ic[i+1] — that operand comes from the VK, which is already
        // trusted input (a caller who can choose the VK can prove anything).
        if scalar == [0u8; FR_BYTES] {
            continue;
        }
        let ic_i = g1_at(ic, (i + 1) * G1_BYTES);
        let term = match small_scalar(&scalar) {
            // k == 1 returns ic_i with no syscall at all.
            Some(k) => mul_small(ic_i, k)?,
            None => g1_scalar_mul(ic_i, &scalar)?,
        };
        acc = g1_add(acc, term)?;
    }
    Ok(acc)
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
/// mutate a valid proof's bytes and it still verifies; this rejects that. It does **not** make
/// proof bytes unique: Groth16 proofs are re-randomizable, so never use them (or their hash) as a
/// replay or dedup key; bind a nullifier, nonce or signer into the public inputs instead.
/// (Non-canonical public inputs are rejected by both variants: [`VerifierError::NonCanonicalPublicInput`].)
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

// -- batch verification -------------------------------------------------------
//
// M proofs against one VK in a single pairing call. Each proof's check
// `e(-Aᵢ, Bᵢ)·e(α, β)·e(vk_xᵢ, γ)·e(Cᵢ, δ) = 1` is raised to a weight rᵢ and the
// M checks multiplied; the shared α, β, γ, δ let the last three terms merge:
//
//   Πᵢ e(rᵢ·(-Aᵢ), Bᵢ) · e((Σrᵢ)·α, β) · e(Σ rᵢ·vk_xᵢ, γ) · e(Σ rᵢ·Cᵢ, δ) = 1
//
// M + 3 pairs instead of 4M. Without the weights, invalid proofs could be made
// to cancel each other out. With them, if proof j is invalid the batch passes only
// when rⱼ hits the one value (mod r) that cancels the rest: r₀ = 1, and each other
// rᵢ is 252 bits of SHA-256 over the domain tag, the VK (length-prefixed) and the
// whole batch,
// so they're fixed only once everything they weigh is. The weights are public, so
// a prover can grind: each new batch is a fresh try at about 2⁻²⁵² (full-width
// weights cost the same as narrow ones: a scalar mul is fixed-price).
//
// Strict, like `verify_groth16_strict`: one encoding per point.

/// Domain tag for the batch weights' hash.
const BATCH_DOMAIN: &[u8] = b"xark-groth16-batch-v1";

/// SHA-256 of the concatenated `vals` (the `sol_sha256` syscall on-chain).
#[inline(always)]
fn batch_hash(vals: &[&[u8]]) -> [u8; 32] {
    solana_sha256_hasher::hashv(vals).to_bytes()
}

#[inline(always)]
fn g16_pairing_bytes(input: &[u8]) -> Result<[u8; 32], AltBn128Error> {
    pairing_bytes(input)
}

/// Weight `rᵢ` (`i ≥ 1`): `SHA-256(seed || i)` as a 32-byte LE scalar in
/// `[2²⁵², 2²⁵³)`: bits 253..255 cleared and bit 252 set, so it's never 0 and
/// canonical (`2²⁵³ < r`), with 252 bits from the hash.
#[inline(always)]
fn batch_weight(seed: &[u8; 32], i: u64) -> [u8; FR_BYTES] {
    let mut r = batch_hash(&[seed, &i.to_le_bytes()]);
    r[31] = (r[31] & 0x0f) | 0x10;
    r
}

/// `acc = (acc + x) mod r` for canonical `acc, x < r`, on 256-bit LE integers:
/// the sum is below `2r < 2²⁵⁵`, so one conditional subtraction reduces it.
#[inline(always)]
fn add_mod_r(acc: &mut [u8; FR_BYTES], x: &[u8; FR_BYTES]) {
    let mut carry = 0u16;
    for i in 0..FR_BYTES {
        let t = acc[i] as u16 + x[i] as u16 + carry;
        acc[i] = t as u8;
        carry = t >> 8;
    }
    if !le_lt(acc, &FR_MODULUS_LE) {
        let mut borrow = 0i16;
        for i in 0..FR_BYTES {
            let t = acc[i] as i16 - FR_MODULUS_LE[i] as i16 - borrow;
            acc[i] = t as u8;
            borrow = (t < 0) as i16;
        }
    }
}

/// Verify several proofs against one VK with a single pairing call: `M + 3`
/// pairs instead of `4M`. `batch` is `M ≥ 1` entries, each a proof followed by
/// its public inputs — the `instruction_data` [`verify_proof_only`] takes,
/// repeated. `scratch` holds the pairing operands, at least `M + 3` of them (one
/// per proof, plus three): on the stack for a small batch (192 bytes each; a Solana stack
/// frame is 4 KB, so up to about 16 proofs), or on the heap or in account data:
///
/// ```ignore
/// let mut scratch = [[0u8; PAIRING_PAIR_BYTES]; 4 + 3];
/// let ok = verify_groth16_batch(VK_BYTES, instruction_data, &mut scratch)?;
/// ```
///
/// `Ok(true)` means every proof verifies (except with probability about 2⁻²⁵² per
/// batch an attacker tries);
/// `Ok(false)` means at least one doesn't, but not which: verify them one by one
/// to find it. Coordinates must be canonical, as in [`verify_groth16_strict`].
///
/// A batch can hold the same statement twice (proofs can be copied or
/// re-randomized): reject duplicate nullifiers *within* the batch as well as
/// against storage, and read each entry's public inputs from this same `batch`.
/// See the crate README's "Using batches safely".
pub fn verify_groth16_batch(
    vk_bytes: &[u8],
    batch: &[u8],
    scratch: &mut [[u8; PAIRING_PAIR_BYTES]],
) -> Result<bool, VerifierError> {
    if !coords_canonical(vk_bytes) {
        return Err(VerifierError::NonCanonicalCoordinate);
    }
    let vk = parse_vk(vk_bytes)?;
    let num_inputs = vk.ic.len() / G1_BYTES - 1;
    let entry = PROOF_BYTES + num_inputs * FR_BYTES;
    if batch.is_empty() || !batch.len().is_multiple_of(entry) {
        return Err(VerifierError::BatchLength {
            entry,
            actual: batch.len(),
        });
    }
    let n = batch.len() / entry;
    let need = n + 3;
    if scratch.len() < need {
        return Err(VerifierError::ScratchTooSmall {
            expected: need,
            actual: scratch.len(),
        });
    }
    // Every proof's coordinates canonical before the hash sees them.
    for e in batch.chunks_exact(entry) {
        if !coords_canonical(&e[..PROOF_BYTES]) {
            return Err(VerifierError::NonCanonicalCoordinate);
        }
    }

    // One proof needs no weights (r₀ = 1): skip the hash, and `α · 1` below.
    let seed = if n > 1 {
        batch_hash(&[
            BATCH_DOMAIN,
            &(vk_bytes.len() as u64).to_le_bytes(),
            vk_bytes,
            batch,
        ])
    } else {
        [0u8; 32]
    };
    let mut sum_r = [0u8; FR_BYTES];
    sum_r[0] = 1; // r₀
    let (mut vk_x_acc, mut c_acc) = (G1Point([0; G1_BYTES]), G1Point([0; G1_BYTES]));
    for (i, e) in batch.chunks_exact(entry).enumerate() {
        let (proof, public_inputs) = e.split_at(PROOF_BYTES);
        let a = g1_at(proof, 0);
        let c = g1_at(proof, G1_BYTES + G2_BYTES);
        let x = vk_x(vk.ic, public_inputs)?;
        let a = if i == 0 {
            (vk_x_acc, c_acc) = (x, c);
            a
        } else {
            let r = batch_weight(&seed, i as u64);
            add_mod_r(&mut sum_r, &r);
            vk_x_acc = g1_add(vk_x_acc, g1_scalar_mul(x, &r)?)?;
            c_acc = g1_add(c_acc, g1_scalar_mul(c, &r)?)?;
            g1_scalar_mul(a, &r)?
        };
        let slot = &mut scratch[i];
        slot[..G1_BYTES].copy_from_slice(&a.0);
        slot[G1_BYTES..].copy_from_slice(&proof[G1_BYTES..G1_BYTES + G2_BYTES]); // B
    }
    let alpha = if n > 1 {
        g1_scalar_mul(vk.alpha, &sum_r)?
    } else {
        vk.alpha
    };
    for (k, (g1, g2)) in [(alpha, vk.beta), (vk_x_acc, vk.gamma), (c_acc, vk.delta)]
        .into_iter()
        .enumerate()
    {
        let slot = &mut scratch[n + k];
        slot[..G1_BYTES].copy_from_slice(&g1.0);
        slot[G1_BYTES..].copy_from_slice(&g2.0);
    }
    let result = g16_pairing_bytes(scratch[..need].as_flattened())?;
    Ok(result[0] == 1 && result[1..].iter().all(|b| *b == 0))
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

    /// `add_mod_r` wraps at `r`, and weights are full
    /// width, nonzero and canonical.
    #[test]
    fn batch_weights_and_their_sum() {
        let mut r_minus_1 = FR_MODULUS_LE;
        r_minus_1[0] -= 1;
        let mut s = r_minus_1;
        add_mod_r(&mut s, &r_minus_1); // r - 2
        let mut two = [0u8; FR_BYTES];
        two[0] = 2;
        add_mod_r(&mut s, &two);
        assert_eq!(s, [0u8; FR_BYTES], "(r-1) + (r-1) + 2 = 2r = 0");
        let mut one = [0u8; FR_BYTES];
        one[0] = 1;
        let mut s = one;
        add_mod_r(&mut s, &one);
        assert_eq!(s[0], 2);

        for i in 1..64 {
            let w = batch_weight(&[7u8; 32], i);
            assert!(scalar_is_canonical(&w));
            assert_eq!(w[31] >> 4, 1, "w in [2^252, 2^253)");
        }
    }

    /// BN254's G1 generator in the LE wire format: `x = 1`, `y = 2`.
    fn g1_generator() -> G1Point {
        let mut bytes = [0u8; G1_BYTES];
        bytes[0] = 1;
        bytes[G1_BYTES / 2] = 2;
        G1Point(bytes)
    }

    /// `add_count` counts one doubling per bit below the MSB plus one add per
    /// set bit below it.
    #[test]
    fn add_count_boundaries() {
        assert_eq!(add_count(0), 0, "k = 0 never reaches the adder");
        assert_eq!(add_count(1), 0, "1 * P is P, no group op");
        assert_eq!(add_count(2), 1, "one doubling");
        assert_eq!(add_count(3), 2, "one doubling, one add");
        assert_eq!(add_count(5), 3, "0b101: two doublings, one add");
        assert_eq!(add_count(128), 7, "0b1000_0000: seven doublings, no adds");
        assert_eq!(add_count(192), 8, "0b1100_0000: seven doublings, one add");
    }

    /// The fast path accepts exactly the scalars whose double-and-add fits the
    /// measured budget, and nothing that merely looks small in its low limb.
    #[test]
    fn small_scalar_domain() {
        let le = |k: u64| {
            let mut s = [0u8; FR_BYTES];
            s[..8].copy_from_slice(&k.to_le_bytes());
            s
        };
        assert_eq!(small_scalar(&le(1)), Some(1));
        assert_eq!(small_scalar(&le(5)), Some(5));
        assert_eq!(
            small_scalar(&le(MAX_SMALL_SCALAR)),
            Some(MAX_SMALL_SCALAR),
            "2^MAX_ADDS costs exactly MAX_ADDS doublings"
        );
        assert_eq!(small_scalar(&le(0)), None, "zero is handled by the caller");
        assert_eq!(
            small_scalar(&le(MAX_SMALL_SCALAR + 1)),
            None,
            "past the budget"
        );
        assert_eq!(small_scalar(&le(192)), None, "add_count 8 > MAX_ADDS");

        // Small low limb, non-zero high limb: must not be mistaken for small.
        let mut spoofed = le(5);
        spoofed[FR_BYTES - 1] = 1;
        assert_eq!(small_scalar(&spoofed), None, "high limbs are not ignored");
    }

    /// Exhaustive over the whole fast-path domain: `mul_small` is bit-identical
    /// to the reference scalar mul for every `k` the fast path accepts.
    #[test]
    fn mul_small_matches_reference_mul_over_the_whole_domain() {
        let g = g1_generator();
        let mut checked = 0;
        for k in 1..=MAX_SMALL_SCALAR {
            let mut s = [0u8; FR_BYTES];
            s[..8].copy_from_slice(&k.to_le_bytes());
            if small_scalar(&s).is_none() {
                continue;
            }
            let want = g1_scalar_mul(g, &s).expect("reference mul");
            let got = mul_small(g, k).expect("double-and-add");
            assert_eq!(got.0, want.0, "k = {k}");
            checked += 1;
        }
        assert!(checked > 0, "the domain must not be empty");
    }

    /// The `k == 0` skip relies on `0 · P` being the additive identity: adding
    /// it back leaves the accumulator unchanged.
    #[test]
    fn zero_scalar_term_is_the_additive_identity() {
        let g = g1_generator();
        let zero_term = g1_scalar_mul(g, &[0u8; FR_BYTES]).expect("0 * G");
        assert_eq!(
            g1_add(g, zero_term).expect("G + O").0,
            g.0,
            "acc + 0*P must equal acc"
        );
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
    // These exercise the parse path of `verify_groth16` / `verify_groth16_strict`;
    // every structural error path early-exits *before* any `alt_bn128` curve op,
    // so they prove without stubbing the backend (the curve ops are unreachable
    // here). Totality over the full body (no panic for an *accepted* input, where
    // the curve ops do run) is discharged separately by the stubbed totality
    // harnesses below. `N` is bounded to small concrete values; the code is
    // uniform in `N`, so each bounded harness witnesses the general property.
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
    // Totality (no panic) over the FULL verify_groth16 body including the curve
    // ops, with kani::stub replacing the BN254 operators.
    //
    // The curve ops (G1Point::Mul/Add, pairing) resolve to the alt_bn128 syscall
    // on-chain / Arkworks off-chain — neither is symbolically executable in
    // Kani's budget. Every call site routes through the three #[inline(always)]
    // wrappers above, swapped for kani::stub replacements returning unconstrained
    // Result<_, AltBn128Error>; production codegen is byte-identical.
    //
    // Proves: panic freedom of the Rust around the curve ops on any backend
    // behaviour. Does NOT prove: the *value* of the boolean return (Groth16
    // soundness — out of scope), nor that curve ops yield on-curve points.
    //
    // N is bounded to {0, 1, 2} — empty / single-iter / multi-iter of the only
    // N-dependent path (the IC accumulator loop), whose body is per-iter uniform.
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
    // Named aliases for totality and operand assembly. The N-parameterised
    // harnesses above discharge totality; these give the single-entry-point names:
    //
    //   * totality_verify_groth16     — verify_groth16 on accepted-input shape.
    //   * totality_verify_proof_only  — verify_proof_only's split wrapper plus
    //                                   its downstream verify_groth16.
    //   * pairing_operand_assembly    — byte-level check that the buffer handed
    //                                   to alt_bn128_pairing equals
    //                                   neg(A) || B || α || β || vk_x || γ || C || δ.
    //
    // Same g1_scalar_mul / g1_add / g16_pairing stubs as the block above.
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

    /// **The fast path only fires on a scalar that *is* the integer it
    /// reports.** If `small_scalar` returns `Some(k)` then the full 32-byte
    /// input equals the little-endian encoding of `k`, and `k` sits inside the
    /// budgeted domain. This is what stops a large scalar with a small low limb
    /// from being routed through `mul_small` and multiplied by the wrong value.
    #[kani::proof]
    fn small_scalar_is_exact_and_budgeted() {
        let s: [u8; FR_BYTES] = kani::any();
        if let Some(k) = small_scalar(&s) {
            assert!(k >= 1 && k <= MAX_SMALL_SCALAR);
            assert!(add_count(k) <= MAX_ADDS);
            let mut expect = [0u8; FR_BYTES];
            expect[..8].copy_from_slice(&k.to_le_bytes());
            assert!(s == expect, "Some(k) implies the scalar is exactly k");
        }
    }

    fn stub_g16_pairing_bytes(_input: &[u8]) -> Result<[u8; 32], AltBn128Error> {
        if kani::any() {
            Ok(kani::any())
        } else {
            Err(AltBn128Error::GroupError)
        }
    }

    fn stub_batch_hash(_vals: &[&[u8]]) -> [u8; 32] {
        kani::any()
    }

    /// **Fail-closed: an empty batch is `Err(BatchLength)`**, never `Ok(true)`
    /// over zero proofs.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing_bytes, stub_g16_pairing_bytes)]
    #[kani::stub(super::batch_hash, stub_batch_hash)]
    fn batch_empty_rejected() {
        let vk = [0u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES]; // canonical
        let mut scratch = [[0u8; PAIRING_PAIR_BYTES]; 1 + 3];
        let r = verify_groth16_batch(&vk, &[], &mut scratch);
        assert!(matches!(r, Err(VerifierError::BatchLength { .. })));
    }

    /// **Fail-closed: a batch that isn't a whole number of entries is
    /// `Err(BatchLength)`** (one input ⇒ 288-byte entries; one byte over).
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing_bytes, stub_g16_pairing_bytes)]
    #[kani::stub(super::batch_hash, stub_batch_hash)]
    fn batch_partial_entry_rejected() {
        let vk = [0u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES];
        let batch: [u8; PROOF_BYTES + FR_BYTES + 1] = kani::any();
        let mut scratch = [[0u8; PAIRING_PAIR_BYTES]; 2 + 3];
        let r = verify_groth16_batch(&vk, &batch, &mut scratch);
        assert!(matches!(r, Err(VerifierError::BatchLength { .. })));
    }

    /// **Fail-closed: a scratch under `M + 3` pairing operands is
    /// `Err(ScratchTooSmall)`**, before anything is written to it.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing_bytes, stub_g16_pairing_bytes)]
    #[kani::stub(super::batch_hash, stub_batch_hash)]
    fn batch_scratch_too_small_rejected() {
        let vk = [0u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES];
        let batch: [u8; 2 * (PROOF_BYTES + FR_BYTES)] = kani::any();
        let mut scratch = [[0u8; PAIRING_PAIR_BYTES]; 2 + 3 - 1];
        let r = verify_groth16_batch(&vk, &batch, &mut scratch);
        assert!(matches!(r, Err(VerifierError::ScratchTooSmall { .. })));
    }

    /// **Totality of `verify_groth16_batch`** over two one-input proofs: no
    /// panic, out-of-bounds or overflow on any path (curve ops, the hash and the
    /// pairing stubbed, both outcomes of each explored).
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing_bytes, stub_g16_pairing_bytes)]
    #[kani::stub(super::batch_hash, stub_batch_hash)]
    fn totality_verify_groth16_batch() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES] = kani::any();
        let batch: [u8; 2 * (PROOF_BYTES + FR_BYTES)] = kani::any();
        let mut scratch = [[0u8; PAIRING_PAIR_BYTES]; 2 + 3];
        let _ = verify_groth16_batch(&vk, &batch, &mut scratch);
    }

    /// Totality with one proof: the `M == 1` path (no hash, `α` unscaled).
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing_bytes, stub_g16_pairing_bytes)]
    #[kani::stub(super::batch_hash, stub_batch_hash)]
    fn totality_verify_groth16_batch_m1() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + 2 * G1_BYTES] = kani::any();
        let batch: [u8; PROOF_BYTES + FR_BYTES] = kani::any();
        let mut scratch = [[0u8; PAIRING_PAIR_BYTES]; 1 + 3];
        let _ = verify_groth16_batch(&vk, &batch, &mut scratch);
    }

    /// Totality with no public inputs (`N == 0`, 256-byte entries), two proofs.
    #[kani::proof]
    #[kani::stub(super::g1_scalar_mul, stub_g1_scalar_mul)]
    #[kani::stub(super::g1_add, stub_g1_add)]
    #[kani::stub(super::g16_pairing_bytes, stub_g16_pairing_bytes)]
    #[kani::stub(super::batch_hash, stub_batch_hash)]
    fn totality_verify_groth16_batch_n0() {
        let vk: [u8; VK_FIXED_PREFIX_BYTES + G1_BYTES] = kani::any();
        let batch: [u8; 2 * PROOF_BYTES] = kani::any();
        let mut scratch = [[0u8; PAIRING_PAIR_BYTES]; 2 + 3];
        let _ = verify_groth16_batch(&vk, &batch, &mut scratch);
    }

    /// `add_mod_r` is addition mod `r` for every canonical `a, b < r`: the
    /// result is canonical and equals `a + b` or `a + b - r` (checked with
    /// independent u128 limb arithmetic).
    #[kani::proof]
    fn add_mod_r_is_mod_add() {
        let a: [u8; FR_BYTES] = kani::any();
        let b: [u8; FR_BYTES] = kani::any();
        kani::assume(u256_lt_le(&a, &FR_MODULUS_LE) && u256_lt_le(&b, &FR_MODULUS_LE));
        let mut s = a;
        add_mod_r(&mut s, &b);
        assert!(u256_lt_le(&s, &FR_MODULUS_LE));
        // a + b and s + (r or 0) as (hi, lo) u128 pairs; no carry out of hi,
        // since everything is below 2r < 2^255.
        let limbs = |x: &[u8; FR_BYTES]| {
            (
                u128::from_le_bytes(x[16..].try_into().unwrap()),
                u128::from_le_bytes(x[..16].try_into().unwrap()),
            )
        };
        let add = |(xh, xl): (u128, u128), (yh, yl): (u128, u128)| {
            let (lo, c) = xl.overflowing_add(yl);
            (xh + yh + c as u128, lo)
        };
        let want = add(limbs(&a), limbs(&b));
        assert!(add(limbs(&s), (0, 0)) == want || add(limbs(&s), limbs(&FR_MODULUS_LE)) == want);
    }
}
