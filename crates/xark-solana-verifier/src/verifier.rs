//! Groth16 BN254 verifier core (little-endian wire format).
//!
//! # Wire format
//!
//! The Solana `alt_bn128` syscalls expose explicit LE variants
//! (`alt_bn128_g1_addition_le`, `alt_bn128_g1_multiplication_le`,
//! `alt_bn128_pairing_le`) since `solana-bn254 3.x`. This crate's wire
//! format is LE end-to-end: every `Fq` and `Fr` element is encoded as a
//! 32-byte little-endian limb, so the bytes go straight to the syscall
//! without conversion.
//!
//! ```text
//! vk_bytes     : alpha    (G1, 64 B)
//!              | beta     (G2, 128 B)
//!              | gamma    (G2, 128 B)
//!              | delta    (G2, 128 B)
//!              | ic_count (u32 LE, 4 B)
//!              | ic_count * G1 (64 B each)
//! proof_bytes  : A (G1, 64 B) | B (G2, 128 B) | C (G1, 64 B)     (256 B)
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
//! # Backend abstraction
//!
//! The hot path is parametrised over a [`Bn128Backend`] so host-side unit
//! tests can swap the syscalls for an Arkworks-native implementation. The
//! deployed program calls [`verify_groth16`] which selects
//! [`SolanaBackend`]; tests call [`verify_groth16_with`].

use solana_program_error::ProgramError;
use thiserror::Error;

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

// -- error type ---------------------------------------------------------------

/// Reasons `verify_groth16` may reject an input *without* running the
/// pairing check (structural / arity validation, mostly).
#[derive(Debug, Error)]
pub enum VerifierError {
    #[error("vk_bytes shorter than the fixed prefix ({expected} B) + ic_count: got {actual} B")]
    TruncatedVk { expected: usize, actual: usize },
    #[error("vk ic_count is zero; need at least one IC element")]
    EmptyIc,
    #[error("vk ic length mismatch: ic_count={ic_count}, expected {expected} B, got {actual} B")]
    IcLengthMismatch {
        ic_count: u32,
        expected: usize,
        actual: usize,
    },
    #[error("proof_bytes must be exactly {expected} B; got {actual}")]
    ProofLength { expected: usize, actual: usize },
    #[error("public_inputs must be {expected} B (num_inputs * {fr}); got {actual}")]
    PublicInputsLength {
        fr: usize,
        expected: usize,
        actual: usize,
    },
    #[error(
        "public-input arity mismatch: vk has ic_count={ic_count} (=> {expected_inputs} inputs), got {actual_inputs}"
    )]
    InputArityMismatch {
        ic_count: u32,
        expected_inputs: u32,
        actual_inputs: u32,
    },
    #[error("alt_bn128 syscall returned an error")]
    Syscall,
}

impl From<VerifierError> for ProgramError {
    fn from(_e: VerifierError) -> Self {
        ProgramError::InvalidInstructionData
    }
}

// -- backend trait ------------------------------------------------------------

/// Pluggable BN254 backend so that tests can swap in an Arkworks-native
/// implementation while the deployed program uses Solana's syscalls.
///
/// All inputs and outputs use the LE wire format (G1 = 64 B, G2 = 128 B,
/// Fr = 32 B LE, pairing input = N × 192 B).
pub trait Bn128Backend {
    /// G1 point addition. `input` is 128 B (two G1). Returns 64 B (one G1).
    fn add(input: &[u8]) -> Result<[u8; G1_BYTES], VerifierError>;
    /// G1 scalar multiplication. `input` is 96 B (G1 || Fr). Returns 64 B.
    fn mul(input: &[u8]) -> Result<[u8; G1_BYTES], VerifierError>;
    /// Multi-pair pairing check. `input` is N × 192 B. Returns `true` iff
    /// the pairing product equals the identity in GT.
    fn pairing(input: &[u8]) -> Result<bool, VerifierError>;
}

// -- Solana syscall backend ---------------------------------------------------

const G1_ADD_INPUT_LEN: usize = 2 * G1_BYTES;
const G1_MUL_INPUT_LEN: usize = G1_BYTES + FR_BYTES;

/// Production backend: invokes the `alt_bn128_*_le` syscalls.
pub struct SolanaBackend;

impl Bn128Backend for SolanaBackend {
    fn add(input: &[u8]) -> Result<[u8; G1_BYTES], VerifierError> {
        let buf: &[u8; G1_ADD_INPUT_LEN] =
            input.try_into().map_err(|_| VerifierError::Syscall)?;
        let out = solana_bn254::prelude::alt_bn128_g1_addition_le(buf)
            .map_err(|_| VerifierError::Syscall)?;
        if out.len() != G1_BYTES {
            return Err(VerifierError::Syscall);
        }
        let mut arr = [0u8; G1_BYTES];
        arr.copy_from_slice(&out);
        Ok(arr)
    }

    fn mul(input: &[u8]) -> Result<[u8; G1_BYTES], VerifierError> {
        let buf: &[u8; G1_MUL_INPUT_LEN] =
            input.try_into().map_err(|_| VerifierError::Syscall)?;
        let out = solana_bn254::prelude::alt_bn128_g1_multiplication_le(buf)
            .map_err(|_| VerifierError::Syscall)?;
        if out.len() != G1_BYTES {
            return Err(VerifierError::Syscall);
        }
        let mut arr = [0u8; G1_BYTES];
        arr.copy_from_slice(&out);
        Ok(arr)
    }

    fn pairing(input: &[u8]) -> Result<bool, VerifierError> {
        let out = solana_bn254::prelude::alt_bn128_pairing_le(input)
            .map_err(|_| VerifierError::Syscall)?;
        // The syscall's output is a 32-byte u256 in *little-endian*: `1`
        // iff the pairing product equals identity in GT.
        if out.len() != 32 {
            return Err(VerifierError::Syscall);
        }
        // LE u256 == 1 iff byte 0 == 1 and bytes 1..32 are all zero.
        let is_one = out[0] == 1 && out[1..].iter().all(|b| *b == 0);
        Ok(is_one)
    }
}

// -- core verifier ------------------------------------------------------------

/// Production entry: verify a Groth16 proof using Solana syscalls.
pub fn verify_groth16(
    vk_bytes: &[u8],
    proof_bytes: &[u8],
    public_inputs: &[u8],
) -> Result<bool, VerifierError> {
    verify_groth16_with::<SolanaBackend>(vk_bytes, proof_bytes, public_inputs)
}

/// Backend-generic Groth16 verifier. Production uses [`SolanaBackend`];
/// host-side tests pass an arkworks-backed impl.
pub fn verify_groth16_with<B: Bn128Backend>(
    vk_bytes: &[u8],
    proof_bytes: &[u8],
    public_inputs: &[u8],
) -> Result<bool, VerifierError> {
    // ---- Parse VK ----------------------------------------------------------
    if vk_bytes.len() < VK_FIXED_PREFIX_BYTES + 4 {
        return Err(VerifierError::TruncatedVk {
            expected: VK_FIXED_PREFIX_BYTES + 4,
            actual: vk_bytes.len(),
        });
    }
    let alpha = &vk_bytes[0..G1_BYTES];
    let beta = &vk_bytes[G1_BYTES..G1_BYTES + G2_BYTES];
    let gamma = &vk_bytes[G1_BYTES + G2_BYTES..G1_BYTES + 2 * G2_BYTES];
    let delta = &vk_bytes[G1_BYTES + 2 * G2_BYTES..G1_BYTES + 3 * G2_BYTES];

    let ic_count_offset = VK_FIXED_PREFIX_BYTES;
    let ic_count = u32::from_le_bytes([
        vk_bytes[ic_count_offset],
        vk_bytes[ic_count_offset + 1],
        vk_bytes[ic_count_offset + 2],
        vk_bytes[ic_count_offset + 3],
    ]);
    if ic_count == 0 {
        return Err(VerifierError::EmptyIc);
    }
    let ic_bytes_start = ic_count_offset + 4;
    let ic_bytes_expected = (ic_count as usize) * G1_BYTES;
    if vk_bytes.len() != ic_bytes_start + ic_bytes_expected {
        return Err(VerifierError::IcLengthMismatch {
            ic_count,
            expected: ic_bytes_start + ic_bytes_expected,
            actual: vk_bytes.len(),
        });
    }
    let ic_slice = &vk_bytes[ic_bytes_start..];

    // ---- Parse proof -------------------------------------------------------
    if proof_bytes.len() != PROOF_BYTES {
        return Err(VerifierError::ProofLength {
            expected: PROOF_BYTES,
            actual: proof_bytes.len(),
        });
    }
    let proof_a = &proof_bytes[0..G1_BYTES];
    let proof_b = &proof_bytes[G1_BYTES..G1_BYTES + G2_BYTES];
    let proof_c = &proof_bytes[G1_BYTES + G2_BYTES..PROOF_BYTES];

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
    let mut acc = [0u8; G1_BYTES];
    acc.copy_from_slice(&ic_slice[0..G1_BYTES]);
    for i in 0..num_inputs as usize {
        let ic_i = &ic_slice[(i + 1) * G1_BYTES..(i + 2) * G1_BYTES];
        let scalar = &public_inputs[i * FR_BYTES..(i + 1) * FR_BYTES];

        let mut mul_in = [0u8; G1_MUL_INPUT_LEN];
        mul_in[..G1_BYTES].copy_from_slice(ic_i);
        mul_in[G1_BYTES..].copy_from_slice(scalar);
        let term = B::mul(&mul_in)?;

        let mut add_in = [0u8; G1_ADD_INPUT_LEN];
        add_in[..G1_BYTES].copy_from_slice(&acc);
        add_in[G1_BYTES..].copy_from_slice(&term);
        acc = B::add(&add_in)?;
    }

    // ---- Assemble pairing input: 4 × (G1, G2) = 768 B ----------------------
    //   (-A, B), (alpha, beta), (vk_x, gamma), (C, delta).
    // `proof_a` is pre-negated by the exporter.
    let mut pairing_input = [0u8; 4 * PAIRING_PAIR_BYTES];
    pairing_input[0..G1_BYTES].copy_from_slice(proof_a);
    pairing_input[G1_BYTES..G1_BYTES + G2_BYTES].copy_from_slice(proof_b);
    let off = PAIRING_PAIR_BYTES;
    pairing_input[off..off + G1_BYTES].copy_from_slice(alpha);
    pairing_input[off + G1_BYTES..off + G1_BYTES + G2_BYTES].copy_from_slice(beta);
    let off = 2 * PAIRING_PAIR_BYTES;
    pairing_input[off..off + G1_BYTES].copy_from_slice(&acc);
    pairing_input[off + G1_BYTES..off + G1_BYTES + G2_BYTES].copy_from_slice(gamma);
    let off = 3 * PAIRING_PAIR_BYTES;
    pairing_input[off..off + G1_BYTES].copy_from_slice(proof_c);
    pairing_input[off + G1_BYTES..off + G1_BYTES + G2_BYTES].copy_from_slice(delta);

    B::pairing(&pairing_input)
}

/// Verify a proof against a *pre-baked* VK with a compact instruction
/// data layout: `proof_bytes (256 B) || public_inputs (N × 32 B)`. Used
/// by [`xark_groth16_program`](crate::xark_groth16_program) to keep the
/// on-chain entrypoint as small as possible — the VK is embedded in
/// program code, not transmitted with every call.
pub fn verify_proof_only_with<B: Bn128Backend>(
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
    verify_groth16_with::<B>(vk_bytes, proof, public_inputs)
}
