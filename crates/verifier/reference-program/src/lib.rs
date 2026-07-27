//! Reference Solana program that wraps [`xark_verifier::verify_groth16`].
//!
//! The instruction data layout is `proof_bytes || public_inputs` (the same
//! wire format the verifier itself documents); the VK is read from the
//! single account at index 0 (a read-only account whose data is the LE VK
//! blob produced by `xark export`).
//!
//! **This program is the reproducible-build target.** Its compiled
//! `.so`'s SHA-256 is pinned in
//! `crates/verifier/reference-program/expected.sha256` and enforced by the
//! `reproducible-build` CI workflow. See `docs/reproducible-build.md`.
//!
//! Real production deployments will bake their VK in at compile time via
//! `Verifier<N>::from_le_bytes(include_bytes!("vk.bin"))` (see the
//! `xark-verifier` README). This reference program reads it dynamically so
//! the audit artifact is a single fixed `.so`, independent of any
//! particular circuit.
#![cfg_attr(target_os = "solana", no_std)]

use pinocchio::{
    AccountView, Address, ProgramResult, default_allocator, error::ProgramError,
    nostd_panic_handler, program_entrypoint,
};
use xark_verifier::{FR_BYTES, PROOF_BYTES, verify_groth16};

// This program and all its on-chain dependencies are `no_std`, so wire up the
// entrypoint, bump allocator, and a real `#[panic_handler]` explicitly — the
// all-in-one `entrypoint!` macro assumes `std` provides the panic handler.
program_entrypoint!(process_instruction);
default_allocator!();
nostd_panic_handler!();

/// The single entry point: parses the VK out of account 0's data, splits
/// instruction data into `proof || public_inputs`, and calls
/// [`verify_groth16`]. A failed pairing check (`Ok(false)`) is treated as
/// `Err(ProgramError::Custom(1))` so the runtime aborts the transaction.
pub fn process_instruction(
    _program_id: &Address,
    accounts: &mut [AccountView],
    instruction_data: &[u8],
) -> ProgramResult {
    if instruction_data.len() < PROOF_BYTES {
        return Err(ProgramError::Custom(2));
    }
    let (proof, public_inputs) = instruction_data.split_at(PROOF_BYTES);
    if public_inputs.len() % FR_BYTES != 0 {
        return Err(ProgramError::Custom(3));
    }
    // SECURITY: this reference program reads the VK from account 0 with no owner/
    // address/hash check — acceptable only because it is the circuit-agnostic,
    // hash-pinned reproducible-build artifact, NOT a production template. A real
    // deployment MUST authenticate the VK (bake it in, or pin the account
    // owner/address and VK hash), else an attacker's VK is accepted.
    let vk_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let vk_data = vk_account.try_borrow()?;
    match verify_groth16(&vk_data, proof, public_inputs) {
        Ok(true) => Ok(()),
        Ok(false) => Err(ProgramError::Custom(1)),
        Err(_) => Err(ProgramError::Custom(4)),
    }
}
