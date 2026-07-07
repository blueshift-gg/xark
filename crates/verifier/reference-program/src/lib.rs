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

use solana_program_entrypoint::entrypoint;
use solana_program_error::ProgramError;
use xark_verifier::{verify_groth16, FR_BYTES, PROOF_BYTES};

entrypoint!(process_instruction);

/// The single entry point: parses the VK out of account 0's data, splits
/// instruction data into `proof || public_inputs`, and calls
/// [`verify_groth16`]. A failed pairing check (`Ok(false)`) is treated as
/// `Err(ProgramError::Custom(1))` so the runtime aborts the transaction.
pub fn process_instruction(
    _program_id: &solana_program_entrypoint::__Pubkey,
    accounts: &[solana_program_entrypoint::__AccountInfo<'_>],
    instruction_data: &[u8],
) -> Result<(), ProgramError> {
    if instruction_data.len() < PROOF_BYTES {
        return Err(ProgramError::Custom(2));
    }
    let (proof, public_inputs) = instruction_data.split_at(PROOF_BYTES);
    if public_inputs.len() % FR_BYTES != 0 {
        return Err(ProgramError::Custom(3));
    }
    // ⚠️ SECURITY — VK AUTHENTICATION IS THE CALLER'S RESPONSIBILITY.
    //
    // This reference program reads the verifying key from account 0's data with
    // **no** owner check, address pin, or hash check. That is acceptable *only*
    // because this binary is the circuit-agnostic reproducible-build artifact
    // (a single fixed `.so`, hash-pinned in `expected.sha256`) — it is NOT a
    // production template for VK handling. A real deployment MUST authenticate
    // the VK, e.g. bake it in at compile time via
    // `Verifier::<N>::from_le_bytes(include_bytes!("vk.bin"))` (see the
    // `xark-verifier` README), or hard-assert the account's owner/address and a
    // pinned VK hash here. Without that, an attacker supplies their own account
    // 0 holding any VK they have a valid proof for and `verify_groth16` returns
    // `Ok(true)` — accepting a proof for a *different* statement.
    let vk_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let vk_data = vk_account.try_borrow_data()?;
    match verify_groth16(&vk_data, proof, public_inputs) {
        Ok(true) => Ok(()),
        Ok(false) => Err(ProgramError::Custom(1)),
        Err(_) => Err(ProgramError::Custom(4)),
    }
}
