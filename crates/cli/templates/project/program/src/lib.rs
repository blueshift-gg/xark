//! A Solana program that verifies proofs of the `{{circuit}}` circuit (Pinocchio).
//! One instruction, `Verify`: a proof and the public inputs it proves. `verify`
//! comes from the crate `xark export` generated, and checks the proof with the
//! alt_bn128 syscalls.
#![cfg_attr(not(test), no_std)]

use pinocchio::{AccountView, Address, ProgramResult, error::ProgramError, program_entrypoint};

mod errors;
mod instructions;

pub use errors::*;
pub use instructions::*;

program_entrypoint!(process_instruction);
#[cfg(not(test))]
pinocchio::nostd_panic_handler!();
#[cfg(not(test))]
pinocchio::no_allocator!();

fn process_instruction(
    _program_id: &Address,
    accounts: &mut [AccountView],
    instruction_data: &[u8],
) -> ProgramResult {
    let result = dispatch(accounts, instruction_data);
    // The program's own errors log their names, which its tests match.
    if let Err(error @ ProgramError::Custom(_)) = &result {
        log(error.to_str::<{{Error}}>());
    }
    result
}

fn dispatch(_accounts: &mut [AccountView], instruction_data: &[u8]) -> ProgramResult {
    match instruction_data.split_first() {
        Some((Verify::DISCRIMINATOR, data)) => Verify::try_from(data)?.process(),
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

/// `Program log: <message>`.
fn log(message: &str) {
    #[cfg(any(target_os = "solana", target_arch = "bpf"))]
    // SAFETY: the pointer and length are a valid `&str`'s.
    unsafe {
        pinocchio::syscalls::sol_log_(message.as_ptr(), message.len() as u64)
    };
    #[cfg(not(any(target_os = "solana", target_arch = "bpf")))]
    let _ = message;
}
