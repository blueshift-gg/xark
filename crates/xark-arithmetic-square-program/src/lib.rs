//! Sample on-chain Groth16 verifier program for the `arithmetic_square`
//! circuit. Demonstrates the `xark_groth16_program!` macro: a single
//! invocation embeds the LE-encoded VK at compile time and emits a
//! pinocchio entrypoint that consumes `proof_bytes || public_inputs` from
//! the instruction data.
//!
//! Build for SBF deployment:
//!
//! ```bash
//! cargo build-sbf -p xark-arithmetic-square-program
//! ```
//!
//! Output: `target/deploy/xark_arithmetic_square_program.so`.
//!
//! The host-side `xark-solana-verifier`'s Mollusk e2e test
//! (`tests/mollusk_e2e.rs`) loads that .so and runs it against the
//! committed `arithmetic_square` KAT proof.

xark_solana_verifier::xark_groth16_program! {
    vk: include_bytes!(
        "../../../tests/fixtures/groth16/arithmetic_square/verifying_key.solana.bin"
    ),
}
