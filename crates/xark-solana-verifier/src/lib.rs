//! Solana on-chain Groth16 BN254 verifier.
//!
//! Two ways to use this crate:
//!
//! * **Embedded-VK program** — invoke the [`xark_groth16_program!`] macro
//!   in your program crate's `lib.rs` with `include_bytes!("vk.bin")`.
//!   The macro emits a pinocchio entrypoint, a generic `verify_payload`
//!   function, and a `const VK_BYTES` so tests can call it host-side.
//!   Instruction data carries only `proof_bytes || public_inputs`
//!   (~256 + 32 × N bytes).
//!
//! * **Generic-VK program** — call [`verify_groth16`] directly with the
//!   VK, proof, and public inputs you parsed out of instruction data
//!   yourself. Useful when a single program serves many circuits, with
//!   the VK identified by a hash and loaded from an account.
//!
//! Both paths use the LE wire format documented in [`verifier`] and the
//! `alt_bn128_*_le` syscalls from `solana-bn254 3.x`. Host-side tests can
//! swap [`SolanaBackend`] for an Arkworks impl via [`verify_groth16_with`].
//!
//! ## Crate features
//!
//! * `ark-backend` — exposes a host-side Arkworks implementation of
//!   [`Bn128Backend`] (in [`ark_backend`]) for unit tests that don't want
//!   to spin up Mollusk.

pub mod macros;
pub mod verifier;

#[cfg(feature = "ark-backend")]
pub mod ark_backend;

pub use verifier::*;
