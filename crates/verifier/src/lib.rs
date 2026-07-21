//! Solana on-chain Groth16 BN254 verifier.
//!
//! Two ways to use this crate:
//! * **Generated per-circuit crate** (recommended) — `xark export` emits a small
//!   crate embedding the circuit's verifying key as a `const Verifier<N>` and
//!   exposing `verify(...)`. The VK is baked in at compile time, so it can't be
//!   swapped.
//! * **Generic-VK** — call [`verify_groth16`] directly with the VK, proof, and
//!   public inputs. When the VK is loaded from an account the program **must**
//!   authenticate it (e.g. pin its hash).
//!
//! Both paths use the LE wire format documented in [`verifier`]. Curve arithmetic
//! comes from [`solana_nostd_alt_bn128`], which routes through the `alt_bn128`
//! syscalls on-chain and Arkworks off-chain. The crate is `no_std` on the Solana
//! target and links only `core` there, so the verifier can be pulled into the
//! `#![no_std]` cdylibs `svm-unit-test` generates without a `#[panic_handler]`
//! collision.
#![cfg_attr(any(target_os = "solana", target_arch = "bpf"), no_std)]

pub mod typed;
pub mod verifier;

pub use typed::*;
pub use verifier::*;
