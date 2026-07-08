//! Solana on-chain Groth16 BN254 verifier.
//!
//! Two ways to use this crate:
//!
//! * **A generated per-circuit crate** (recommended) — `xark export` emits a
//!   small, self-contained crate that embeds your circuit's verifying key as
//!   a `const Verifier<N>` (via `Verifier::from_le_bytes(include_bytes!(…))`)
//!   and exposes `verify(...)`. Your Solana program just depends on that crate
//!   and calls it; when the circuit changes you re-export, and the generated
//!   crate is the only thing that updates. The VK is baked in at compile time,
//!   so it can't be swapped.
//!
//! * **Generic-VK** — call [`verify_groth16`] directly with the VK, proof,
//!   and public inputs you parsed out of instruction data yourself. Useful
//!   when a single program serves many circuits, with the VK loaded from an
//!   account — which the program **must** authenticate (e.g. pin its hash).
//!
//! Both paths use the LE wire format documented in [`verifier`]. Curve
//! arithmetic is provided by [`solana_nostd_alt_bn128`], which routes
//! through the `alt_bn128` syscalls on-chain and Arkworks off-chain.
//!
//! The crate is `no_std` on the Solana target (`cfg_attr(target_os =
//! "solana", no_std)`) and links nothing but `core` there, so the whole
//! verifier — including [`verify_groth16`] — can be pulled into the
//! `#![no_std]` cdylibs `svm-unit-test` generates for each `#[svm_test]`
//! without a `#[panic_handler]` collision.
//!
//! ## Testing
//!
//! * `tests/sbpf.rs` — `#[svm_test]` bodies that compile `verify_groth16`
//!   into their own SBPF programs and run them in [Mollusk] on the real
//!   `alt_bn128` syscalls (positive across every committed circuit, plus
//!   negative tests that bad inputs are rejected on chain), reporting
//!   per-proof compute units.
//! * `tests/binding.rs` — every public input is cryptographically bound.
//! * `tests/fuzz.rs` — `verify_groth16` never panics and never accepts
//!   adversarial bytes.
//!
//! Host `cargo test` runs the verifier against the Arkworks path, so the
//! logic is covered even without the SBF toolchain.
//!
//! [Mollusk]: https://github.com/anza-xyz/mollusk
#![cfg_attr(any(target_os = "solana", target_arch = "bpf"), no_std)]

pub mod typed;
pub mod verifier;

pub use typed::*;
pub use verifier::*;
