//! `xark`: the language *and* the toolchain. As a **library** (`use xark::prelude::*`)
//! it is the standard prelude for writing zero-knowledge programs in the
//! `xark` Rust subset.
//!
//! A circuit is an ordinary `#![no_std]` Rust function over [`Field`] values.
//! The `xark` toolchain compiles it end to end — rustc-MIR → xark-IR → R1CS →
//! Groth16 — with **no per-gadget backend support**: gadgets are ordinary
//! frontend library code that lowers to the same small primitive constraint
//! set, and the backend is a generic Groth16 over that constraint system.
//!
//! One glob import gives you the everyday surface:
//!
//! ```rust,ignore
//! #![no_std]
//! use xark::prelude::*;
//!
//! /// Prove knowledge of a cube root: `secret^3 == result`.
//! pub fn circuit(secret: Private<Field>, result: Public<Field>) {
//!     assert_eq(secret ^ 3, result);
//! }
//! ```
//!
//! [`Private<T>`] marks a private witness input, [`Public<T>`] a public input;
//! both are transparent aliases the compiler recovers from the signature.
//! [`assert_eq`] emits an equality constraint (circuit `==`, not native
//! `bool`). `Field` supports `+ - * ^` (with `^ n` meaning exponentiation).
//!
//! ## Building gadgets
//!
//! Lower-level bit/word helpers live in the `xark-bits` crate (`to_bits32`,
//! `xor32`, `rotr32`, `add32`, …). Specialized building blocks — non-native
//! ("foreign field") arithmetic (`xark-bignum`) and the gadgets (`xark-poseidon`,
//! `xark-keccak`, …) — are *separate crates* you add only when you need them.

#![no_std]

/// The `xark` language markers (`Field`, `Private`, `Public`, `assert_eq`, the
/// `Field` methods and operator impls, and the recognized intrinsics). Formerly
/// the standalone `xark-lang` crate, now an in-crate module so that circuit
/// programs and gadgets depend on a single crate (`xark`).
pub mod lang;

/// The compiler intrinsics — the `#[inline(never)]` `loop {}` stubs the compiler
/// recognizes by name in MIR (the `Field` operator/hint ABI). See the module doc
/// for the constraint-vs-hint distinction. `lang.rs` calls these to back its
/// `Field` impls; circuit authors use the `Field` methods, not these directly.
pub mod intrinsics;

/// The everyday circuit-author surface. `use xark::prelude::*;`.
pub mod prelude {
    pub use crate::lang::{
        assert, assert_eq, assert_ge, assert_gt, assert_le, assert_lt, Field, Private, Public,
    };
    pub use xark_macros::circuit;
}

pub use crate::lang::{assert_eq, Field, Private, Public};
pub use xark_macros::circuit;
