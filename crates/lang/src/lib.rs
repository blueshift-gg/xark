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
//!     require_eq(secret ^ 3, result);
//! }
//! ```
//!
//! [`Private<T>`] marks a private witness input, [`Public<T>`] a public input;
//! both are transparent aliases the compiler recovers from the signature.
//! [`require_eq`] emits an equality constraint (circuit `==`, not native
//! `bool`). `Field` supports `+ - * ^` (with `^ n` meaning exponentiation).
//!
//! ## Building gadgets
//!
//! Lower-level bit/word helpers live in the `xark-bits` crate (`to_bits32`,
//! `xor32`, `rotr32`, `add32`, …). Specialized building blocks — non-native
//! ("foreign field") arithmetic (`xark-bignum`) and the gadgets (`xark-poseidon`,
//! `xark-keccak`, …) — are *separate crates* you add only when you need them.

#![no_std]

// Self-alias so the `#[derive(CircuitInput)]` macro's generated `::xark::Field`
// paths resolve *inside* this crate (where the derive is used on `Digest`), the
// same way they resolve in downstream circuit crates. Standard proc-macro pattern.
extern crate self as xark;

/// The `xark` language markers (`Field`, `Private`, `Public`, `require_eq`, the
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
        require, require_eq, require_ge, require_gt, require_le, require_lt, witness_begin,
        witness_end, Field, Private, Public,
    };
    pub use xark_macros::circuit;
}

// The same surface as `prelude`, re-exported at the crate root so both
// `use xark::prelude::*;` and `use xark::{require, Field, ...};` work.
pub use crate::lang::{
    require, require_eq, require_ge, require_gt, require_le, require_lt, witness_begin,
    witness_end, Field, Private, Public,
};
// `require_eq` (above) dispatches through `RequireEqCircuit`, so it compares scalars,
// fixed arrays, and composite circuit types (e.g. a SHA-256 digest vs a `Digest`).
// Downstream crates import the trait to add impls for their own gadget-output shapes.
pub use crate::lang::RequireEqCircuit;
// The recognized scalar equality intrinsic every `RequireEqCircuit` impl bottoms out
// at — re-exported at the crate root (doc-hidden) so the compiler's intrinsic scan
// finds it by name. Authors never touch it; they write `require_eq`.
#[doc(hidden)]
pub use crate::lang::__xark_require_eq_scalar;
// `#[circuit]`, the `#[derive(CircuitInput)]` that generates a struct's
// `Into<[Field; N]>` in the compiler's structural-flatten order, and
// `#[derive(Transparent)]` that generates a transparent type's host `NativeInput`
// leaf fan-out (matching that same flatten order).
pub use xark_macros::{circuit, CircuitInput, Transparent};
