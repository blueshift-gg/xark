//! `xark`: the standard prelude (`use xark::prelude::*`) for writing zero-knowledge
//! programs in the `xark` Rust subset. A circuit is an ordinary `#![no_std]` Rust
//! function over [`Field`] values; the toolchain compiles it end to end (rustc-MIR
//! → xark-IR → R1CS → Groth16) with no per-gadget backend support — gadgets are
//! ordinary frontend library code lowering to the same primitive constraint set.
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
//! [`Private<T>`]/[`Public<T>`] are transparent aliases the compiler recovers from
//! the signature; [`require_eq`] emits an equality constraint (circuit `==`, not
//! native `bool`); `Field` supports `+ - * ^` (`^ n` = exponentiation). Lower-level
//! bit/word helpers (`xark-bits`) and gadgets (`xark-bignum`, `xark-poseidon`, …)
//! are separate crates.

#![no_std]

// `Field::to_decimal` (host-side input tooling) allocates a `String`. `alloc` links
// in both builds; the allocation only ever runs host-side, never in a circuit.
extern crate alloc;

// Self-alias so the `#[derive(CircuitInput)]` macro's generated `::xark::Field`
// paths resolve *inside* this crate (where the derive is used on `Digest`), the
// same way they resolve in downstream circuit crates. Standard proc-macro pattern.
extern crate self as xark;

/// The `xark` language markers: `Field`, `Private`, `Public`, `require_eq`, the
/// `Field` methods and operator impls, and the recognized intrinsics.
pub mod lang;

/// The compiler intrinsics — the `#[inline(never)]` `loop {}` stubs the compiler
/// recognizes by name in MIR (the `Field` operator/hint ABI). See the module doc
/// for the constraint-vs-hint distinction. `lang.rs` calls these to back its
/// `Field` impls; circuit authors use the `Field` methods, not these directly.
pub mod intrinsics;

/// The everyday circuit-author surface. `use xark::prelude::*;`.
pub mod prelude {
    pub use crate::lang::{
        Field, Private, Public, require, require_eq, require_ge, require_gt, require_le,
        require_lt, require_ne, witness_begin, witness_end,
    };
    // `CircuitInput` makes a `Field`-composed struct a circuit input (the everyday way to
    // group inputs); `circuit` is the entry attribute.
    pub use xark_macros::{CircuitInput, circuit};
}

// Same surface as `prelude`, re-exported at the crate root so both
// `use xark::prelude::*;` and `use xark::{require, Field, ...};` work.
pub use crate::lang::{
    Field, Private, Public, require, require_eq, require_ge, require_gt, require_le, require_lt,
    require_ne, witness_begin, witness_end,
};
// `require_eq` dispatches through `RequireEqCircuit`, comparing scalars, fixed
// arrays, and composite types; downstream crates impl it for their own shapes.
pub use crate::lang::RequireEqCircuit;
// The recognized scalar-equality intrinsic every `RequireEqCircuit` impl bottoms
// out at — re-exported (doc-hidden) so the compiler's intrinsic scan finds it by
// name. Authors never touch it; they write `require_eq`.
#[doc(hidden)]
pub use crate::lang::__xark_require_eq_scalar;
// `#[derive(CircuitInput)]` makes a `Field`-composed struct a circuit input: it
// generates the `Into<[Field; N]>` flatten AND the host-side `NativeInput` fan-out
// (`Native = Self`, each field rendered via `Field::to_decimal`) — so the host builds
// the same struct with `Field` values, no `String` mirror. `#[derive(Transparent)]`
// does the same for a byte-backed gadget type (`limbs`/native-bytes form).
pub use xark_macros::{CircuitInput, Transparent, circuit};
