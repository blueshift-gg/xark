//! `xark`: the standard prelude (`use xark::prelude::*`) for writing zero-knowledge
//! programs in the `xark` Rust subset. A circuit is an ordinary Rust
//! function over [`Field`] values; the toolchain compiles it end to end (rustc →
//! wasm32 → xark-IR → R1CS → Groth16) with no per-gadget backend support — gadgets are
//! ordinary frontend library code lowering to the same primitive constraint set.
//!
//! ```rust,ignore
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
// Host builds run circuit code natively (`intrinsics::native`), with a per-thread
// witness-region depth. The circuit build links `std` too (`wasm32-unknown-unknown`
// ships it), so a circuit crate may use it: panics reach the compiler through a hook
// (`wasm::install_panic_hook`), not a `#[panic_handler]` that would clash with std's.
#[cfg(any(not(xark), target_arch = "wasm32"))]
extern crate std;

// Self-alias so `#[input]`'s generated `::xark::…` paths resolve *inside*
// this crate (where it derives `Country`), the same way they resolve in downstream
// circuit crates. Standard proc-macro pattern.
extern crate self as xark;

/// The `xark` language markers: `Field`, `Private`, `Public`, `require_eq`, the
/// `Field` methods and operator impls, and the recognized intrinsics.
pub mod lang;

pub mod input;
pub use input::{Enum, Input};

/// Everyday input types: [`Date`], [`Text`], [`Choice`] and [`Bitfield`] (of an
/// [`Enum`]).
pub mod types;
#[cfg(not(xark))]
pub use types::InvalidValue;
pub use types::{Bitfield, Choice, Date, Text};

#[cfg(not(xark))]
pub mod client;

/// The client build's exported items, or nothing in any other build (so a circuit
/// crate never names the `xark_client` cfg itself). Used by `#[input]` on an `impl`.
#[cfg(xark_client)]
#[doc(hidden)]
#[macro_export]
macro_rules! __client_export {
    ($($item:item)*) => { $($item)* };
}

#[cfg(not(xark_client))]
#[doc(hidden)]
#[macro_export]
macro_rules! __client_export {
    ($($item:item)*) => {};
}

/// The items that use the prover (`#[circuit]`'s validator), in every host build
/// but the client build, which has no prover. Used by `#[circuit]`.
#[cfg(not(xark_client))]
#[doc(hidden)]
#[macro_export]
macro_rules! __with_prover {
    ($($item:item)*) => { $($item)* };
}

#[cfg(xark_client)]
#[doc(hidden)]
#[macro_export]
macro_rules! __with_prover {
    ($($item:item)*) => {};
}

/// ISO 3166-1 [`Country`] codes.
pub mod country;
pub use country::Country;

pub mod intrinsics;

/// The stable-frontend circuit build (`--cfg xark` on `wasm32`): the `xark.*` imports
/// the intrinsics and [`input`]'s binding call, and the runtime.
#[cfg(all(xark, target_arch = "wasm32"))]
#[doc(hidden)]
pub mod wasm;

/// The everyday circuit-author surface. `use xark::prelude::*;`.
pub mod prelude {
    pub use crate::lang::{
        Field, Private, Public, require, require_eq, require_ge, require_gt, require_le,
        require_lt, require_ne, witness_begin, witness_end,
    };
    // `#[input]` makes a struct a circuit input (`Input`), an enum a
    // `Choice`/`Bitfield` of variants (`Enum`), and an `impl` block's methods client
    // functions; `circuit` is the entry attribute.
    pub use crate::country::Country;
    pub use crate::input::{Enum, Input};
    pub use crate::types::{Bitfield, Choice, Date, Text};
    pub use xark_macros::{circuit, input};
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

/// The natural encoding length of a value held in `limbs` × `bits`-bit limbs: 32
/// bytes for a field-sized value (up to 264 bits of limbs, e.g. 3 × 86: the value
/// itself is below 2²⁵⁶), else the limbs' bits rounded up to bytes.
#[doc(hidden)]
pub const fn natural_bytes(limbs: usize, bits: usize) -> usize {
    if limbs * bits <= 264 {
        32
    } else {
        (limbs * bits).div_ceil(8)
    }
}
/// The host-side prover: load a built circuit and `check` / `prove` inputs
/// against it (`xark::prover::circuit("name").prove(inputs)`). Host builds only,
/// and not the client build (`client.wasm`), which never proves.
#[cfg(all(not(xark), not(xark_client)))]
pub use xark_prover as prover;
// Host-side helpers for building input values (gadgets' `From` impls, derives).
#[cfg(not(xark))]
#[doc(hidden)]
pub mod host;
#[doc(hidden)]
pub use crate::lang::bytes_to_fields;
// The recognized scalar-equality intrinsic every `RequireEqCircuit` impl bottoms
// out at — re-exported (doc-hidden) so the compiler's intrinsic scan finds it by
// name. Authors never touch it; they write `require_eq`.
#[doc(hidden)]
pub use crate::lang::__xark_require_eq_scalar;
// `#[input]`: `xark::Input` for a struct (its fields in order; with
// `#[input(number(bits = B))]` or `#[input(bytes)]` a standard encoding and its host
// conversions), `xark::Enum` for a fieldless enum, client functions for an `impl`.
// (The attribute shares its name with the `input` module: macros have their own
// namespace.)
pub use xark_macros::{circuit, input};
