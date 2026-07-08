//! `xark-mimc`: a MiMC-structured gadget, written entirely in the `Field`
//! subset, used to exercise the field-arithmetic lowering.
//!
//! ⚠️ **NON-CRYPTOGRAPHIC — DO NOT USE AS A HASH/PRF/COMMITMENT.** This gadget
//! uses S-box exponent 3 and only 3 rounds. Over the BN254 scalar field `x ↦ x³`
//! is **not a permutation** (`3 | r − 1`, so it is 3-to-1), and 3 rounds is far
//! below the ~160+ a real MiMC needs — the construction is neither invertible
//! nor collision-resistant. A production instantiation needs a permutation
//! S-box (`x⁵` — `5 ∤ r − 1` on BN254, as both Poseidon crates use), a proper
//! round count, and nothing-up-my-sleeve round constants (tracked as a follow-up).
//! It exists only as a lowering test vehicle.
//!
//! Circuit authors just `use xark_mimc::mimc3;` — the compiler inlines it, so
//! there is no backend "gadget" handling; it is ordinary library code that
//! lowers to the same constraints as if it were written inline.
//!
//! Build with `-Zalways-encode-mir` so the compiler can read this crate's MIR
//! across the crate boundary (the workspace `.cargo/config.toml` sets this).

#![no_std]

use xark::Field;

/// The MiMC S-box for exponent 3.
fn sbox(x: Field) -> Field {
    x ^ 3
}

/// One MiMC round: `(state + key + round_constant)^3`.
fn round(state: Field, key: Field, c: Field) -> Field {
    sbox(state + key + c)
}

/// A toy 3-round MiMC-structured map keyed by `k`, finalized with a key
/// addition.
///
/// ⚠️ **NON-CRYPTOGRAPHIC** (see the crate-level warning): `x³` is not a
/// permutation over BN254 `Fr` and 3 rounds is far too few — this is not a hash,
/// PRF, or commitment. Round constants are full BN254-field-sized values. This
/// is deliberately unrolled (no loops yet); the structure is what a
/// `#[circuit]`-side loop would expand to.
pub fn mimc3(x: Field, k: Field) -> Field {
    let s = round(x, k, Field::from(0u8));
    let s = round(
        s,
        k,
        Field::from("7120861356467033611736373842526102177239622603558704633600844922174959859415"),
    );
    let s = round(
        s,
        k,
        Field::from("5464731394973421946722394282035800941955447322641943688940765294088180338198"),
    );
    s + k
}
