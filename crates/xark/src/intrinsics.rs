//! Compiler intrinsics: the ABI between circuit library code and the `xark`
//! compiler.
//!
//! # What an intrinsic *is*
//!
//! An intrinsic is a plain `#[inline(never)]` function whose body is `loop {}`
//! and is **never executed**. It exists only as a marker the compiler
//! recognizes: [`build_call_registry`] (in `lower_mir.rs`) enumerates this
//! module's functions and maps each `__xark_*` stub — by its exact name, against
//! this known module — to a [`KnownCall`] variant, producing a `DefId → KnownCall`
//! table. [`classify_call`] is then an exact `DefId` lookup, and `lower_call` has
//! one arm per variant that emits the real R1CS / witness-generation effect.
//! Compilation stops after MIR extraction, so the `loop {}` never runs — it is
//! just the intended shape of an unreachable marker.
//!
//! Recognition is by `DefId`, resolved once from this module, so a `__xark_*`
//! stub must keep its exact name (the registry keys on it) but may move modules
//! freely. These functions live here (rather than inline in `lang.rs`) purely to
//! gather the compiler ABI in one documented place; `lang.rs`'s `Field` operator
//! impls and `hint_*` methods call them via `use crate::intrinsics::*`, and the
//! compiler reaches the intrinsic by *inlining* those thin wrappers.
//!
//! [`build_call_registry`]: crate::lower_mir::build_call_registry
//! [`classify_call`]: crate::lower_mir::CallRegistry::classify
//! [`KnownCall`]: crate::lower_mir::KnownCall
//!
//! # Two families
//!
//! **Constraint intrinsics** lower *directly* to R1CS: they emit constraints
//! (and/or fold into a linear combination) that fully define their result. On
//! their own they are sound — the returned wire is pinned by the emitted
//! constraints (or is a pure linear combination of already-pinned wires).
//!
//! **Hint intrinsics** are the "compute out-of-circuit, verify in-circuit"
//! pattern. They allocate a fresh private witness (advice) and record a
//! `WitnessGen` step (see `crates/xark-ir/src/solver.rs`) so the *solver* can
//! compute the value natively (an inverse, a bit, a division, a non-native
//! reduction). The emitted advice is **unconstrained on its own**: the *caller*
//! must add the constraints that pin it (e.g. `hint_inverse(x)` returns `w`, and
//! the caller must assert `x·w == 1`). The typed `Field::…` wrappers in
//! `lang.rs` (`inv`, `to_bits`, `Bignum::mul`, …) are the safe forms that pair
//! each hint with its pinning constraints.

// The intrinsic stubs below are recognized by the compiler by name and never
// run; their `loop {}` bodies are the intended marker shape.
#![allow(clippy::empty_loop)]

use crate::lang::Field;

// ---------------------------------------------------------------------------
// Constraint intrinsics — lower directly to R1CS.
// ---------------------------------------------------------------------------

/// Field addition `a + b`. Maps to [`KnownCall::Add`]; lowers to the linear
/// combination `a + b` with **no constraint**.
///
/// [`KnownCall::Add`]: crate::lower_mir::KnownCall::Add
#[inline(never)]
pub fn __xark_add(_lhs: Field, _rhs: Field) -> Field {
    loop {}
}

/// Field subtraction `a - b`. Maps to [`KnownCall::Sub`]; lowers to the linear
/// combination `a - b` with **no constraint**.
///
/// [`KnownCall::Sub`]: crate::lower_mir::KnownCall::Sub
#[inline(never)]
pub fn __xark_sub(_lhs: Field, _rhs: Field) -> Field {
    loop {}
}

/// Field multiplication `a · b`. Maps to [`KnownCall::Mul`]. Emits **one** R1CS
/// constraint `a · b = t` and returns the fresh internal variable `t`. If either
/// operand is a compile-time constant the product is linear and folds into the
/// coefficients instead (no constraint, no fresh variable).
///
/// [`KnownCall::Mul`]: crate::lower_mir::KnownCall::Mul
#[inline(never)]
pub fn __xark_mul(_lhs: Field, _rhs: Field) -> Field {
    loop {}
}

/// Field negation `-a`. Maps to [`KnownCall::Neg`]; lowers to the linear
/// combination `-a` with **no constraint**.
///
/// [`KnownCall::Neg`]: crate::lower_mir::KnownCall::Neg
#[inline(never)]
pub fn __xark_neg(_value: Field) -> Field {
    loop {}
}

/// Exponentiation `base^n` for a compile-time `n`. Maps to
/// [`KnownCall::PowU64`]; lowers to repeated multiplications by
/// exponentiation-by-squaring (special-cased `n = 0,1,2,3`), so roughly
/// `⌊log₂ n⌋ + popcount(n) − 1` multiplication constraints. Backs the `^`
/// operator (`BitXor<u64>`) on `Field`.
///
/// [`KnownCall::PowU64`]: crate::lower_mir::KnownCall::PowU64
#[inline(never)]
pub fn __xark_pow_u64(_base: Field, _exponent: u64) -> Field {
    loop {}
}

/// Boolean XOR for `a, b ∈ {0, 1}`. Maps to [`KnownCall::Xor`]; lowers to a
/// single fused constraint `(2a) · b = a + b − c`, returning the fresh variable
/// `c = a + b − 2ab`. Assumes booleanity of the operands (unchecked here).
///
/// [`KnownCall::Xor`]: crate::lower_mir::KnownCall::Xor
#[inline(never)]
pub fn __xark_xor(_a: Field, _b: Field) -> Field {
    loop {}
}

/// Boolean OR for `a, b ∈ {0, 1}`. Maps to [`KnownCall::Or`]; lowers to a single
/// constraint `a · b = a + b − c`, returning the fresh variable `c = a + b − ab`.
/// Assumes booleanity of the operands.
///
/// [`KnownCall::Or`]: crate::lower_mir::KnownCall::Or
#[inline(never)]
pub fn __xark_or(_a: Field, _b: Field) -> Field {
    loop {}
}

/// Field equality: returns a `bool` (`{0,1}` wire) that is `1` iff `a == b`.
/// Maps to [`KnownCall::Eq`]; lowers via the equality-to-zero gadget on `a − b`
/// (an inverse-or-zero hint plus two multiplication constraints and an equality
/// constraint). Width-independent — no range check. Backs `PartialEq` on
/// `Field`.
///
/// [`KnownCall::Eq`]: crate::lower_mir::KnownCall::Eq
#[inline(never)]
pub fn __xark_eq(_a: Field, _b: Field) -> bool {
    loop {}
}

/// Unsigned less-than: `a < b` for `a, b ∈ [0, 2^N)`, as a `bool` (`{0,1}` wire).
/// Maps to [`KnownCall::ULt`]; lowers with the borrow-bit trick plus an `N`-bit
/// range proof (`top = bitₙ(a − b + 2ⁿ)`, `lt = 1 − top`). **Assumes the
/// operands are already `< 2^N`** — the caller (e.g. `Field::lt`,
/// `PartialOrd<uN>`) must range-check the witness operands first. Rejects
/// `N > 252` (so `2^(N+1)` stays below the BN254 field order).
///
/// [`KnownCall::ULt`]: crate::lower_mir::KnownCall::ULt
#[inline(never)]
pub fn __xark_ult<const N: usize>(_a: Field, _b: Field) -> bool {
    loop {}
}

/// Reinterpret a `bool` (`{0,1}`) wire as a `Field` wire. Maps to
/// [`KnownCall::BoolToField`]; lowers to the **identity** (the same variable),
/// emitting **zero constraints** — a `bool` already *is* a `{0,1}` field wire.
/// Backs `From<bool> for Field`.
///
/// [`KnownCall::BoolToField`]: crate::lower_mir::KnownCall::BoolToField
#[inline(never)]
pub fn __xark_bool_to_field(_b: bool) -> Field {
    loop {}
}

// ---------------------------------------------------------------------------
// Hint intrinsics — the solver computes the value; the CALLER must pin it.
// ---------------------------------------------------------------------------

/// Allocate a fresh private-witness (advice) variable with **no** witness-gen
/// hint. Maps to [`KnownCall::Advice`]. The value is prover-supplied and the
/// emitted witness-generation program cannot compute it, so the gadget author
/// must fully constrain it. Prefer the typed `__xark_hint_*` forms, which also
/// record how to compute the value.
///
/// [`KnownCall::Advice`]: crate::lower_mir::KnownCall::Advice
#[inline(never)]
pub fn __xark_advice() -> Field {
    loop {}
}

/// Advice hint: the solver computes `x⁻¹` (mapping `0 → 0`). Maps to
/// [`KnownCall::HintInverse`]; allocates advice + records an inverse witness-gen
/// step. **Unconstrained** — the caller must pin `x · w == 1` (see `Field::inv`).
///
/// [`KnownCall::HintInverse`]: crate::lower_mir::KnownCall::HintInverse
#[inline(never)]
pub fn __xark_hint_inverse(_x: Field) -> Field {
    loop {}
}

/// Advice hint: `x⁻¹` if `x != 0`, else `0`. Maps to
/// [`KnownCall::HintInverseOrZero`]; allocates advice + records an
/// inverse-or-zero witness-gen step. Backs the `is_zero` / `__xark_eq` gadget;
/// the caller supplies the pinning constraints (`x · w == 0` at zero).
///
/// [`KnownCall::HintInverseOrZero`]: crate::lower_mir::KnownCall::HintInverseOrZero
#[inline(never)]
pub fn __xark_hint_inverse_or_zero(_x: Field) -> Field {
    loop {}
}

/// Advice hint: the solver extracts bit `index` of `x`. Maps to
/// [`KnownCall::HintBit`]; allocates advice + records a bit-extraction
/// witness-gen step. **Unconstrained** — the caller must pin it via a
/// booleanity check and a recomposition constraint (see `Field::to_bits`).
///
/// [`KnownCall::HintBit`]: crate::lower_mir::KnownCall::HintBit
#[inline(never)]
pub fn __xark_hint_bit(_x: Field, _index: usize) -> Field {
    loop {}
}

/// Advice hint: integer division `[q, r]` with `a = b·q + r`, `0 ≤ r < b`. Maps
/// to [`KnownCall::HintDivRem`]; allocates two advice variables + records a
/// div/rem witness-gen step, returned as a two-element array. **Unconstrained**
/// — the caller must pin `b·q + r == a` and range-check `r < b` (see
/// `Field::hint_div_rem` / the `Rem` impls).
///
/// [`KnownCall::HintDivRem`]: crate::lower_mir::KnownCall::HintDivRem
#[inline(never)]
pub fn __xark_hint_div_rem(_a: Field, _b: Field) -> [Field; 2] {
    loop {}
}

/// Non-native multiply-reduce hint over `N` little-endian `bits`-bit limbs (the
/// width-generic `Bignum` form). Maps to [`KnownCall::HintMulModDivMod`];
/// allocates `2N` advice variables + records a mul-mod div/mod witness-gen step.
/// Returns `(q, r)` with `A·B = q·m + r`, `0 ≤ r < m` (each of `A`, `B`, `m`, `q`,
/// `r` recomposed from its limbs). **Unconstrained** — the caller must pin the
/// limb-wise `A·B == q·m + r` identity plus range checks. Backs `xark-bignum`
/// `Bignum::mul`.
///
/// [`KnownCall::HintMulModDivMod`]: crate::lower_mir::KnownCall::HintMulModDivMod
#[inline(never)]
pub fn __xark_hint_mulmod_divmod<const N: usize>(
    _a: [Field; N],
    _b: [Field; N],
    _m: [Field; N],
    _bits: usize,
) -> ([Field; N], [Field; N]) {
    loop {}
}

/// Non-native modular-inverse hint (`N` × `bits`-bit limbs). Maps to
/// [`KnownCall::HintModInverse`]; allocates `N` advice variables + records a
/// Fermat mod-inverse witness-gen step (`A^(m−2) mod m`, `m` prime). Returns
/// `A⁻¹ mod m` as limbs. **Unconstrained** — the caller must pin the non-native
/// `A · A⁻¹ ≡ 1 (mod m)` check.
///
/// [`KnownCall::HintModInverse`]: crate::lower_mir::KnownCall::HintModInverse
#[inline(never)]
pub fn __xark_hint_mod_inverse<const N: usize>(
    _a: [Field; N],
    _m: [Field; N],
    _bits: usize,
) -> [Field; N] {
    loop {}
}

/// Non-native fused-subtract borrow hint (`N` × `bits`-bit limbs), for
/// `(a − b − c) mod m`. Maps to [`KnownCall::HintSub2`]; allocates one advice
/// `qabs` plus `N` advice remainder limbs + records a sub2 witness-gen step.
/// Returns `(qabs, r)` where `r = (a − b − c) mod m` and `qabs ∈ {0,1,2}` is the
/// borrow such that `a + qabs·m == b + c + r` (the solver computes
/// `s = a + 2m − b − c`, `r = s mod m`, `qabs = 2 − s/m`). **Unconstrained** —
/// the caller pins the limb-wise identity + range checks.
///
/// [`KnownCall::HintSub2`]: crate::lower_mir::KnownCall::HintSub2
#[inline(never)]
pub fn __xark_hint_sub2<const N: usize>(
    _a: [Field; N],
    _b: [Field; N],
    _c: [Field; N],
    _m: [Field; N],
    _bits: usize,
) -> (Field, [Field; N]) {
    loop {}
}
