//! Compiler intrinsics: the ABI between circuit library code and the `xark`
//! compiler.
//!
//! An intrinsic is a plain `#[inline(never)]` function. In the circuit build (`xark`
//! on `wasm32`) its body calls the matching `xark.*` wasm import, which the frontend
//! (`xark-frontend`'s `host.rs`) turns into the real R1CS / witness-gen effect. In a
//! host build it computes the value natively (its `native` module), exactly as the solver
//! would, so circuit code (a gadget, a helper such as a commitment, a whole
//! `#[circuit]` body) also runs as plain Rust in tests and services, and a failed
//! `require` panics there. `lang.rs` wrappers reach it via inlining.
//!
//! Two families:
//! - **Constraint intrinsics** lower *directly* to R1CS: they emit constraints
//!   that fully define their result, so they are sound on their own.
//! - **Hint intrinsics** ("compute out-of-circuit, verify in-circuit") allocate
//!   fresh advice and record a `WitnessGen` step so the solver can compute the
//!   value. The advice is **unconstrained on its own** — the *caller* must add
//!   the pinning constraints (e.g. `hint_inverse(x)` returns `w`; caller requires
//!   `x·w == 1`). The typed `Field::…` wrappers in `lang.rs` are the safe forms.

// The circuit-build marker body is `loop {}` (never executed); this allow justifies it.
#![allow(clippy::empty_loop)]

use crate::lang::Field;

/// An intrinsic's body: `circuit_op!(circuit, host)` is the `xark.*` import call
/// in the circuit build (`xark` on `wasm32`) and the native computation in a host
/// build. Each arm is dropped unexpanded where it doesn't apply, so `crate::wasm`
/// only has to exist in the wasm build and `native` only on the host. (`xark`
/// off `wasm32`, an editor's check, gets the marker.)
#[cfg(all(xark, target_arch = "wasm32"))]
macro_rules! circuit_op {
    ($e:expr, $host:expr) => {
        $e
    };
}
#[cfg(not(xark))]
macro_rules! circuit_op {
    ($e:expr, $host:expr) => {
        $host
    };
}
#[cfg(all(xark, not(target_arch = "wasm32")))]
macro_rules! circuit_op {
    ($e:expr, $host:expr) => {
        __xark_marker()
    };
}

/// The body of a circuit-only operation. In a circuit build (`cfg(xark)`) it is never
/// executed: the compiler replaces each call by name, so `loop {}` is just a
/// placeholder. In a host build it panics with an explanation; only operations with
/// no host value (hint-less [`__xark_advice`]) reach it there.
#[cfg(xark)]
#[doc(hidden)]
#[inline(always)]
pub fn __xark_marker() -> ! {
    loop {}
}

#[cfg(not(xark))]
#[doc(hidden)]
#[cold]
#[inline(never)]
pub fn __xark_marker() -> ! {
    panic!(
        "xark: `Field::advice()` has no value outside a circuit: it is a prover-supplied \
         witness with no hint to compute it. Use a `hint_*` (which records how to compute \
         the value), or check the circuit through `xark_prover` (the `#[circuit]` fn's \
         host form does this)."
    )
}

// Constraint intrinsics — lower directly to R1CS.

/// Field addition `a + b`; lowers to the linear combination `a + b`, no constraint.
#[inline(never)]
pub fn __xark_add(_lhs: Field, _rhs: Field) -> Field {
    circuit_op!(
        crate::wasm::add(_lhs, _rhs),
        native::field(native::fr(_lhs) + native::fr(_rhs))
    )
}

/// Field subtraction `a - b`. Lowers to the linear
/// combination `a - b` with **no constraint**.
#[inline(never)]
pub fn __xark_sub(_lhs: Field, _rhs: Field) -> Field {
    circuit_op!(
        crate::wasm::sub(_lhs, _rhs),
        native::field(native::fr(_lhs) - native::fr(_rhs))
    )
}

/// Field multiplication `a · b`. Emits **one** R1CS
/// constraint `a · b = t` and returns the fresh internal variable `t`. If either
/// operand is a compile-time constant the product is linear and folds into the
/// coefficients instead (no constraint, no fresh variable).
#[inline(never)]
pub fn __xark_mul(_lhs: Field, _rhs: Field) -> Field {
    circuit_op!(
        crate::wasm::mul(_lhs, _rhs),
        native::field(native::fr(_lhs) * native::fr(_rhs))
    )
}

/// Field negation `-a`. Lowers to the linear
/// combination `-a` with **no constraint**.
#[inline(never)]
pub fn __xark_neg(_value: Field) -> Field {
    circuit_op!(crate::wasm::neg(_value), native::field(-native::fr(_value)))
}

/// Exponentiation `base.pow(n)` for a compile-time `n`. Lowers to repeated multiplications by
/// exponentiation-by-squaring (special-cased `n = 0,1,2,3`), so roughly
/// `⌊log₂ n⌋ + popcount(n) − 1` multiplication constraints. Backs the
/// [`Field::pow`](crate::Field::pow) method (the `^` operator now means XOR).
#[inline(never)]
pub fn __xark_pow_u64(_base: Field, _exponent: u64) -> Field {
    circuit_op!(
        crate::wasm::pow_u64(_base, _exponent),
        native::pow(_base, _exponent)
    )
}

/// Boolean XOR for `a, b ∈ {0, 1}`. Lowers to a
/// single fused constraint `(2a) · b = a + b − c`, returning the fresh variable
/// `c = a + b − 2ab`. Assumes booleanity of the operands (unchecked here).
#[inline(never)]
pub fn __xark_xor(_a: Field, _b: Field) -> Field {
    circuit_op!(crate::wasm::xor(_a, _b), native::xor(_a, _b))
}

/// Boolean OR for `a, b ∈ {0, 1}`. Lowers to a single
/// constraint `a · b = a + b − c`, returning the fresh variable `c = a + b − ab`.
/// Assumes booleanity of the operands.
#[inline(never)]
pub fn __xark_or(_a: Field, _b: Field) -> Field {
    circuit_op!(crate::wasm::or(_a, _b), native::or(_a, _b))
}

/// Field equality: returns a `bool` (`{0,1}` wire) that is `1` iff `a == b`.
/// lowers via the equality-to-zero gadget on `a − b`
/// (an inverse-or-zero hint plus two multiplication constraints and an equality
/// constraint). Width-independent — no range check. Backs `PartialEq` on
/// `Field`.
#[inline(never)]
pub fn __xark_eq(_a: Field, _b: Field) -> bool {
    circuit_op!(crate::wasm::eq(_a, _b), native::fr(_a) == native::fr(_b))
}

/// Unsigned less-than: `a < b` for `a, b ∈ [0, 2^N)`, as a `bool` (`{0,1}` wire).
/// lowers with the borrow-bit trick plus an `N`-bit
/// range proof (`top = bitₙ(a − b + 2ⁿ)`, `lt = 1 − top`). **Assumes the
/// operands are already `< 2^N`** — the caller (e.g. `Field::lt`,
/// `PartialOrd<uN>`) must range-check the witness operands first. Rejects
/// `N > 252` (so `2^(N+1)` stays below the BN254 field order).
#[inline(never)]
pub fn __xark_ult<const N: usize>(_a: Field, _b: Field) -> bool {
    circuit_op!(
        crate::wasm::ult::<N>(_a, _b),
        native::big(_a) < native::big(_b)
    )
}

/// Reinterpret a `bool` (`{0,1}`) wire as a `Field` wire. Lowers to the **identity** (the same variable),
/// emitting **zero constraints** — a `bool` already *is* a `{0,1}` field wire.
/// Backs `From<bool> for Field`.
#[inline(never)]
pub fn __xark_bool_to_field(_b: bool) -> Field {
    circuit_op!(crate::wasm::bool_to_field(_b), Field::from_u64(_b as u64))
}

// ---------------------------------------------------------------------------
// Hint intrinsics — the solver computes the value; the CALLER must pin it.
// ---------------------------------------------------------------------------

/// Allocate a fresh private-witness (advice) variable with **no** witness-gen
/// hint. The value is prover-supplied and the
/// emitted witness-generation program cannot compute it, so the gadget author
/// must fully constrain it. Prefer the typed `__xark_hint_*` forms, which also
/// record how to compute the value.
#[inline(never)]
pub fn __xark_advice() -> Field {
    circuit_op!(crate::wasm::advice(), __xark_marker())
}

/// Advice hint: the solver computes `x⁻¹` (mapping `0 → 0`). Allocates advice + records an inverse witness-gen
/// step. **Unconstrained** — the caller must pin `x · w == 1` (see `Field::inv`).
#[inline(never)]
pub fn __xark_hint_inverse(_x: Field) -> Field {
    circuit_op!(crate::wasm::hint_inverse(_x), native::inverse_or_zero(_x))
}

/// Advice hint: `x⁻¹` if `x != 0`, else `0`. Allocates advice + records an
/// inverse-or-zero witness-gen step. Backs the `is_zero` / `__xark_eq` gadget;
/// the caller supplies the pinning constraints (`x · w == 0` at zero).
#[inline(never)]
pub fn __xark_hint_inverse_or_zero(_x: Field) -> Field {
    circuit_op!(
        crate::wasm::hint_inverse_or_zero(_x),
        native::inverse_or_zero(_x)
    )
}

/// Advice hint: the solver extracts bit `index` of `x`. Allocates advice + records a bit-extraction
/// witness-gen step. **Unconstrained** — the caller must pin it via a
/// booleanity check and a recomposition constraint (see `Field::to_bits`).
#[inline(never)]
pub fn __xark_hint_bit(_x: Field, _index: usize) -> Field {
    circuit_op!(
        crate::wasm::hint_bit(_x, _index),
        Field::from_u64(native::big(_x).bit(_index as u64) as u64)
    )
}

/// Advice hint: integer division `[q, r]` with `a = b·q + r`, `0 ≤ r < b`.
/// Allocates two advice variables + records a
/// div/rem witness-gen step, returned as a two-element array. **Unconstrained**
/// — the caller must pin `b·q + r == a` and range-check `r < b` (see
/// `Field::hint_div_rem` / the `Rem` impls).
#[inline(never)]
pub fn __xark_hint_div_rem(_a: Field, _b: Field) -> [Field; 2] {
    circuit_op!(crate::wasm::hint_div_rem(_a, _b), native::div_rem(_a, _b))
}

/// Non-native multiply-reduce hint over `N` little-endian `bits`-bit limbs (the
/// width-generic `Bignum` form).
/// allocates `2N` advice variables + records a mul-mod div/mod witness-gen step.
/// Returns `(q, r)` with `A·B = q·m + r`, `0 ≤ r < m` (each of `A`, `B`, `m`, `q`,
/// `r` recomposed from its limbs). **Unconstrained** — the caller must pin the
/// limb-wise `A·B == q·m + r` identity plus range checks. Backs `xark-bignum`
/// `Bignum::mul`.
#[inline(never)]
pub fn __xark_hint_mulmod_divmod<const N: usize>(
    _a: [Field; N],
    _b: [Field; N],
    _m: [Field; N],
    _bits: usize,
) -> ([Field; N], [Field; N]) {
    circuit_op!(
        crate::wasm::hint_mulmod_divmod::<N>(_a, _b, _m, _bits),
        native::mulmod_divmod(_a, _b, _m, _bits)
    )
}

/// Non-native modular-inverse hint (`N` × `bits`-bit limbs). Allocates `N` advice variables + records a
/// Fermat mod-inverse witness-gen step (`A^(m−2) mod m`, `m` prime). Returns
/// `A⁻¹ mod m` as limbs. **Unconstrained** — the caller must pin the non-native
/// `A · A⁻¹ ≡ 1 (mod m)` check.
#[inline(never)]
pub fn __xark_hint_mod_inverse<const N: usize>(
    _a: [Field; N],
    _m: [Field; N],
    _bits: usize,
) -> [Field; N] {
    circuit_op!(
        crate::wasm::hint_mod_inverse::<N>(_a, _m, _bits),
        native::mod_inverse(_a, _m, _bits)
    )
}

/// Non-native fused-subtract borrow hint (`N` × `bits`-bit limbs), for
/// `(a − b − c) mod m`. Allocates one advice
/// `qabs` plus `N` advice remainder limbs + records a sub2 witness-gen step.
/// Returns `(qabs, r)` where `r = (a − b − c) mod m` and `qabs ∈ {0,1,2}` is the
/// borrow such that `a + qabs·m == b + c + r` (the solver computes
/// `s = a + 2m − b − c`, `r = s mod m`, `qabs = 2 − s/m`). **Unconstrained** —
/// the caller pins the limb-wise identity + range checks.
#[inline(never)]
pub fn __xark_hint_sub2<const N: usize>(
    _a: [Field; N],
    _b: [Field; N],
    _c: [Field; N],
    _m: [Field; N],
    _bits: usize,
) -> (Field, [Field; N]) {
    circuit_op!(
        crate::wasm::hint_sub2::<N>(_a, _b, _c, _m, _bits),
        native::sub2(_a, _b, _c, _m, _bits)
    )
}

/// The host bodies of the intrinsics: BN254 arithmetic on a `Field`'s value, and each
/// hint computed exactly as the solver computes it (`xark_ir::solver`), so circuit
/// code run natively gets the values a proof would.
#[cfg(not(xark))]
pub(crate) mod native {
    use super::Field;
    use alloc::vec::Vec;
    use ark_bn254::Fr;
    use ark_ff::{BigInteger, Field as _, PrimeField};
    use num_bigint::BigUint;

    pub fn fr(f: Field) -> Fr {
        f.into()
    }

    pub fn field(x: Fr) -> Field {
        x.into()
    }

    /// The value as an integer in `[0, p)`.
    pub fn big(f: Field) -> BigUint {
        BigUint::from_bytes_le(&fr(f).into_bigint().to_bytes_le())
    }

    fn from_big(n: &BigUint) -> Field {
        field(Fr::from_le_bytes_mod_order(&n.to_bytes_le()))
    }

    pub fn pow(base: Field, exp: u64) -> Field {
        field(fr(base).pow([exp]))
    }

    pub fn xor(a: Field, b: Field) -> Field {
        let (a, b) = (fr(a), fr(b));
        let ab = a * b;
        field(a + b - ab - ab)
    }

    pub fn or(a: Field, b: Field) -> Field {
        let (a, b) = (fr(a), fr(b));
        field(a + b - a * b)
    }

    /// `x⁻¹`, or `0` at `0` (the solver's convention for both inverse hints).
    pub fn inverse_or_zero(x: Field) -> Field {
        field(fr(x).inverse().unwrap_or_default())
    }

    /// Integer division of the values' representatives in `[0, p)`.
    pub fn div_rem(a: Field, b: Field) -> [Field; 2] {
        let (a, b) = (big(a), big(b));
        assert!(b != BigUint::ZERO, "xark: division by zero");
        [from_big(&(&a / &b)), from_big(&(&a % &b))]
    }

    /// `limbs` (little-endian, `bits` each) as one integer.
    fn join<const N: usize>(limbs: [Field; N], bits: usize) -> BigUint {
        limbs
            .iter()
            .enumerate()
            .fold(BigUint::ZERO, |acc, (i, l)| acc + (big(*l) << (bits * i)))
    }

    /// `n` as `N` little-endian `bits`-bit limbs (higher bits dropped, as the solver does).
    fn split<const N: usize>(n: &BigUint, bits: usize) -> [Field; N] {
        let mask = (BigUint::from(1u8) << bits) - 1u8;
        core::array::from_fn(|i| from_big(&((n >> (bits * i)) & &mask)))
    }

    pub fn mulmod_divmod<const N: usize>(
        a: [Field; N],
        b: [Field; N],
        m: [Field; N],
        bits: usize,
    ) -> ([Field; N], [Field; N]) {
        let m = join(m, bits);
        assert!(m != BigUint::ZERO, "xark: mulmod by a zero modulus");
        let p = join(a, bits) * join(b, bits);
        (split(&(&p / &m), bits), split(&(&p % &m), bits))
    }

    pub fn mod_inverse<const N: usize>(a: [Field; N], m: [Field; N], bits: usize) -> [Field; N] {
        let m = join(m, bits);
        assert!(m >= BigUint::from(2u8), "xark: mod_inverse: modulus < 2");
        let a = join(a, bits) % &m;
        assert!(a != BigUint::ZERO, "xark: mod_inverse of zero");
        split(&a.modpow(&(&m - 2u8), &m), bits)
    }

    pub fn sub2<const N: usize>(
        a: [Field; N],
        b: [Field; N],
        c: [Field; N],
        m: [Field; N],
        bits: usize,
    ) -> (Field, [Field; N]) {
        let m = join(m, bits);
        assert!(m != BigUint::ZERO, "xark: sub2 by a zero modulus");
        let (lhs, rhs) = (join(a, bits) + &m + &m, join(b, bits) + join(c, bits));
        assert!(lhs >= rhs, "xark: sub2: a + 2m < b + c");
        let s = lhs - rhs;
        let q: Vec<u64> = (&s / &m).to_u64_digits();
        assert!(
            q.len() <= 1 && q.first().is_none_or(|q| *q <= 2),
            "xark: sub2: inputs >= modulus"
        );
        let q = q.first().copied().unwrap_or(0);
        (Field::from_u64(2 - q), split(&(&s % &m), bits))
    }

    std::thread_local! {
        /// Open [`crate::witness_begin`] regions on this thread: their `require`s aren't
        /// constraints in a circuit, so they aren't checked here either.
        static WITNESS_ONLY: core::cell::Cell<u32> = const { core::cell::Cell::new(0) };
    }

    pub fn witness_begin() {
        WITNESS_ONLY.with(|d| d.set(d.get() + 1));
    }

    pub fn witness_end() {
        WITNESS_ONLY.with(|d| d.set(d.get().saturating_sub(1)));
    }

    /// A `require_eq` run natively: values that fail it are values the circuit
    /// rejects, so this panics, at the `require` the circuit code wrote.
    #[track_caller]
    pub fn require_eq(a: Field, b: Field) {
        if a != b && WITNESS_ONLY.with(|d| d.get()) == 0 {
            panic!("xark: requirement failed: {a:?} != {b:?} (the circuit rejects these values)");
        }
    }

    /// [`require_eq`] for `require(cond)`.
    #[track_caller]
    pub fn require(cond: bool) {
        if !cond && WITNESS_ONLY.with(|d| d.get()) == 0 {
            panic!("xark: requirement failed (the circuit rejects these values)");
        }
    }
}
