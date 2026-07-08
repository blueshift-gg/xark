//! The `xark` language markers used by circuit programs (formerly the
//! standalone `xark-lang` crate, now merged into `xark`).
//!
//! It defines the `Field` circuit type, the `Private`/`Public` visibility
//! aliases, and a set of `#[inline(never)]` marker/intrinsic functions that the
//! `xark` compiler recognizes in MIR. None of these functions are ever
//! actually executed: the compiler stops after MIR extraction, so their bodies
//! are irrelevant (`loop {}`).

// The intrinsic stubs below are recognized by the compiler by name and never
// run; their `loop {}` bodies are the intended marker shape.
#![allow(clippy::empty_loop)]
// `to_bits`/`from_bits` are circuit-lowered: the compiler rejects compound
// assignment on `Field`, so `acc = acc + …` is required, not `acc += …`.
#![allow(clippy::assign_op_pattern)]

use core::marker::PhantomData;
use core::ops::{
    Add, AddAssign, BitXor, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign,
};

/// The opaque circuit field element.
///
/// It carries a private non-zero-sized payload so that (a) it cannot be
/// constructed by circuit authors except through the recognized intrinsics, and
/// (b) MIR optimization cannot collapse `Field` values to a single constant ZST
/// (which would erase the data-flow the compiler tracks).
///
/// Implements `core::ops` arithmetic (`+ - * /`, unary `-`, `*Assign`, `^`) plus
/// Comparisons (`== != < <= > >=`) are circuit operations: they return a `bool`
/// that is a `{0,1}` field wire (the compiler lowers `PartialEq`/`PartialOrd`),
/// usable in further boolean logic or muxed via [`Field::from`]`(cond)`. For
/// *ordering* on a bounded integer, wrap in [`U<N>`](crate::uint::U) /
/// [`I<N>`](crate::int::I) — a bare `Field` only supports `==`/`!=` (equality);
/// ordering the canonical `[0, r)` representative is rarely intended.
#[derive(Clone, Copy)]
pub struct Field {
    /// Little-endian 4×64-bit value of a *compile-time-constant* field element.
    /// Meaningful only for constants (`Field::from`/`Field::constant`, which are
    /// `const fn`s): the compiler reads this out of a `const Field` value. For
    /// witnesses, inputs and computed values the compiler tracks the value
    /// symbolically and never reads these limbs.
    _limbs: [u64; 4],
}

/// A private witness input. Transparent alias, erased during type checking; the
/// compiler recovers the distinction from the *syntactic* HIR signature.
pub type Private<T> = T;

/// A public input. See [`Private`].
pub type Public<T> = T;

impl Field {
    /// Constant constructor backing `From<u8..u64>` — recognised by the compiler
    /// through the *call* (so circuit bodies keep working) and evaluated for real
    /// in `const` contexts, so `const F: Field = 5u64.into()` is a value.
    const fn constant_u64(value: u64) -> Field {
        Field {
            _limbs: [value, 0, 0, 0],
        }
    }

    /// Constant constructor backing `From<u128>`. See [`Field::constant_u64`].
    const fn constant_u128(value: u128) -> Field {
        Field {
            _limbs: [value as u64, (value >> 64) as u64, 0, 0],
        }
    }

    /// A `const`-context constructor from a `u128` value. Unlike `From<u128>`
    /// (a non-`const` trait method), this is usable in `const` items — it exists
    /// so field-parameter derivation (`xark_ff`'s limb splitting) can build
    /// `[Field; N]` limb arrays at compile time. Not for circuit bodies; use
    /// `Field::from(x)` there.
    #[doc(hidden)]
    pub const fn from_u128(value: u128) -> Field {
        Field {
            _limbs: [value as u64, (value >> 64) as u64, 0, 0],
        }
    }

    /// In-circuit constant from a decimal string, for full field-sized constants
    /// (e.g. round constants) that don't fit a `u128`:
    /// `Field::constant("218882428718...")`. A `const fn`, so it works both in
    /// circuit bodies (recognised by the call) and in `const` items. Parses a
    /// non-negative decimal `< 2^256`; panics (a compile error in `const`
    /// contexts) on a non-digit or overflow.
    pub const fn constant(decimal: &str) -> Field {
        let bytes = decimal.as_bytes();
        let mut limbs = [0u64; 4];
        let mut i = 0;
        while i < bytes.len() {
            let b = bytes[i];
            assert!(
                b'0' <= b && b <= b'9',
                "Field::constant expects a decimal string"
            );
            // limbs = limbs * 10 + (b - '0'), 256-bit little-endian.
            let mut carry = (b - b'0') as u128;
            let mut j = 0;
            while j < 4 {
                let v = limbs[j] as u128 * 10 + carry;
                limbs[j] = v as u64;
                carry = v >> 64;
                j += 1;
            }
            assert!(carry == 0, "Field::constant literal overflows 256 bits");
            i += 1;
        }
        Field { _limbs: limbs }
    }

    /// Allocate a fresh *advice* (private witness) field element with no
    /// witness-generation hint. The circuit must pin it down with `assert_eq`.
    /// Prefer the typed `hint_*` constructors below, which also record how to
    /// compute the value so the emitted IR is self-contained.
    #[inline(never)]
    pub fn advice() -> Field {
        __xark_advice()
    }

    /// Advice hint: `1 / x`. Allocates a private witness and records that its
    /// value is the modular inverse of `x`. Pin it with `x * w == 1`.
    #[inline(never)]
    pub fn hint_inverse(x: Field) -> Field {
        __xark_hint_inverse(x)
    }

    /// Advice hint: `1 / x` if `x != 0`, else `0` (unconstrained at 0).
    #[inline(never)]
    pub fn hint_inverse_or_zero(x: Field) -> Field {
        __xark_hint_inverse_or_zero(x)
    }

    /// Advice hint: the `index`-th least-significant bit of `x`. Allocates a
    /// private witness and records that its value is `bit(x, index)`. Pin it
    /// with a booleanity check and a recomposition constraint.
    #[inline(never)]
    pub fn hint_bit(x: Field, index: usize) -> Field {
        __xark_hint_bit(x, index)
    }

    /// Decompose `self` into `N` little-endian boolean bits. Each bit is pinned
    /// boolean (`b² == b`) and the bits are pinned to recompose to `self`
    /// (`Σ bitᵢ·2ⁱ == self`) — which also proves `self < 2^N`. Composed entirely
    /// from `Field` primitives (`hint_bit` + arithmetic + `assert_eq`).
    pub fn to_bits<const N: usize>(self) -> [Field; N] {
        // N > 253 wraps mod r, so recomposition wouldn't pin `self`
        const {
            assert!(
                N <= 253,
                "to_bits::<N>: N must be <= 253 (BN254 field capacity)"
            )
        };
        let mut bits = [Field::from(0u8); N];
        let mut i = 0usize;
        while i < N {
            bits[i] = Field::hint_bit(self, i); // witness-gen: bits[i] = bit(self, i)
            i += 1;
        }
        let mut i = 0usize;
        while i < N {
            bits[i].assert_bool(); // booleanity: bit ∈ {0, 1}
            i += 1;
        }
        let mut acc = Field::from(0u8);
        let mut pow = Field::from(1u8);
        let mut i = 0usize;
        while i < N {
            acc = acc + bits[i] * pow;
            pow = pow + pow;
            i += 1;
        }
        assert_eq(acc, self); // recomposition pins the bits to `self` (⇒ self < 2^N)
        bits
    }

    /// Recompose `N` little-endian bits into a field element (`Σ bitᵢ·2ⁱ`). Only
    /// forms the linear combination; the caller must have pinned the bits boolean
    /// (e.g. via [`Field::to_bits`]).
    pub fn from_bits<const N: usize>(bits: [Field; N]) -> Field {
        // N > 253: weighted sum can exceed r and wrap
        const {
            assert!(
                N <= 253,
                "from_bits::<N>: N must be <= 253 (BN254 field capacity)"
            )
        };
        let mut acc = Field::from(0u8);
        let mut pow = Field::from(1u8);
        let mut i = 0usize;
        while i < N {
            acc = acc + bits[i] * pow;
            pow = pow + pow;
            i += 1;
        }
        acc
    }

    /// Boolean XOR: for `self, rhs ∈ {0,1}`, returns `self ^ rhs` as a single
    /// constrained variable (one fused R1CS constraint), avoiding the linear-
    /// combination growth of writing `self + rhs - 2*self*rhs` by hand.
    #[inline(never)]
    pub fn xor(self, rhs: Field) -> Field {
        __xark_xor(self, rhs)
    }

    /// Boolean OR: for `self, rhs ∈ {0,1}`, returns `self | rhs` as a single
    /// constrained variable (one fused R1CS constraint).
    #[inline(never)]
    pub fn or(self, rhs: Field) -> Field {
        __xark_or(self, rhs)
    }

    /// Boolean AND: `self · rhs` (for `self, rhs ∈ {0, 1}`).
    pub fn and(self, rhs: Field) -> Field {
        self * rhs
    }

    /// Boolean NOT: `1 − self` (for `self ∈ {0, 1}`).
    // Not the std bitwise `Not`: this is a boolean-domain gadget, kept as a named method.
    #[allow(clippy::should_implement_trait)]
    pub fn not(self) -> Field {
        Field::from(1u8) - self
    }

    /// Assert `self ∈ {0, 1}` — the booleanity constraint `self² == self`.
    pub fn assert_bool(self) {
        assert_eq(self * self, self);
    }

    /// Native modular inverse. Allocates `w = self⁻¹` as advice AND pins it with
    /// `self · w == 1`, so the result is safe-by-default (unlike the raw
    /// [`Field::hint_inverse`], which returns an *unconstrained* witness).
    pub fn inv(self) -> Field {
        let w = Field::hint_inverse(self);
        assert_eq(self * w, Field::from(1u8));
        w
    }

    /// Circuit equality-to-zero: a `bool` (a `{0,1}` wire) that is `true` iff
    /// `self == 0`.
    pub fn is_zero(self) -> bool {
        self == Field::from(0u8)
    }

    /// Advice hint: integer division of `a` by `b` on the canonical
    /// representatives. Returns `[q, r]` with `a = b*q + r`, `0 <= r < b`.
    /// Allocates two private witnesses; pin them with `b*q + r == a` and
    /// `r < b` (a range check).
    #[inline(never)]
    pub fn hint_div_rem(a: Field, b: Field) -> [Field; 2] {
        __xark_hint_div_rem(a, b)
    }

    /// Non-native multiply-reduce hint over `N` little-endian `bits`-bit limbs
    /// (the width-generic `Bignum` form). Returns `(q, r)` with `A·B = q·m + r`,
    /// `0 <= r < m`. Pin with the limb-wise `A·B == q·m + r` check + range
    /// checks. This is what makes non-native field multiplication solvable.
    #[inline(never)]
    pub fn hint_mulmod_divmod<const N: usize>(
        a: [Field; N],
        b: [Field; N],
        m: [Field; N],
        bits: usize,
    ) -> ([Field; N], [Field; N]) {
        __xark_hint_mulmod_divmod(a, b, m, bits)
    }

    /// Non-native modular-inverse hint (`N` × `bits`-bit limbs). Returns
    /// `a⁻¹ mod m`. Pin with a non-native `a · w == 1 (mod m)` check.
    #[inline(never)]
    pub fn hint_mod_inverse<const N: usize>(
        a: [Field; N],
        m: [Field; N],
        bits: usize,
    ) -> [Field; N] {
        __xark_hint_mod_inverse(a, m, bits)
    }

    /// Fused-subtract hint (`N` × `bits`-bit limbs): for `(a - b - c) mod m`,
    /// returns `(qabs, r)` with `r = (a-b-c) mod m` and `qabs ∈ {0,1,2}` such
    /// that `a + qabs·m == b + c + r`.
    #[inline(never)]
    pub fn hint_sub2<const N: usize>(
        a: [Field; N],
        b: [Field; N],
        c: [Field; N],
        m: [Field; N],
        bits: usize,
    ) -> (Field, [Field; N]) {
        __xark_hint_sub2(a, b, c, m, bits)
    }
}

/// Canonical conversions from unsigned integer types (`u8`..`u128`) to in-circuit
/// `Field` constants: `Field::from(x)`. Each routes through an internal constant
/// intrinsic. For constants above `u128` (up to ~254 bits) use [`Field::constant`]
/// with a decimal string (Rust integer literals cap at `u128`).
impl From<u8> for Field {
    fn from(v: u8) -> Field {
        Field::constant_u64(v as u64)
    }
}
impl From<u16> for Field {
    fn from(v: u16) -> Field {
        Field::constant_u64(v as u64)
    }
}
impl From<u32> for Field {
    fn from(v: u32) -> Field {
        Field::constant_u64(v as u64)
    }
}
impl From<u64> for Field {
    fn from(v: u64) -> Field {
        Field::constant_u64(v)
    }
}
impl From<u128> for Field {
    fn from(v: u128) -> Field {
        Field::constant_u128(v)
    }
}
/// Decimal-string constant: `Field::from("218882428718…")` / `"…".into()`, for
/// full field-sized (up to ~254-bit) constants that don't fit in `u128`. The
/// compiler rejects a string with any non-decimal character at compile time.
impl From<&str> for Field {
    fn from(s: &str) -> Field {
        Field::constant(s)
    }
}

/// Circuit equality: `self == other` / `self != other` return a `bool` that is a
/// `{0,1}` field wire (the compiler lowers this to the equality gadget). It is
/// *not* a host comparison — `Field` holds a symbolic witness with no host
/// value, so the derived `PartialEq`/`Eq`/`Hash` were dropped on purpose.
impl PartialEq for Field {
    fn eq(&self, other: &Field) -> bool {
        __xark_eq(*self, *other)
    }
}

/// Reinterpret a circuit `bool` (a `{0,1}` wire) as a `Field` wire, so a
/// comparison result can be used in arithmetic — e.g. a branchless mux
/// `if_false + Field::from(cond) * (if_true - if_false)`. Zero constraints: a
/// `bool` *is* already a `{0,1}` field wire.
impl From<bool> for Field {
    fn from(b: bool) -> Field {
        __xark_bool_to_field(b)
    }
}

impl Add for Field {
    type Output = Field;

    #[inline(never)]
    fn add(self, rhs: Field) -> Field {
        __xark_add(self, rhs)
    }
}

impl Sub for Field {
    type Output = Field;

    #[inline(never)]
    fn sub(self, rhs: Field) -> Field {
        __xark_sub(self, rhs)
    }
}

impl Mul for Field {
    type Output = Field;

    #[inline(never)]
    fn mul(self, rhs: Field) -> Field {
        __xark_mul(self, rhs)
    }
}

impl Neg for Field {
    type Output = Field;

    #[inline(never)]
    fn neg(self) -> Field {
        __xark_neg(self)
    }
}

/// Field division `a / b = a · b⁻¹` (`b` must be nonzero).
impl Div for Field {
    type Output = Field;
    // Field division genuinely is multiply-by-inverse; the `*` here is correct.
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Field) -> Field {
        self * rhs.inv()
    }
}

impl AddAssign for Field {
    fn add_assign(&mut self, rhs: Field) {
        *self = *self + rhs;
    }
}
impl SubAssign for Field {
    fn sub_assign(&mut self, rhs: Field) {
        *self = *self - rhs;
    }
}
impl MulAssign for Field {
    fn mul_assign(&mut self, rhs: Field) {
        *self = *self * rhs;
    }
}
impl DivAssign for Field {
    fn div_assign(&mut self, rhs: Field) {
        *self = *self / rhs;
    }
}

impl BitXor<u64> for Field {
    type Output = Field;

    #[inline(never)]
    fn bitxor(self, rhs: u64) -> Field {
        __xark_pow_u64(self, rhs)
    }
}

/// `Field` arithmetic with a native-integer constant on the right — `a + 1`,
/// `a * 3`, `a - 2` — as sugar for `a op Field::from(n)`. Each forwards to the
/// recognized `Field`-`Field` operator, so it lowers to the exact same R1CS; the
/// integer must be a compile-time constant (a circuit has no runtime integers).
/// (`^` stays the `pow` operator — see [`BitXor<u64>`].)
macro_rules! impl_field_int_ops {
    ($($t:ty),+ $(,)?) => {$(
        impl Add<$t> for Field {
            type Output = Field;
            fn add(self, rhs: $t) -> Field { self + Field::from(rhs) }
        }
        impl Sub<$t> for Field {
            type Output = Field;
            fn sub(self, rhs: $t) -> Field { self - Field::from(rhs) }
        }
        impl Mul<$t> for Field {
            type Output = Field;
            fn mul(self, rhs: $t) -> Field { self * Field::from(rhs) }
        }
        impl Div<$t> for Field {
            type Output = Field;
            fn div(self, rhs: $t) -> Field { self / Field::from(rhs) }
        }
        impl AddAssign<$t> for Field {
            fn add_assign(&mut self, rhs: $t) { *self = *self + rhs; }
        }
        impl SubAssign<$t> for Field {
            fn sub_assign(&mut self, rhs: $t) { *self = *self - rhs; }
        }
        impl MulAssign<$t> for Field {
            fn mul_assign(&mut self, rhs: $t) { *self = *self * rhs; }
        }
        impl DivAssign<$t> for Field {
            fn div_assign(&mut self, rhs: $t) { *self = *self / rhs; }
        }
    )+};
}
impl_field_int_ops!(u8, u16, u32, u64, u128);

/// Emit a circuit equality constraint `lhs == rhs`.
///
/// This is a marker: the compiler lowers it to an R1CS constraint rather than
/// executing it.
#[inline(never)]
pub fn assert_eq(_lhs: Field, _rhs: Field) {
    loop {}
}

#[inline(never)]
pub fn __xark_add(_lhs: Field, _rhs: Field) -> Field {
    loop {}
}

#[inline(never)]
pub fn __xark_sub(_lhs: Field, _rhs: Field) -> Field {
    loop {}
}

#[inline(never)]
pub fn __xark_mul(_lhs: Field, _rhs: Field) -> Field {
    loop {}
}

#[inline(never)]
pub fn __xark_neg(_value: Field) -> Field {
    loop {}
}

#[inline(never)]
pub fn __xark_pow_u64(_base: Field, _exponent: u64) -> Field {
    loop {}
}

#[inline(never)]
pub fn __xark_advice() -> Field {
    loop {}
}

#[inline(never)]
pub fn __xark_hint_inverse(_x: Field) -> Field {
    loop {}
}

#[inline(never)]
pub fn __xark_hint_inverse_or_zero(_x: Field) -> Field {
    loop {}
}

#[inline(never)]
pub fn __xark_hint_bit(_x: Field, _index: usize) -> Field {
    loop {}
}

#[inline(never)]
pub fn __xark_hint_div_rem(_a: Field, _b: Field) -> [Field; 2] {
    loop {}
}

#[inline(never)]
pub fn __xark_xor(_a: Field, _b: Field) -> Field {
    loop {}
}

#[inline(never)]
pub fn __xark_or(_a: Field, _b: Field) -> Field {
    loop {}
}

#[inline(never)]
pub fn __xark_hint_mulmod_divmod<const N: usize>(
    _a: [Field; N],
    _b: [Field; N],
    _m: [Field; N],
    _bits: usize,
) -> ([Field; N], [Field; N]) {
    loop {}
}

#[inline(never)]
pub fn __xark_hint_mod_inverse<const N: usize>(
    _a: [Field; N],
    _m: [Field; N],
    _bits: usize,
) -> [Field; N] {
    loop {}
}

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

// --- comparison intrinsics: return a `bool` that is a `{0,1}` field wire -----
// The compiler lowers these directly (never inlined); they back `PartialEq` /
// `PartialOrd` on `Field` / `U<N>` / `I<N>` so `==` `!=` `<` `<=` `>` `>=` work
// as circuit operations.

/// Field equality: `a == b` as a `bool` wire (`1` iff `a == b`).
#[inline(never)]
pub fn __xark_eq(_a: Field, _b: Field) -> bool {
    loop {}
}

/// Unsigned less-than: `a < b` for `a, b ∈ [0, 2^N)`, as a `bool` wire.
#[inline(never)]
pub fn __xark_ult<const N: usize>(_a: Field, _b: Field) -> bool {
    loop {}
}

/// Signed less-than: `a < b` for `a, b ∈ [−2^(N−1), 2^(N−1))`, as a `bool` wire.
#[inline(never)]
pub fn __xark_ilt<const N: usize>(_a: Field, _b: Field) -> bool {
    loop {}
}

/// Reinterpret a `bool` wire as a `Field` wire (identity — both are `{0,1}`
/// wires). Backs `From<bool> for Field`.
#[inline(never)]
pub fn __xark_bool_to_field(_b: bool) -> Field {
    loop {}
}

/// Reinterpret a `{0,1}` `Field` wire as a `bool` wire (identity). For producers
/// that already pinned a wire boolean (e.g. a cached sign bit) and want to feed
/// it to `bool` operators.
#[inline(never)]
pub fn __xark_field_to_bool(_f: Field) -> bool {
    loop {}
}

// Keep `PhantomData` referenced so `#![no_std]` users pulling only this crate do
// not trip an unused-import lint if they re-export internals. It documents that
// `Field` is intended to be a zero-sized opaque marker.
#[doc(hidden)]
pub type _FieldMarker = PhantomData<Field>;
