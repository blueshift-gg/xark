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

use core::cmp::{Ordering, PartialOrd};
use core::marker::PhantomData;
use core::ops::{
    Add, AddAssign, BitXor, Div, DivAssign, Mul, MulAssign, Neg, Rem, Shl, Shr, Sub, SubAssign,
};

// The compiler intrinsics (the `__xark_*` marker stubs) live in `crate::intrinsics`;
// the `Field` impls and `hint_*` methods below call them. Recognition is by name,
// so their module location does not affect the compiler.
use crate::intrinsics::*;

/// The opaque circuit field element.
///
/// It carries a private non-zero-sized payload so that (a) it cannot be
/// constructed by circuit authors except through the recognized intrinsics, and
/// (b) MIR optimization cannot collapse `Field` values to a single constant ZST
/// (which would erase the data-flow the compiler tracks).
///
/// Implements `core::ops` arithmetic (`+ - * /`, unary `-`, `*Assign`, `^`).
///
/// Comparisons are circuit operations that return a `bool` — a `{0,1}` field
/// wire (usable in further boolean logic or muxed via [`Field::from`]`(cond)`):
/// * `==` / `!=` against another `Field` **or** a native-int constant
///   (`PartialEq` / `PartialEq<uN>`) — width-independent equality.
/// * `<` `<=` `>` `>=` against a native-int constant (`PartialOrd<uN>`), whose
///   type fixes the bit-width `N` for the required range check.
/// * two-witness ordering via the explicit-width methods
///   [`Field::lt`]`::<N>` / `gt` / `le` / `ge`.
///
/// A bare `Field` is intentionally **not** `PartialOrd for Field`: ordering the
/// canonical `[0, r)` representative needs a width, so it must come from the RHS
/// type or the `::<N>`. See `docs/integer-ops.md`.
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
    /// so field-parameter derivation (`xark_bignum`'s limb splitting) can build
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

    /// Interpret the stored limbs as a BN254 field element. Native-only: the
    /// bridge between the opaque circuit `Field` and real arithmetic.
    #[cfg(feature = "native")]
    pub(crate) fn to_fr(self) -> ark_bn254::Fr {
        use ark_ff::PrimeField;
        let mut bytes = [0u8; 32];
        let mut i = 0;
        while i < 4 {
            bytes[i * 8..i * 8 + 8].copy_from_slice(&self._limbs[i].to_le_bytes());
            i += 1;
        }
        ark_bn254::Fr::from_le_bytes_mod_order(&bytes)
    }

    /// Store a BN254 field element's canonical representative in the limbs.
    #[cfg(feature = "native")]
    pub(crate) fn from_fr(value: ark_bn254::Fr) -> Field {
        use ark_ff::{BigInteger, PrimeField};
        let bytes = value.into_bigint().to_bytes_le();
        let mut limbs = [0u64; 4];
        for (i, chunk) in bytes.chunks(8).take(4).enumerate() {
            let mut b = [0u8; 8];
            b[..chunk.len()].copy_from_slice(chunk);
            limbs[i] = u64::from_le_bytes(b);
        }
        Field { _limbs: limbs }
    }

    /// The field element's value as a canonical decimal string (native-only).
    /// Lets host code read a computed `Field` — e.g. a commitment from
    /// `xark_poseidon2::hash2` — to feed `xark prove --input` or store on-chain.
    #[cfg(feature = "native")]
    pub fn to_decimal(self) -> String {
        use ark_ff::PrimeField;
        self.to_fr().into_bigint().to_string()
    }

    /// The field element as 32 canonical little-endian bytes — the on-chain /
    /// `xark`-artifact wire format (native-only).
    #[cfg(feature = "native")]
    pub fn to_bytes_le(self) -> [u8; 32] {
        use ark_ff::{BigInteger, PrimeField};
        let mut out = [0u8; 32];
        let bytes = self.to_fr().into_bigint().to_bytes_le();
        out[..bytes.len()].copy_from_slice(&bytes);
        out
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

    // --- Field-vs-Field ordered comparison (explicit width) ------------------
    // The one comparison case with no native-int operand to carry a width, so
    // the width `N` is spelled explicitly: `a.lt::<32>(b)`. Both operands are
    // *witnesses*, so BOTH are range-checked to `< 2^N` via `to_bits::<N>`
    // before the width-`N` unsigned comparison — otherwise a prover could place
    // an out-of-range residue in either wire and defeat the compare. `le`/`ge`
    // delegate to `gt`/`lt` (boolean `!`), inheriting that single pair of range
    // checks. These are inherent methods (not `PartialOrd for Field`): a bare
    // `Field` stays orderless because ordering needs a width (see docs/integer-ops).

    /// `self < rhs` as a `{0,1}` `bool` wire, interpreting both as `N`-bit
    /// unsigned integers (range-checks both to `< 2^N`).
    // Named like `PartialOrd::lt` on purpose: the explicit-width Field-vs-Field form.
    #[allow(clippy::should_implement_trait)]
    pub fn lt<const N: usize>(self, rhs: Field) -> bool {
        let _ = self.to_bits::<N>();
        let _ = rhs.to_bits::<N>();
        __xark_ult::<N>(self, rhs)
    }

    /// `self > rhs` (= `rhs < self`), `N`-bit unsigned. See [`Field::lt`].
    #[allow(clippy::should_implement_trait)]
    pub fn gt<const N: usize>(self, rhs: Field) -> bool {
        let _ = self.to_bits::<N>();
        let _ = rhs.to_bits::<N>();
        __xark_ult::<N>(rhs, self)
    }

    /// `self <= rhs`, `N`-bit unsigned — `!(self > rhs)`. See [`Field::lt`].
    #[allow(clippy::should_implement_trait)]
    pub fn le<const N: usize>(self, rhs: Field) -> bool {
        !self.gt::<N>(rhs)
    }

    /// `self >= rhs`, `N`-bit unsigned — `!(self < rhs)`. See [`Field::lt`].
    #[allow(clippy::should_implement_trait)]
    pub fn ge<const N: usize>(self, rhs: Field) -> bool {
        !self.lt::<N>(rhs)
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

/// Integer comparison of a `Field` against a native-integer *constant*, where the
/// constant's type supplies the domain width `N = bitwidth(T)` (`bool → 1`,
/// `u8 → 8`, …, `u128 → 128`).
///
/// * `x == c` / `x != c` — width-independent equality (`__xark_eq`), **no** range
///   check: equality of residues needs no bounding.
/// * `x < c` / `x <= c` / `x > c` / `x >= c` — ordered comparison. Each first
///   range-checks the *witness* operand `x` to `< 2^N` via `to_bits::<N>` (the
///   soundness contract: a prover holding an out-of-range residue cannot satisfy
///   the decomposition, so the compare can't be defeated), then compares against
///   the compile-time constant `c` (which needs no check — it is known `< 2^N`).
///   `le`/`ge` are `!gt`/`!lt` so they inherit `gt`/`lt`'s single range check.
///
/// The `c < x` mirror is written `x > c`. Two-witness comparison uses the
/// explicit-width [`Field::lt`] etc. See `docs/integer-ops.md`.
macro_rules! impl_field_int_cmp {
    ($($t:ty => $n:literal),+ $(,)?) => {$(
        impl PartialEq<$t> for Field {
            // Equality is width-independent: no range check needed.
            fn eq(&self, rhs: &$t) -> bool {
                __xark_eq(*self, Field::from(*rhs))
            }
            // `ne` uses the default (`!eq`).
        }
        impl PartialOrd<$t> for Field {
            // Never reaches lowering: once `lt`/`le`/`gt`/`ge` are overridden the
            // `<`/`<=`/`>`/`>=` operators call those directly, so `partial_cmp` is
            // never invoked. It exists only to satisfy the trait — a circuit
            // comparison yields a `{0,1}` wire, not a host `Option<Ordering>`.
            fn partial_cmp(&self, _rhs: &$t) -> Option<Ordering> {
                loop {}
            }
            fn lt(&self, rhs: &$t) -> bool {
                let _ = self.to_bits::<$n>(); // range-check the witness operand < 2^N
                __xark_ult::<$n>(*self, Field::from(*rhs))
            }
            fn gt(&self, rhs: &$t) -> bool {
                let _ = self.to_bits::<$n>(); // range-check the witness operand < 2^N
                __xark_ult::<$n>(Field::from(*rhs), *self) // c < x
            }
            fn le(&self, rhs: &$t) -> bool {
                !self.gt(rhs)
            }
            fn ge(&self, rhs: &$t) -> bool {
                !self.lt(rhs)
            }
        }
    )+};
}
impl_field_int_cmp!(bool => 1, u8 => 8, u16 => 16, u32 => 32, u64 => 64, u128 => 128);

/// Integer shifts of a `Field` against a native-integer *constant*, where the
/// constant's type supplies the domain width `N = bitwidth(T)` (`u8 → 8`, …,
/// `u128 → 128`) and its value is the shift amount. So `x >> 3u32` means "treat
/// `x` as a 32-bit value, shift right by 3". `bool` is excluded (a 1-bit domain
/// is degenerate for shifting); signed shifts are out of scope.
///
/// Provided for `u8`..`u128` — all sound: a shift is pure bit re-wiring, and
/// `from_bits::<N>` with `N ≤ 128 ≤ 253` cannot wrap the field.
///
/// Each op first calls `to_bits::<N>(self)`, which range-checks `self < 2^N`
/// (the soundness contract — a prover holding an out-of-domain residue cannot
/// satisfy the decomposition). The shift amount `n` must be a compile-time
/// constant; the compiler const-propagates it at the inline site so the loop
/// bounds, branch conditions, and array indices fold to constants (a non-const
/// amount naturally fails to lower).
///
/// * **`x >> n`** — `⌊x / 2ⁿ⌋` within the `N`-bit domain: place bit `i+n` at
///   position `i`, zero-fill the top. `n ≥ N` → 0. Free re-wiring (just the
///   shared `to_bits::<N>`, then `from_bits::<N>`).
/// * **`x << n`** — place bit `i-n` at position `i`, zero-fill the low bits;
///   bits shifted past position `N` are **dropped** (integer `<<`, i.e.
///   truncated to `N` bits — *not* `x·2ⁿ mod p`). `n ≥ N` → 0.
macro_rules! impl_field_int_shift {
    ($($t:ty => $n:literal),+ $(,)?) => {$(
        impl Shr<$t> for Field {
            type Output = Field;
            fn shr(self, n: $t) -> Field {
                let bits = self.to_bits::<$n>(); // range-check self < 2^N
                let mut out = [Field::from(0u8); $n];
                // Guard in the widened domain so a huge `n` can't truncate to a
                // small `usize` and shift by the wrong amount; `n >= N` → all 0.
                if (n as u128) < $n {
                    let n = n as usize; // exact: n < N <= 128
                    let mut i = 0usize;
                    while i + n < $n {
                        out[i] = bits[i + n];
                        i += 1;
                    }
                }
                Field::from_bits::<$n>(out)
            }
        }
        impl Shl<$t> for Field {
            type Output = Field;
            fn shl(self, n: $t) -> Field {
                let bits = self.to_bits::<$n>(); // range-check self < 2^N
                let mut out = [Field::from(0u8); $n];
                if (n as u128) < $n {
                    let n = n as usize; // exact: n < N <= 128
                    let mut i = n;
                    while i < $n {
                        out[i] = bits[i - n]; // bits past position N are dropped (truncate)
                        i += 1;
                    }
                }
                Field::from_bits::<$n>(out)
            }
        }
    )+};
}
impl_field_int_shift!(u8 => 8, u16 => 16, u32 => 32, u64 => 64, u128 => 128);

/// Integer modulus of a `Field` against a native-integer *constant* `m`, where
/// the constant's type supplies the domain width `N = bitwidth(T)` and its value
/// is the modulus: `x % 8u16` means "treat `x` as 16-bit, mod 8".
///
/// **Provided for `u8`..`u64` only** (deliberately **not** `u128`). The general
/// (non-power-of-two) path pins a `hint_div_rem` witness `[q, r]` with
/// `m·q + r == x`, `r < m`, `q < 2ᴺ`; that is sound only while `m·q + r` cannot
/// wrap the field, i.e. `2·N ≤ 253`. For `u8`..`u64` (`2·N ≤ 128 ≤ 253`) this
/// always holds. For `u128` (`N = 128`, `2·N = 256 > 253`) a modulus `m > 2¹²⁶`
/// could admit a wrapping `q < 2¹²⁸` and forge the remainder, so we omit
/// `Rem<u128>` entirely (`x % 5u128` does not compile — use a `u64`-or-narrower
/// modulus, or `Field::from(m)` division primitives directly).
///
/// `x % m`: for `m = 2ᵏ` (power of two), the low `k` bits — free, no hint. For
/// general `m`, the pinned `hint_div_rem` above; the two range checks (`r < m`
/// and `q < 2ᴺ`) are what stop a malicious prover from choosing a wrapping
/// `q`/`r`. `m` must be a compile-time constant (const-propagated at the inline
/// site). Mod-by-zero falls into the general path and is **unprovable** (a
/// `hint_div_rem` by 0), not a clean compile error — because `m` is runtime from
/// rustc's view, so a `const { assert!(m != 0) }` is not available here.
macro_rules! impl_field_int_rem {
    ($($t:ty => $n:literal),+ $(,)?) => {$(
        impl Rem<$t> for Field {
            type Output = Field;
            // Manual power-of-two test: `is_power_of_two` may not lower cleanly.
            #[allow(clippy::manual_is_power_of_two)]
            fn rem(self, m: $t) -> Field {
                let bits = self.to_bits::<$n>(); // range-check self < 2^N (bounds q < 2^N too)
                if m != 0 && (m & (m - 1)) == 0 {
                    // m = 2^k: x mod 2^k is the low k bits — free, no hint.
                    let mut out = [Field::from(0u8); $n];
                    let mut i = 0usize;
                    while i < $n {
                        if (1u128 << i) < (m as u128) {
                            out[i] = bits[i];
                        }
                        i += 1;
                    }
                    Field::from_bits::<$n>(out)
                } else {
                    // General m (m == 0 also lands here and is unprovable: div by 0).
                    let qr = Field::hint_div_rem(self, Field::from(m));
                    let q = qr[0];
                    let r = qr[1];
                    assert_eq(Field::from(m) * q + r, self); // pin the division
                    assert(r < m); // r < m AND r < 2^N (range check via PartialOrd<T>)
                    let _ = q.to_bits::<$n>(); // q < 2^N: with 2N <= 253, m*q + r can't wrap
                    r
                }
            }
        }
    )+};
}
// u128 deliberately excluded: 2N = 256 > 253 would let m*q wrap the field.
impl_field_int_rem!(u8 => 8, u16 => 16, u32 => 32, u64 => 64);

/// Emit a circuit equality constraint `lhs == rhs`.
///
/// Either argument may be `bool` (the result of a comparison, `.is_zero()`,
/// etc.) or `Field` — both types convert to `Field` for zero-cost.
///
/// This is a marker: the compiler lowers it to an R1CS constraint rather than
/// executing it.
#[inline(never)]
pub fn assert_eq<L: Into<Field>, R: Into<Field>>(_lhs: L, _rhs: R) {
    loop {}
}

/// Constrain a boolean wire to be true.
///
/// `assert(cond)` decomposes into `assert_eq(cond, true)` at lowering time.
pub fn assert(cond: bool) {
    assert_eq(cond, true);
}

/// Emit a circuit constraint `a < b` (less than).
pub fn assert_lt<A: PartialOrd<B>, B>(a: A, b: B) {
    assert_eq(a < b, true);
}

/// Emit a circuit constraint `a <= b` (less than or equal).
pub fn assert_le<A: PartialOrd<B>, B>(a: A, b: B) {
    assert_eq(a <= b, true);
}

/// Emit a circuit constraint `a > b` (greater than).
pub fn assert_gt<A: PartialOrd<B>, B>(a: A, b: B) {
    assert_eq(a > b, true);
}

/// Emit a circuit constraint `a >= b` (greater than or equal).
pub fn assert_ge<A: PartialOrd<B>, B>(a: A, b: B) {
    assert_eq(a >= b, true);
}

// The `__xark_*` compiler intrinsics referenced above (`__xark_add`,
// `__xark_eq`, the `hint_*` family, …) now live in `crate::intrinsics`, imported
// at the top of this module. See that module for the constraint-vs-hint ABI and
// per-intrinsic lowering docs.

// Keep `PhantomData` referenced so `#![no_std]` users pulling only this crate do
// not trip an unused-import lint if they re-export internals. It documents that
// `Field` is intended to be a zero-sized opaque marker.
#[doc(hidden)]
pub type _FieldMarker = PhantomData<Field>;
