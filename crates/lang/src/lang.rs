//! The `xark` language markers used by circuit programs: the `Field` circuit
//! type, the `Private`/`Public` visibility aliases, and `#[inline(never)]`
//! intrinsic functions the compiler recognizes (in the circuit build, calls to its
//! `xark.*` imports). On the host they panic with an explanation rather than
//! computing anything.

// Off the circuit build, an intrinsic's body is `intrinsics::__xark_marker` (an
// explanatory panic on the host).
#![allow(clippy::empty_loop)]
// Written in the `acc = acc + …` style (the old compiler rejected `+=` on `Field`;
// the wasm frontend accepts both).
#![allow(clippy::assign_op_pattern)]

use core::cmp::{Ordering, PartialOrd};
use core::marker::PhantomData;
use core::ops::{
    Add, AddAssign, BitXor, Div, DivAssign, Mul, MulAssign, Neg, Rem, Shl, Shr, Sub, SubAssign,
};

// The `__xark_*` intrinsics live in `crate::intrinsics`.
use crate::intrinsics::*;

/// The opaque circuit field element.
///
/// Carries a private non-zero-sized payload so that (a) it cannot be constructed
/// except through the recognized intrinsics, and (b) optimization cannot
/// collapse `Field` values to a single constant ZST (which would erase the
/// data-flow the compiler tracks).
///
/// Implements `core::ops` arithmetic (`+ - * /`, unary `-`, `*Assign`, `^`).
/// Comparisons are circuit operations returning a `bool` — a `{0,1}` field wire:
/// * `==` / `!=` vs a `Field` or native-int constant — width-independent equality.
/// * `<` `<=` `>` `>=` vs a native-int constant (`PartialOrd<uN>`), whose type
///   fixes the bit-width `N` for the required range check.
/// * two-witness ordering via the explicit-width [`Field::lt`]`::<N>` / `gt` / `le` / `ge`.
///
/// A bare `Field` is intentionally **not** `PartialOrd for Field`: ordering the
/// canonical `[0, r)` representative needs a width, so it must come from the RHS
/// type or the `::<N>`. See `docs/integer-ops.md`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Field {
    /// Little-endian 4×64-bit value. In a circuit build it is meaningful only for
    /// constants (the compiler reads it out of a `const Field`; a witness is
    /// tracked symbolically). In a host build every `Field` holds its value here,
    /// in `[0, p)`: circuit code runs natively there.
    _limbs: [u64; 4],
}

/// Prints the field's **decimal value** (e.g. `Field(19900101)`) rather than the
/// raw limbs, so you can read the value straight out of a `{:?}` dump — of a bare
/// `Field`, a `#[input]` struct, or a generated `<Fn>Inputs` — and
/// feed it to `xark prove`. Like [`Field::to_decimal`], the value is meaningful
/// on the host, or for a constant (in a circuit, a witness is symbolic).
impl core::fmt::Debug for Field {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Field({})", self.to_decimal())
    }
}

/// A private witness input. Transparent alias, erased during type checking; the
/// compiler recovers the distinction from the *syntactic* HIR signature.
pub type Private<T> = T;

/// A public input. See [`Private`].
pub type Public<T> = T;

impl Field {
    /// Constant constructor backing `From<u8..u64>` — recognised by the compiler
    /// through the *call* (so circuit bodies work) and const-evaluated for real
    /// literals. For a `const` **item**, call [`Field::from_u128`] directly (`.into()`
    /// can't appear in `const` — `From`/`Into` aren't `const` on stable).
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

    /// The additive identity `0`. `const fn`, so it works in circuit bodies and
    /// `const` items alike. Prefer this (and [`Field::one`]) over
    /// `Field::from(0u8)` for common small constants.
    pub const fn zero() -> Field {
        Field::constant_u64(0)
    }

    /// The multiplicative identity `1`. See [`Field::zero`].
    pub const fn one() -> Field {
        Field::constant_u64(1)
    }

    /// The little-endian 4×64-bit limbs of a `Field`'s value: on the host, or for a
    /// constant (in a circuit a witness is symbolic and these are unspecified). Exposed for *tooling* (a host-side input
    /// builder reads a constant's value back to decimal); authors never need it.
    #[doc(hidden)]
    pub const fn to_limbs(self) -> [u64; 4] {
        self._limbs
    }

    /// The decimal value of a `Field` on the host (or of a constant): how the host
    /// reads an input back out to feed the prover. In a circuit a witness's limbs
    /// are symbolic. `#[doc(hidden)]` tooling; authors never call it.
    #[doc(hidden)]
    pub fn to_decimal(self) -> alloc::string::String {
        use alloc::string::String;
        use alloc::vec::Vec;
        let mut limbs = self._limbs; // little-endian 4×u64
        if limbs == [0u64; 4] {
            return String::from("0");
        }
        // Long division of the 256-bit value by 10, collecting digits.
        let mut digits: Vec<u8> = Vec::new();
        while limbs != [0u64; 4] {
            let mut rem = 0u128;
            let mut i = 4;
            while i > 0 {
                i -= 1;
                let cur = (rem << 64) | limbs[i] as u128;
                limbs[i] = (cur / 10) as u64;
                rem = cur % 10;
            }
            digits.push(b'0' + rem as u8);
        }
        digits.reverse();
        String::from_utf8(digits).expect("ascii digits")
    }

    /// A field element from an integer, in `const` position: `const DOB: Field =
    /// Field::from_u128(19900101)`. Use these `from_*` constructors (not `x.into()`) in a
    /// `const` item — `From`/`Into` are trait methods, and trait methods aren't `const` on
    /// stable Rust, so a conversion can't appear in a `const`. At runtime, `Field::from(x)`
    /// is equivalent. Per-type constructors ([`from_u8`](Self::from_u8) …
    /// [`from_u64`](Self::from_u64), [`from_bool`](Self::from_bool)) avoid an `as u128` cast.
    pub const fn from_u128(value: u128) -> Field {
        Field {
            _limbs: [value as u64, (value >> 64) as u64, 0, 0],
        }
    }

    /// A field element from a `u8`, in `const` position. See [`Field::from_u128`].
    pub const fn from_u8(value: u8) -> Field {
        Field::constant_u64(value as u64)
    }

    /// A field element from a `u16`, in `const` position. See [`Field::from_u128`].
    pub const fn from_u16(value: u16) -> Field {
        Field::constant_u64(value as u64)
    }

    /// A field element from a `u32`, in `const` position. See [`Field::from_u128`].
    pub const fn from_u32(value: u32) -> Field {
        Field::constant_u64(value as u64)
    }

    /// A field element from a `u64`, in `const` position. See [`Field::from_u128`].
    pub const fn from_u64(value: u64) -> Field {
        Field::constant_u64(value)
    }

    /// A field element from a `bool` (`false → 0`, `true → 1`), in `const` position.
    /// See [`Field::from_u128`].
    pub const fn from_bool(value: bool) -> Field {
        Field::constant_u64(value as u64)
    }

    /// The BN254 scalar field order `p`, little-endian 64-bit limbs.
    const MODULUS: [u64; 4] = [
        0x43e1f593f0000001,
        0x2833e84879b97091,
        0xb85045b68181585d,
        0x30644e72e131a029,
    ];

    /// A 256-bit value reduced to `[0, p)`: since `2^256 < 6p`, at most five
    /// subtractions. Keeps a constant `Field` canonical, so `to_decimal` (and so
    /// the prover) sees the value the circuit does.
    const fn reduced(mut limbs: [u64; 4]) -> Field {
        loop {
            // limbs >= p? Compare from the most significant limb.
            let mut i = 4;
            let mut ge = true;
            while i > 0 {
                i -= 1;
                if limbs[i] != Self::MODULUS[i] {
                    ge = limbs[i] > Self::MODULUS[i];
                    break;
                }
            }
            if !ge {
                return Field { _limbs: limbs };
            }
            let mut borrow = 0u64;
            let mut j = 0;
            while j < 4 {
                let (d, b1) = limbs[j].overflowing_sub(Self::MODULUS[j]);
                let (d, b2) = d.overflowing_sub(borrow);
                limbs[j] = d;
                borrow = (b1 | b2) as u64;
                j += 1;
            }
        }
    }

    /// In-circuit constant from a decimal string, for full field-sized constants
    /// that don't fit a `u128`: `Field::constant("218882428718...")`. A `const fn`,
    /// so it works in circuit bodies (recognised by the call) and `const` items.
    /// Parses a non-negative decimal `< 2^256`, reduced mod p; panics (a compile
    /// error in `const` contexts) on a non-digit or overflow.
    pub const fn constant(decimal: &str) -> Field {
        let bytes = decimal.as_bytes();
        let mut limbs = [0u64; 4];
        let mut i = 0;
        while i < bytes.len() {
            let b = bytes[i];
            assert!(
                b'0' <= b && b <= b'9',
                "Field::constant expects a decimal string (non-numeric character)"
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
        Self::reduced(limbs)
    }

    /// A field element from **little-endian** bytes (`bytes[0]` is least significant) —
    /// the direct "raw bytes → `Field`" input constructor, no `Fr`/decimal round-trip.
    /// A `const fn`, so byte-encoded inputs (an id, a random nonce) can be `const`.
    /// At most 32 bytes; the value is reduced mod p (so 32 random bytes are a
    /// uniform-enough field element, and `to_decimal` gives the value proven).
    pub const fn from_le_bytes(bytes: &[u8]) -> Field {
        assert!(bytes.len() <= 32, "Field::from_le_bytes: at most 32 bytes");
        let mut limbs = [0u64; 4];
        let mut i = 0;
        while i < bytes.len() {
            limbs[i / 8] |= (bytes[i] as u64) << ((i % 8) * 8);
            i += 1;
        }
        Self::reduced(limbs)
    }

    /// A field element from **big-endian** bytes (`bytes[0]` is most significant) — the
    /// byte order of most hashes / SEC1 scalars. See [`Field::from_le_bytes`].
    pub const fn from_be_bytes(bytes: &[u8]) -> Field {
        assert!(bytes.len() <= 32, "Field::from_be_bytes: at most 32 bytes");
        let mut limbs = [0u64; 4];
        let n = bytes.len();
        let mut i = 0;
        while i < n {
            // `bytes[n-1-i]` is the i-th least-significant byte.
            limbs[i / 8] |= (bytes[n - 1 - i] as u64) << ((i % 8) * 8);
            i += 1;
        }
        Self::reduced(limbs)
    }

    /// Allocate a fresh *advice* (private witness) field element with no
    /// witness-generation hint. The circuit must pin it with `require_eq`. Prefer
    /// the typed `hint_*` constructors below, which also record how to compute the
    /// value so the emitted IR is self-contained.
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
    /// from `Field` primitives (`hint_bit` + arithmetic + `require_eq`).
    #[cfg_attr(not(xark), track_caller)]
    pub fn to_bits<const N: usize>(self) -> [Field; N] {
        // N > 253 wraps mod r, so recomposition wouldn't pin `self`
        const {
            assert!(
                N <= 253,
                "to_bits::<N>: N must be <= 253 (BN254 field capacity)"
            )
        };
        // The compiler's decomposition memo: a constant's bits, a sum of proven bits,
        // or an earlier `to_bits::<N>` of the same value.
        #[cfg(all(xark, target_arch = "wasm32"))]
        if let Some(bits) = crate::wasm::to_bits_lookup::<N>(&self) {
            return bits;
        }
        let mut bits = [Field::from(0u8); N];
        let mut i = 0usize;
        while i < N {
            bits[i] = Field::hint_bit(self, i);
            i += 1;
        }
        let mut i = 0usize;
        while i < N {
            bits[i].require_bool();
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
        __xark_require_eq_scalar(acc, self); // recomposition pins the bits to `self` (⇒ self < 2^N)
        #[cfg(all(xark, target_arch = "wasm32"))]
        crate::wasm::to_bits_record::<N>(&self, &bits);
        bits
    }

    /// [`Field::to_bits`] for a width known as a value, `n ≤ 253`: the low `n` bits
    /// (the rest of the array zero), proving `self < 2^n` with `n` booleanity rows and
    /// one recomposition. For a width that comes from a type, such as an enum's
    /// variant count, which a const generic can't take.
    #[cfg_attr(not(xark), track_caller)]
    pub fn to_bits_n(self, n: usize) -> [Field; 253] {
        assert!(
            n <= 253,
            "to_bits_n: n must be <= 253 (BN254 field capacity)"
        );
        let mut bits = [Field::from(0u8); 253];
        #[cfg(all(xark, target_arch = "wasm32"))]
        if crate::wasm::to_bits_lookup_n(&self, n, &mut bits) {
            return bits;
        }
        let mut i = 0usize;
        while i < n {
            bits[i] = Field::hint_bit(self, i);
            i += 1;
        }
        let mut i = 0usize;
        while i < n {
            bits[i].require_bool();
            i += 1;
        }
        let mut acc = Field::from(0u8);
        let mut pow = Field::from(1u8);
        let mut i = 0usize;
        while i < n {
            acc = acc + bits[i] * pow;
            pow = pow + pow;
            i += 1;
        }
        __xark_require_eq_scalar(acc, self); // ⇒ self < 2^n
        #[cfg(all(xark, target_arch = "wasm32"))]
        crate::wasm::to_bits_record_n(&self, n, &bits);
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

    /// Exponentiation by a compile-time exponent: `x.pow(3)` is `x³`, lowered to
    /// exponentiation-by-squaring. The exponent is a native `u64` constant — a
    /// circuit has no runtime integers. Not spelled `x ^ 3`: `^` is Rust's XOR
    /// ([`Field::xor`]), so overloading it for `pow` would silently reverse meaning.
    #[inline(never)]
    pub fn pow(self, exp: u64) -> Field {
        __xark_pow_u64(self, exp)
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
    #[cfg_attr(not(xark), track_caller)]
    pub fn require_bool(self) {
        __xark_require_eq_scalar(self * self, self);
    }

    // Field-vs-Field ordered comparison, explicit width: the one case with no
    // native-int operand to carry `N`. Both operands are *witnesses*, so BOTH are
    // range-checked to `< 2^N` via `to_bits::<N>` before the compare — else a
    // prover could place an out-of-range residue in either wire and defeat it.
    // `le`/`ge` delegate to `gt`/`lt`, inheriting that pair of checks. Inherent
    // methods, not `PartialOrd for Field`: a bare `Field` stays orderless because
    // ordering needs a width (see docs/integer-ops).

    /// `self < rhs` as a `{0,1}` `bool` wire, both as `N`-bit unsigned integers
    /// (range-checks both to `< 2^N`).
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
        __xark_require_eq_scalar(self * w, Field::from(1u8));
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
#[cfg(xark)]
impl From<&str> for Field {
    fn from(s: &str) -> Field {
        Field::constant(s)
    }
}

/// An input value from a decimal or `0x`-hex string, as `xark prove --inputs`
/// takes it. Panics on anything else, or on a value `>= p`: an input outside the
/// field is a mistake, never silently reduced (see [`Field::try_from_str`]).
#[cfg(not(xark))]
impl From<&str> for Field {
    fn from(s: &str) -> Field {
        Field::try_from_str(s).unwrap_or_else(|e| panic!("{e}"))
    }
}

/// See `From<&str>`.
#[cfg(not(xark))]
impl From<alloc::string::String> for Field {
    fn from(s: alloc::string::String) -> Field {
        Field::from(s.as_str())
    }
}

/// See `From<&str>`.
#[cfg(not(xark))]
impl From<&alloc::string::String> for Field {
    fn from(s: &alloc::string::String) -> Field {
        Field::from(s.as_str())
    }
}

// Signed integers as input values, so an untyped literal (`cube(3, 27)`, which
// Rust types as `i32`) converts. Negative values panic: inputs must be field
// elements `0 <= x < p`, as `xark prove --inputs` requires. Host-only.
#[cfg(not(xark))]
impl From<i32> for Field {
    fn from(v: i32) -> Field {
        Field::from(i64::from(v))
    }
}

#[cfg(not(xark))]
impl From<i64> for Field {
    fn from(v: i64) -> Field {
        let v = u64::try_from(v).unwrap_or_else(|_| {
            panic!("input value {v} is negative; inputs are field elements 0 <= x < p")
        });
        Field::from_u64(v)
    }
}

/// A prover scalar (`ark_bn254::Fr`, what off-circuit reference code computes) as
/// an input value. Host-only.
#[cfg(not(xark))]
impl From<ark_bn254::Fr> for Field {
    fn from(x: ark_bn254::Fr) -> Field {
        use ark_ff::PrimeField;
        Field {
            _limbs: x.into_bigint().0,
        }
    }
}

#[cfg(not(xark))]
impl Field {
    /// A field element from a decimal or `0x`-hex string, or an error naming what's
    /// wrong: not a number, or not below `p` (out-of-range inputs are rejected, not
    /// reduced, as everywhere else inputs are taken). Host-only.
    pub fn try_from_str(s: &str) -> Result<Field, alloc::string::String> {
        use alloc::format;
        let t = s.trim();
        let (digits, radix) = match t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
            Some(h) => (h, 16u32),
            None => (t, 10u32),
        };
        if digits.is_empty() {
            return Err(format!("`{s}` is not a decimal or 0x-hex number"));
        }
        let mut limbs = [0u64; 4];
        for c in digits.chars() {
            let Some(d) = c.to_digit(radix) else {
                return Err(format!("`{s}` is not a decimal or 0x-hex number"));
            };
            let mut carry = d as u128;
            for l in limbs.iter_mut() {
                let v = *l as u128 * radix as u128 + carry;
                *l = v as u64;
                carry = v >> 64;
            }
            if carry != 0 {
                return Err(format!("`{s}` is larger than the field (2^256 or more)"));
            }
        }
        let f = Field { _limbs: limbs };
        if Field::reduced(limbs)._limbs != limbs {
            return Err(format!(
                "`{s}` is not a field element (it is p or more); inputs are not reduced mod p"
            ));
        }
        Ok(f)
    }
}

/// Circuit equality: `self == other` / `self != other` return a `bool` that is a
/// `{0,1}` field wire (the compiler lowers this to the equality gadget). On the
/// host it compares the values. There is no `Eq`/`Hash`: in a circuit a `Field` is
/// a symbolic witness, not a value to key on.
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

/// A `Field` to the prover's scalar (`ark_bn254::Fr`), reduced mod the field order —
/// the same value the solver feeds the circuit. Host-only (`cfg(not(xark))`), where a
/// `Field` always holds its value; also what the native intrinsics compute with.
#[cfg(not(xark))]
impl From<Field> for ark_bn254::Fr {
    fn from(f: Field) -> ark_bn254::Fr {
        use ark_ff::PrimeField;
        let mut bytes = [0u8; 32];
        let mut i = 0;
        while i < 4 {
            let limb = f._limbs[i].to_le_bytes();
            bytes[i * 8..i * 8 + 8].copy_from_slice(&limb);
            i += 1;
        }
        ark_bn254::Fr::from_le_bytes_mod_order(&bytes)
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

/// Bitwise XOR `^` on `Field`, matching Rust's meaning: for `self, rhs ∈ {0,1}`
/// this is boolean XOR, one fused R1CS constraint (sugar for [`Field::xor`]).
/// Exponentiation is now [`Field::pow`] (`x.pow(3)`), *not* `^` — overloading `^`
/// for powers silently reversed the meaning of valid-looking Rust.
impl BitXor for Field {
    type Output = Field;

    #[inline(never)]
    fn bitxor(self, rhs: Field) -> Field {
        __xark_xor(self, rhs)
    }
}

/// `Field` arithmetic with a native-integer constant on the right — `a + 1`,
/// `a * 3`, `a - 2` — as sugar for `a op Field::from(n)`. Each forwards to the
/// recognized `Field`-`Field` operator, so it lowers to the exact same R1CS; the
/// integer must be a compile-time constant (a circuit has no runtime integers).
/// (Exponentiation is [`Field::pow`], not `^` — `^` is Rust's XOR.)
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

/// Integer comparison of a `Field` against a native-integer *constant*, whose
/// type supplies the domain width `N = bitwidth(T)` (`bool → 1`, …, `u128 → 128`).
///
/// * `x == c` / `x != c` — width-independent equality (`__xark_eq`), **no** range check.
/// * `x < c` / `x <= c` / `x > c` / `x >= c` — ordered comparison. Each first
///   range-checks the *witness* operand `x` to `< 2^N` via `to_bits::<N>` (the
///   soundness contract: a prover holding an out-of-range residue cannot satisfy
///   the decomposition), then compares against `c` (known `< 2^N`, no check).
///   `le`/`ge` are `!gt`/`!lt`, inheriting `gt`/`lt`'s single range check.
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
        }
        impl PartialOrd<$t> for Field {
            // Never reaches lowering: the overridden `lt`/`le`/`gt`/`ge` handle the
            // operators directly, so `partial_cmp` is never invoked. Exists only to
            // satisfy the trait — a circuit compare yields a `{0,1}` wire, not an
            // `Option<Ordering>`.
            fn partial_cmp(&self, _rhs: &$t) -> Option<Ordering> {
                crate::intrinsics::__xark_marker()
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

/// Integer shifts of a `Field` against a native-integer *constant*, whose type
/// supplies the domain width `N = bitwidth(T)` and whose value is the shift
/// amount: `x >> 3u32` = "treat `x` as 32-bit, shift right by 3". `bool` excluded
/// (degenerate); signed shifts out of scope.
///
/// Provided for `u8`..`u128` — all sound: a shift is pure bit re-wiring, and
/// `from_bits::<N>` with `N ≤ 128 ≤ 253` cannot wrap the field. Each op first
/// `to_bits::<N>(self)`, which range-checks `self < 2^N` (the soundness contract).
/// The shift amount `n` must be a compile-time constant (const-propagated at the
/// inline site; a non-const amount fails to lower).
///
/// * **`x >> n`** — `⌊x / 2ⁿ⌋` in the `N`-bit domain: bit `i+n` → position `i`,
///   zero-fill the top. `n ≥ N` → 0.
/// * **`x << n`** — bit `i-n` → position `i`, zero-fill the low bits; bits past
///   position `N` are **dropped** (integer `<<`, truncated to `N` bits — *not*
///   `x·2ⁿ mod p`). `n ≥ N` → 0.
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
                        out[i] = bits[i - n];
                        i += 1;
                    }
                }
                Field::from_bits::<$n>(out)
            }
        }
    )+};
}
impl_field_int_shift!(u8 => 8, u16 => 16, u32 => 32, u64 => 64, u128 => 128);

/// Integer modulus of a `Field` against a native-integer *constant* `m`, whose
/// type supplies the domain width `N = bitwidth(T)` and whose value is the
/// modulus: `x % 8u16` = "treat `x` as 16-bit, mod 8".
///
/// **Provided for `u8`..`u64` only** (deliberately **not** `u128`). The general
/// path pins a `hint_div_rem` witness `[q, r]` with `m·q + r == x`, `r < m`,
/// `q < 2ᴺ`; sound only while `m·q + r` cannot wrap the field, i.e. `2·N ≤ 253`.
/// For `u8`..`u64` (`2·N ≤ 128`) this holds. For `u128` (`2·N = 256 > 253`) a
/// modulus `m > 2¹²⁶` could admit a wrapping `q` and forge the remainder, so
/// `Rem<u128>` is omitted (`x % 5u128` does not compile).
///
/// `x % m`: for `m = 2ᵏ`, the low `k` bits — free, no hint. For general `m`, the
/// pinned `hint_div_rem` above; the two range checks (`r < m`, `q < 2ᴺ`) stop a
/// malicious prover choosing a wrapping `q`/`r`. `m` must be a compile-time
/// constant. Mod-by-zero lands in the general path and is **unprovable** (a
/// `hint_div_rem` by 0), not a clean compile error — `m` is runtime from rustc's
/// view, so `const { assert!(m != 0) }` is unavailable here.
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
                    __xark_require_eq_scalar(Field::from(m) * q + r, self); // pin the division
                    require(r < m); // r < m AND r < 2^N (range check via PartialOrd<T>)
                    let _ = q.to_bits::<$n>(); // q < 2^N: with 2N <= 253, m*q + r can't wrap
                    r
                }
            }
        }
    )+};
}
impl_field_int_rem!(u8 => 8, u16 => 16, u32 => 32, u64 => 64);

/// Emit a circuit equality constraint `lhs == rhs`.
///
/// Dispatches through [`RequireEqCircuit`], so one `require_eq` compares scalars
/// (`Field`/`bool`), fixed arrays `[T; N]` element-wise, and composite gadget
/// outputs (e.g. a SHA-256 digest `[[Field; 32]; 8]` vs a `Digest`).
/// Every leaf bottoms out at the recognized scalar intrinsic
/// ([`__xark_require_eq_scalar`]). In a circuit the compiler lowers each leaf to an
/// R1CS constraint rather than executing it. Run natively (a host build), it
/// checks the values and panics here if they differ.
#[inline]
#[cfg_attr(not(xark), track_caller)]
pub fn require_eq<A: RequireEqCircuit<B>, B>(a: A, b: B) {
    a.require_eq_circuit(b);
}

/// Constrain a boolean wire to be true.
///
/// `require(cond)` decomposes into `require_eq(cond, true)` at lowering time. Run
/// natively (a host build), it panics here if `cond` is false.
#[cfg_attr(not(xark), track_caller)]
pub fn require(cond: bool) {
    #[cfg(not(xark))]
    crate::intrinsics::native::require(cond);
    #[cfg(xark)]
    __xark_require_eq_scalar(cond, true);
}

/// Emit a circuit inequality constraint `a != b`.
///
/// `a != b` holds exactly when `a - b` is nonzero, i.e. invertible. This reuses
/// [`Field::inv`], which allocates `w = (a-b)⁻¹` as advice and pins `(a-b)·w == 1`
/// — a single multiplication constraint. In a field `0·w = 1` is unsatisfiable for
/// every `w`, so the circuit has no solution precisely when `a == b`, with no way
/// for a prover to cheat. Cost: one R1CS constraint plus one witness value.
///
/// Scalars only (`Field`/`bool`, via [`Into<Field>`]); there is no element-wise
/// array form because `[a] != [b]` is ambiguous (all-differ vs not-all-equal).
#[inline]
#[cfg_attr(not(xark), track_caller)]
pub fn require_ne(a: impl Into<Field>, b: impl Into<Field>) {
    #[cfg(not(xark))]
    crate::intrinsics::native::require(a.into() != b.into());
    #[cfg(xark)]
    let _ = (a.into() - b.into()).inv();
}

/// Open a **witness-only** region. Until [`witness_end`], value-producing ops
/// (multiplications, `hint_*` calls) still fill their witness but emit **no R1CS
/// constraints**, and the vars they allocate are pinning-exempt. This lets a
/// gadget *derive* advice (an inverse chain, a GLV reduction, a decompressed
/// coordinate) at **zero constraint cost**, then pin only the final result with
/// normal constrained code after `witness_end`.
///
/// Soundness is the caller's: nothing inside the region is constrained — a
/// `require_eq`/`assert!` there is not enforced — so every value that must be
/// trusted has to be pinned afterwards. Nothing done in the region counts as proven
/// later: recomputing a value after `witness_end` (a `to_bits`, a select, a bounded
/// subtraction) constrains it afresh. Run natively, the region's `require`s
/// aren't checked either.
#[inline(never)]
pub fn witness_begin() {
    #[cfg(all(xark, target_arch = "wasm32"))]
    crate::wasm::witness_begin();
    #[cfg(not(xark))]
    crate::intrinsics::native::witness_begin();
    #[cfg(all(xark, not(target_arch = "wasm32")))]
    crate::intrinsics::__xark_marker()
}

/// Close a [`witness_begin`] region — subsequent ops emit constraints again.
#[inline(never)]
pub fn witness_end() {
    #[cfg(all(xark, target_arch = "wasm32"))]
    crate::wasm::witness_end();
    #[cfg(not(xark))]
    crate::intrinsics::native::witness_end();
    #[cfg(all(xark, not(target_arch = "wasm32")))]
    crate::intrinsics::__xark_marker()
}

/// The dispatch behind [`require_eq`]. Scalar impls (`Field`, `bool`) bottom out
/// at the recognized scalar intrinsic ([`__xark_require_eq_scalar`]); composite
/// impls (fixed arrays here, a digest in `xark-hash`) recurse down to those
/// scalar leaves. Downstream crates add impls for their own gadget-output shapes.
pub trait RequireEqCircuit<Rhs> {
    /// Emit the equality constraint(s) for `self == rhs`.
    fn require_eq_circuit(self, rhs: Rhs);
}

impl<R: Into<Field>> RequireEqCircuit<R> for Field {
    #[inline]
    #[cfg_attr(not(xark), track_caller)]
    fn require_eq_circuit(self, rhs: R) {
        __xark_require_eq_scalar(self, rhs);
    }
}

impl<R: Into<Field>> RequireEqCircuit<R> for bool {
    #[inline]
    #[cfg_attr(not(xark), track_caller)]
    fn require_eq_circuit(self, rhs: R) {
        __xark_require_eq_scalar(self, rhs);
    }
}

// The other `Into<Field>` scalars, so either side of `require_eq` may be one
// (`require_eq(7u64, x)` as well as `require_eq(x, 7u64)`).
macro_rules! impl_require_eq_scalar {
    ($($t:ty),*) => {$(
        impl<R: Into<Field>> RequireEqCircuit<R> for $t {
            #[inline]
            #[cfg_attr(not(xark), track_caller)]
            fn require_eq_circuit(self, rhs: R) {
                __xark_require_eq_scalar(self, rhs);
            }
        }
    )*};
}
impl_require_eq_scalar!(u8, u16, u32, u64, u128, &str);

/// Element-wise equality for fixed-size arrays: `require_eq(out, expected)` on
/// `[T; N]` emits the per-element constraints, unrolling to the same `N` scalar
/// `require_eq`s a manual loop produces. Recurses through nested arrays via the
/// element impl. Both element types are `Copy` — always true for the `Field`/`bool`
/// leaves this compares.
impl<const N: usize, A: Copy + RequireEqCircuit<B>, B: Copy> RequireEqCircuit<[B; N]> for [A; N] {
    #[inline]
    #[cfg_attr(not(xark), track_caller)]
    fn require_eq_circuit(self, rhs: [B; N]) {
        let mut i = 0usize;
        while i < N {
            self[i].require_eq_circuit(rhs[i]);
            i += 1;
        }
    }
}

/// Bytes to their `Field` values, element-wise: what a `[u8; N]` `#[circuit]` parameter
/// becomes in the body (the gadgets take `[Field; N]`). Free: each byte is already a
/// range-checked wire, so `Field::from` is the identity on it.
#[doc(hidden)]
pub fn bytes_to_fields<const N: usize>(bytes: [u8; N]) -> [Field; N] {
    let mut out = [Field::from_u8(0); N];
    let mut i = 0;
    while i < N {
        out[i] = Field::from(bytes[i]);
        i += 1;
    }
    out
}

/// The scalar equality **intrinsic** the compiler recognizes by name and lowers
/// to a two-`Field` R1CS constraint — the leaf every [`RequireEqCircuit`] impl
/// bottoms out at. `#[doc(hidden)]` plumbing; authors write [`require_eq`], which
/// dispatches here. Never executed in a circuit; on the host it checks the values.
#[doc(hidden)]
#[inline(never)]
#[cfg_attr(not(xark), track_caller)]
pub fn __xark_require_eq_scalar<L: Into<Field>, R: Into<Field>>(_lhs: L, _rhs: R) {
    #[cfg(all(xark, target_arch = "wasm32"))]
    crate::wasm::require_eq(_lhs.into(), _rhs.into());
    #[cfg(not(xark))]
    crate::intrinsics::native::require_eq(_lhs.into(), _rhs.into());
    #[cfg(all(xark, not(target_arch = "wasm32")))]
    crate::intrinsics::__xark_marker()
}

/// Emit a circuit constraint `a < b` (less than).
#[cfg_attr(not(xark), track_caller)]
pub fn require_lt<A: PartialOrd<B>, B>(a: A, b: B) {
    __xark_require_eq_scalar(a < b, true);
}

/// Emit a circuit constraint `a <= b` (less than or equal).
#[cfg_attr(not(xark), track_caller)]
pub fn require_le<A: PartialOrd<B>, B>(a: A, b: B) {
    __xark_require_eq_scalar(a <= b, true);
}

/// Emit a circuit constraint `a > b` (greater than).
#[cfg_attr(not(xark), track_caller)]
pub fn require_gt<A: PartialOrd<B>, B>(a: A, b: B) {
    __xark_require_eq_scalar(a > b, true);
}

/// Emit a circuit constraint `a >= b` (greater than or equal).
#[cfg_attr(not(xark), track_caller)]
pub fn require_ge<A: PartialOrd<B>, B>(a: A, b: B) {
    __xark_require_eq_scalar(a >= b, true);
}

// The `__xark_*` intrinsics referenced above live in `crate::intrinsics` (imported
// at the top). See that module for the constraint-vs-hint ABI and lowering docs.

// Keeps `PhantomData` referenced so `#![no_std]` users pulling only this crate do
// not trip an unused-import lint.
#[doc(hidden)]
pub type _FieldMarker = PhantomData<Field>;
