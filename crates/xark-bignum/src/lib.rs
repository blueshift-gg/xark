//! `xark-bignum`: non-native ("foreign field") arithmetic over a 256-bit prime
//! modulus, shared by the secp256k1 / secp256r1 curve gadgets.
//!
//! A field element is a **width-generic `Bignum`**: `LIMBS` little-endian
//! `BITS`-bit limbs (`[Field; LIMBS]`, value `Σ limb[i]·2^(BITS·i)`). Callers pick
//! the width explicitly (e.g. secp256k1 uses `<3, 86>`). Every operation takes the
//! modulus as an explicit parameter (`m` as `LIMBS` limbs, `m_minus_1` for the
//! canonical range check), so the exact same, individually solver-validated
//! routines serve any prime field — base field or scalar field, k1 or r1.
//!
//! All arithmetic is limb-wise with explicit carry/borrow propagation; carries
//! are range-checked so no intermediate term ever wraps the BN254 modulus the
//! circuit is proven over (which would silently break the integer identity). A
//! per-instantiation `const` budget assertion (see [`mod_mul`]) rejects any
//! `(LIMBS, BITS)` whose schoolbook column products could overflow BN254 `Fr`.

#![no_std]
// Circuit-lowered gadget code: the xark compiler rejects compound assignment on
// `Field` (`+=`/`-=`/`*=`), so `x = x + y` is required — not a clippy oversight.
#![allow(clippy::assign_op_pattern)]

use xark::assert_eq;
/// Re-exported so the [`fp!`] macro can name `$crate::Field` without the caller
/// importing `xark`.
pub use xark::Field;

// ===========================================================================
// Width-generic non-native modular arithmetic (`Bignum<LIMBS, BITS>`).
// ===========================================================================

/// Maximum limb count / bit width the fixed decomposition buffers accommodate.
/// Buffers are sized to these maxima and only the first `BITS`/`LIMBS` slots are
/// ever filled or referenced — the unused (constant-zero) slots are pruned from
/// the R1CS, so oversizing the buffers costs nothing. (Avoids `[Field; BITS + 1]`,
/// which would need unstable `generic_const_exprs`.)
const MAX_BITS: usize = 128;
const MAX_LIMBS: usize = 16;
const MAX_COLS: usize = 2 * MAX_LIMBS - 1;

/// A width-generic non-native field element: `LIMBS` little-endian `BITS`-bit
/// limbs (value `Σ limb[i]·2^(BITS·i)`). A **zero-cost** newtype over
/// `[Field; LIMBS]` — every method forwards to the free function of the same
/// name, so the emitted R1CS is byte-identical. Callers alias a concrete width,
/// e.g. `type Fp = Bignum<3, 86>` for a 256-bit prime field.
#[derive(Clone, Copy)]
pub struct Bignum<const LIMBS: usize, const BITS: usize> {
    pub limbs: [Field; LIMBS],
}

impl<const LIMBS: usize, const BITS: usize> Bignum<LIMBS, BITS> {
    /// The limb count and bit width, exposed so `fp!(Name, "0x…", ThisType)` can
    /// read the geometry off a `Bignum<LIMBS, BITS>` type alias (e.g. a shared
    /// `type Scalar = Bignum<3, 86>` used for both the field and `[Scalar; 2]`
    /// points).
    pub const LIMBS: usize = LIMBS;
    pub const BITS: usize = BITS;

    /// Wrap `LIMBS` little-endian limbs.
    pub fn new(limbs: [Field; LIMBS]) -> Self {
        Bignum { limbs }
    }

    /// Range-check every limb to `[0, 2^BITS)`.
    pub fn range_check(self) {
        range_check_limbs::<LIMBS, BITS>(self.limbs)
    }

    /// `(self · rhs) mod m`. `m_minus_1` is `m − 1` (the remainder range bound).
    pub fn mul(self, rhs: Self, m: Self, m_minus_1: Self) -> Self {
        let limbs = mod_mul::<LIMBS, BITS>(self.limbs, rhs.limbs, m.limbs, m_minus_1.limbs);
        Bignum { limbs }
    }

    /// `(self + rhs) mod m`.
    pub fn add(self, rhs: Self, m: Self) -> Self {
        let limbs = mod_add::<LIMBS, BITS>(self.limbs, rhs.limbs, m.limbs);
        Bignum { limbs }
    }

    /// `(self − rhs) mod m`. `comp` is the caller-supplied `m`-complement const.
    pub fn sub(self, rhs: Self, comp: Self) -> Self {
        let limbs = mod_sub::<LIMBS, BITS>(self.limbs, rhs.limbs, comp.limbs);
        Bignum { limbs }
    }

    /// `(m − self) mod m`.
    pub fn neg(self, m: Self) -> Self {
        let limbs = mod_neg::<LIMBS, BITS>(self.limbs, m.limbs);
        Bignum { limbs }
    }

    /// `self⁻¹ mod m`.
    pub fn inverse(self, m: Self) -> Self {
        let limbs = mod_inverse::<LIMBS, BITS>(self.limbs, m.limbs);
        Bignum { limbs }
    }

    /// Fused `(self − b − c) mod m` (one hint, cheaper than two subtractions).
    /// `m_minus_1` is `m − 1`.
    pub fn sub2(self, b: Self, c: Self, m: Self, m_minus_1: Self) -> Self {
        let limbs = sub2::<LIMBS, BITS>(self.limbs, b.limbs, c.limbs, m.limbs, m_minus_1.limbs);
        Bignum { limbs }
    }

    /// `(3·self) mod m` (cheaper than two additions).
    pub fn triple(self, m: Self) -> Self {
        let limbs = triple_mod::<LIMBS, BITS>(self.limbs, m.limbs);
        Bignum { limbs }
    }

    /// Reduce a value that may be `≥ m` (but `< 2·m`) to the canonical `[0, m)`.
    pub fn reduce(self, m: Self) -> Self {
        let limbs = reduce_once::<LIMBS, BITS>(self.limbs, m.limbs);
        Bignum { limbs }
    }
}

/// Parse a decimal or `0x`-hex string into `N` little-endian `BITS`-bit limbs
/// (each `< 2^BITS`) at compile time. `panic!` (a compile error in `const`
/// contexts) on a non-digit or a value that overflows `N·BITS` bits.
const fn parse_limbs<const N: usize, const BITS: usize>(s: &str) -> [u128; N] {
    let bytes = s.as_bytes();
    let (radix, start): (u128, usize) =
        if bytes.len() >= 2 && bytes[0] == b'0' && (bytes[1] == b'x' || bytes[1] == b'X') {
            (16, 2)
        } else {
            (10, 0)
        };
    let mask = (1u128 << BITS) - 1;
    let mut limbs = [0u128; N];
    let mut i = start;
    while i < bytes.len() {
        let b = bytes[i];
        let d = if b >= b'0' && b <= b'9' {
            (b - b'0') as u128
        } else if b >= b'a' && b <= b'f' {
            (b - b'a' + 10) as u128
        } else if b >= b'A' && b <= b'F' {
            (b - b'A' + 10) as u128
        } else {
            panic!("modulus string: expected a decimal or 0x-hex digit")
        };
        assert!(
            d < radix,
            "modulus string: digit out of range for its radix"
        );
        // limbs = limbs * radix + d, in base 2^BITS.
        let mut carry = d;
        let mut j = 0;
        while j < N {
            let v = limbs[j] * radix + carry;
            limbs[j] = v & mask;
            carry = v >> BITS;
            j += 1;
        }
        assert!(carry == 0, "modulus string does not fit in LIMBS*BITS bits");
        i += 1;
    }
    limbs
}

const fn to_field_limbs<const N: usize>(vals: [u128; N]) -> [Field; N] {
    let mut out = [Field::from_u128(0); N];
    let mut i = 0;
    while i < N {
        out[i] = Field::from_u128(vals[i]);
        i += 1;
    }
    out
}

/// The modulus as `N` little-endian `BITS`-bit `Field` limbs. See [`fp!`].
pub const fn modulus_limbs<const N: usize, const BITS: usize>(s: &str) -> [Field; N] {
    to_field_limbs(parse_limbs::<N, BITS>(s))
}

/// `modulus − 1` as limbs (the canonical remainder range bound).
pub const fn modulus_minus_1<const N: usize, const BITS: usize>(s: &str) -> [Field; N] {
    let mut v = parse_limbs::<N, BITS>(s);
    let mask = (1u128 << BITS) - 1;
    let mut borrow = 1u128;
    let mut i = 0;
    while i < N {
        if v[i] >= borrow {
            v[i] -= borrow;
            borrow = 0;
        } else {
            v[i] = v[i] + (mask + 1) - borrow;
            borrow = 1;
        }
        i += 1;
    }
    assert!(borrow == 0, "modulus must be >= 1");
    to_field_limbs(v)
}

/// `2^(BITS·N) − modulus` as limbs (the subtraction complement) — the two's
/// complement `~modulus + 1` in base `2^BITS`.
pub const fn complement<const N: usize, const BITS: usize>(s: &str) -> [Field; N] {
    let p = parse_limbs::<N, BITS>(s);
    let mask = (1u128 << BITS) - 1;
    let mut c = [0u128; N];
    let mut i = 0;
    while i < N {
        c[i] = mask - p[i];
        i += 1;
    }
    let mut carry = 1u128;
    let mut i = 0;
    while i < N {
        let v = c[i] + carry;
        c[i] = v & mask;
        carry = v >> BITS;
        i += 1;
    }
    to_field_limbs(c)
}

/// Define a non-native prime-field element type in one line:
/// ```ignore
/// xark_bignum::fp!(Fp, "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F");
/// let c = a * b + a - b;   // `Fp` has +  -  *  unary-  and .inverse()/.sub2()/.triple()/.reduce()
/// ```
/// You give it the name and the modulus (a decimal or `0x`-hex string); a
/// `~256`-bit field defaults to the `3 × 86`-bit limb layout. An optional trailing
/// `LIMBS, BITS` picks a different geometry: `fp!(Fp, "0x…", 4, 64)`. The limb
/// split, `m − 1`, and the `2^(BITS·LIMBS) − m` subtraction complement are all
/// derived at compile time; the generated type is a zero-cost `[Field; LIMBS]`
/// newtype whose operators forward to the width-generic free functions, so the
/// emitted R1CS is byte-identical to calling them by hand.
#[macro_export]
macro_rules! fp {
    // Two-arg form: a ~256-bit prime field. Defaults to the standard 3 × 86-bit
    // limb layout (86 bits is the multiply-optimal limb size over BN254), so you
    // write only the name and the modulus.
    ($vis:vis $name:ident, $modulus:literal) => {
        $crate::fp!(@build $vis $name, $modulus, 3, 86);
    };
    // Geometry from a `Bignum<LIMBS, BITS>` type — `fp!(Fp, "0x…", Scalar)` — so a
    // single `type Scalar = Bignum<L, B>` can feed both the field and its
    // `[Scalar; 2]` points.
    ($vis:vis $name:ident, $modulus:literal, $geom:ty) => {
        $crate::fp!(@build $vis $name, $modulus, { <$geom>::LIMBS }, { <$geom>::BITS });
    };
    // Explicit limb layout: `fp!(Fp, "0x…", 4, 64)`.
    ($vis:vis $name:ident, $modulus:literal, $limbs:literal, $bits:literal) => {
        $crate::fp!(@build $vis $name, $modulus, $limbs, $bits);
    };
    (@build $vis:vis $name:ident, $modulus:literal, $limbs:expr, $bits:expr) => {
        #[derive(Clone, Copy)]
        $vis struct $name {
            pub limbs: [$crate::Field; $limbs],
        }
        #[allow(dead_code)]
        impl $name {
            const M: [$crate::Field; $limbs] = $crate::modulus_limbs::<{ $limbs }, { $bits }>($modulus);
            const M1: [$crate::Field; $limbs] = $crate::modulus_minus_1::<{ $limbs }, { $bits }>($modulus);
            const C: [$crate::Field; $limbs] = $crate::complement::<{ $limbs }, { $bits }>($modulus);
            /// Wrap `LIMBS` little-endian `BITS`-bit limbs.
            pub fn new(limbs: [$crate::Field; $limbs]) -> Self {
                Self { limbs }
            }
            /// Range-check every limb to `[0, 2^BITS)`.
            pub fn range_check(self) {
                $crate::range_check_limbs::<{ $limbs }, { $bits }>(self.limbs)
            }
            /// `self⁻¹ mod m`.
            pub fn inverse(self) -> Self {
                Self::new($crate::mod_inverse::<{ $limbs }, { $bits }>(self.limbs, Self::M))
            }
            /// Fused `(self − b − c) mod m` (one hint).
            pub fn sub2(self, b: Self, c: Self) -> Self {
                Self::new($crate::sub2::<{ $limbs }, { $bits }>(self.limbs, b.limbs, c.limbs, Self::M, Self::M1))
            }
            /// `(3·self) mod m`.
            pub fn triple(self) -> Self {
                Self::new($crate::triple_mod::<{ $limbs }, { $bits }>(self.limbs, Self::M))
            }
            /// Reduce a value `< 2·m` to the canonical `[0, m)`.
            pub fn reduce(self) -> Self {
                Self::new($crate::reduce_once::<{ $limbs }, { $bits }>(self.limbs, Self::M))
            }
            /// Assert canonical: every limb `∈ [0, 2^BITS)` and value `< m`.
            /// Rejects non-canonical encodings (the source of ECDSA malleability).
            pub fn assert_canonical(self) {
                $crate::range_check_limbs::<{ $limbs }, { $bits }>(self.limbs);
                $crate::assert_lt::<{ $limbs }, { $bits }>(self.limbs, Self::M1);
            }
            /// Assert this element is nonzero (assumes range-checked limbs).
            pub fn assert_nonzero(self) {
                $crate::assert_nonzero_limbs::<{ $limbs }>(self.limbs);
            }
        }
        impl ::core::ops::Add for $name {
            type Output = Self;
            fn add(self, rhs: Self) -> Self {
                Self::new($crate::mod_add::<{ $limbs }, { $bits }>(self.limbs, rhs.limbs, Self::M))
            }
        }
        impl ::core::ops::Sub for $name {
            type Output = Self;
            fn sub(self, rhs: Self) -> Self {
                Self::new($crate::mod_sub::<{ $limbs }, { $bits }>(self.limbs, rhs.limbs, Self::C))
            }
        }
        impl ::core::ops::Mul for $name {
            type Output = Self;
            fn mul(self, rhs: Self) -> Self {
                Self::new($crate::mod_mul::<{ $limbs }, { $bits }>(self.limbs, rhs.limbs, Self::M, Self::M1))
            }
        }
        impl ::core::ops::Neg for $name {
            type Output = Self;
            fn neg(self) -> Self {
                Self::new($crate::mod_neg::<{ $limbs }, { $bits }>(self.limbs, Self::M))
            }
        }
    };
}

/// `2^BITS` as a field constant (valid since the soundness budget forces
/// `BITS < 128`).
fn two_pow<const BITS: usize>() -> Field {
    Field::from(1u128 << BITS)
}

/// Decompose `v < 2^(BITS+1)` into `BITS+1` pinned boolean bits (low `BITS` + top
/// borrow/carry bit at index `BITS`). Only the first `BITS+1` buffer slots are
/// filled; the rest stay constant-zero.
/// Decompose `v` into `BITS + EXTRA` little-endian bits (boolean-constrained and
/// recomposition-pinned). `EXTRA` is the headroom above `BITS` for the top
/// carry/borrow: `1` for a single carry bit, `2` for a doubled term.
fn decompose_top<const BITS: usize, const EXTRA: usize>(v: Field) -> [Field; MAX_BITS] {
    let mut bits = [Field::from(0u8); MAX_BITS];
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < BITS + EXTRA {
        let bit = Field::hint_bit(v, i);
        bit.assert_bool();
        bits[i] = bit;
        acc = acc + bit * pow;
        pow = pow + pow;
        i += 1;
    }
    assert_eq(acc, v);
    bits
}

/// Recompose the low `BITS` bits of a decomposition buffer.
fn low_bits<const BITS: usize>(bits: [Field; MAX_BITS]) -> Field {
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < BITS {
        acc = acc + bits[i] * pow;
        pow = pow + pow;
        i += 1;
    }
    acc
}

/// Range-check `v < 2^BITS`.
fn range_bits<const BITS: usize>(v: Field) {
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < BITS {
        let bit = Field::hint_bit(v, i);
        bit.assert_bool();
        acc = acc + bit * pow;
        pow = pow + pow;
        i += 1;
    }
    assert_eq(acc, v);
}

/// Range-check a biased column carry `v < 2^(BITS+6)` (the `mulmod_columns`
/// carries; `+6` covers `log2(LIMBS)` plus signed-carry headroom for the widths
/// this gadget targets).
fn range_bits_carry<const BITS: usize>(v: Field) {
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < BITS + 6 {
        let bit = Field::hint_bit(v, i);
        bit.assert_bool();
        acc = acc + bit * pow;
        pow = pow + pow;
        i += 1;
    }
    assert_eq(acc, v);
}

/// Range-check `v < 2^3` (small biased `sub2` carries, width-independent).
fn range_lt_8(v: Field) {
    let b0 = Field::hint_bit(v, 0);
    let b1 = Field::hint_bit(v, 1);
    let b2 = Field::hint_bit(v, 2);
    b0.assert_bool();
    b1.assert_bool();
    b2.assert_bool();
    assert_eq(b0 + b1 + b1 + b2 + b2 + b2 + b2, v);
}

/// Range-check each of the `LIMBS` limbs of `x` to `[0, 2^BITS)`.
pub fn range_check_limbs<const LIMBS: usize, const BITS: usize>(x: [Field; LIMBS]) {
    let mut i = 0usize;
    while i < LIMBS {
        range_bits::<BITS>(x[i]);
        i += 1;
    }
}

/// Modular negation `(m - b) mod m` (enforces `b <= m`).
pub fn mod_neg<const LIMBS: usize, const BITS: usize>(
    b: [Field; LIMBS],
    m: [Field; LIMBS],
) -> [Field; LIMBS] {
    let two_b = two_pow::<BITS>();
    let mut out = [Field::from(0u8); LIMBS];
    let mut borrow = Field::from(0u8);
    let mut i = 0usize;
    while i < LIMBS {
        let d_i = m[i] - b[i] - borrow + two_b;
        let bits = decompose_top::<BITS, 1>(d_i);
        out[i] = low_bits::<BITS>(bits);
        borrow = Field::from(1u8) - bits[BITS];
        i += 1;
    }
    assert_eq(borrow, Field::from(0u8));
    out
}

/// Modular addition `(a + b) mod m`. Precondition `a, b < m`, so `a+b < 2m` fits
/// in `LIMBS` limbs and one conditional subtraction of `m` suffices.
pub fn mod_add<const LIMBS: usize, const BITS: usize>(
    a: [Field; LIMBS],
    b: [Field; LIMBS],
    m: [Field; LIMBS],
) -> [Field; LIMBS] {
    let two_b = two_pow::<BITS>();
    let mut s = [Field::from(0u8); LIMBS];
    let mut carry = Field::from(0u8);
    let mut i = 0usize;
    while i < LIMBS {
        let sum_i = a[i] + b[i] + carry;
        let bits = decompose_top::<BITS, 1>(sum_i);
        s[i] = low_bits::<BITS>(bits);
        carry = bits[BITS];
        i += 1;
    }
    let mut diff = [Field::from(0u8); LIMBS];
    let mut borrow = Field::from(0u8);
    let mut k = Field::from(0u8);
    let mut i = 0usize;
    while i < LIMBS {
        let d_i = s[i] - m[i] - borrow + two_b;
        let bits = decompose_top::<BITS, 1>(d_i);
        diff[i] = low_bits::<BITS>(bits);
        let no_borrow = bits[BITS];
        borrow = Field::from(1u8) - no_borrow;
        k = no_borrow;
        i += 1;
    }
    let mut result = [Field::from(0u8); LIMBS];
    let mut i = 0usize;
    while i < LIMBS {
        result[i] = s[i] + k * (diff[i] - s[i]);
        i += 1;
    }
    result
}

/// Modular subtraction `(a - b) mod m`. Direct two-pass: `diff = a - b`
/// (borrow = `[a<b]`), then `result = diff - borrow·comp` where `comp = 2^(BITS·LIMBS·... )`
/// is the caller-supplied top-representation complement of `m`.
pub fn mod_sub<const LIMBS: usize, const BITS: usize>(
    a: [Field; LIMBS],
    b: [Field; LIMBS],
    comp: [Field; LIMBS],
) -> [Field; LIMBS] {
    let two_b = two_pow::<BITS>();
    let mut diff = [Field::from(0u8); LIMBS];
    let mut borrow = Field::from(0u8);
    let mut i = 0usize;
    while i < LIMBS {
        let d_i = a[i] - b[i] - borrow + two_b;
        let bits = decompose_top::<BITS, 1>(d_i);
        diff[i] = low_bits::<BITS>(bits);
        borrow = Field::from(1u8) - bits[BITS];
        i += 1;
    }
    let mut result = [Field::from(0u8); LIMBS];
    let mut borrow2 = Field::from(0u8);
    let mut i = 0usize;
    while i < LIMBS {
        let d_i = diff[i] - borrow * comp[i] - borrow2 + two_b;
        let bits = decompose_top::<BITS, 1>(d_i);
        result[i] = low_bits::<BITS>(bits);
        borrow2 = Field::from(1u8) - bits[BITS];
        i += 1;
    }
    assert_eq(borrow2, Field::from(0u8));
    result
}

/// `(3·v) mod m` for `v < m`. Forms the exact triple `3v < 3m` (per-limb
/// `3·v[i] + carry < 2^(BITS+2)`, carry ∈ [0,3]) in one scaling pass, then reduces
/// `[0,3m) → [0,m)` with two conditional subtractions.
pub fn triple_mod<const LIMBS: usize, const BITS: usize>(
    v: [Field; LIMBS],
    m: [Field; LIMBS],
) -> [Field; LIMBS] {
    let mut s = [Field::from(0u8); LIMBS];
    let mut carry = Field::from(0u8);
    let mut i = 0usize;
    while i < LIMBS {
        let t = v[i] + v[i] + v[i] + carry;
        let bits = decompose_top::<BITS, 2>(t);
        let lo = low_bits::<BITS>(bits);
        s[i] = lo;
        carry = bits[BITS] + Field::from(2u8) * bits[BITS + 1];
        i += 1;
    }
    assert_eq(carry, Field::from(0u8)); // 3v < 2^(BITS·LIMBS) ⇒ no top overflow
    reduce_once::<LIMBS, BITS>(reduce_once::<LIMBS, BITS>(s, m), m)
}

/// Reduce `x < 2m` modulo `m`, one conditional subtraction.
pub fn reduce_once<const LIMBS: usize, const BITS: usize>(
    x: [Field; LIMBS],
    m: [Field; LIMBS],
) -> [Field; LIMBS] {
    let two_b = two_pow::<BITS>();
    let mut diff = [Field::from(0u8); LIMBS];
    let mut borrow = Field::from(0u8);
    let mut k = Field::from(0u8);
    let mut i = 0usize;
    while i < LIMBS {
        let d_i = x[i] - m[i] - borrow + two_b;
        let bits = decompose_top::<BITS, 1>(d_i);
        diff[i] = low_bits::<BITS>(bits);
        let no_borrow = bits[BITS];
        borrow = Field::from(1u8) - no_borrow;
        k = no_borrow;
        i += 1;
    }
    let mut out = [Field::from(0u8); LIMBS];
    let mut i = 0usize;
    while i < LIMBS {
        out[i] = x[i] + k * (diff[i] - x[i]);
        i += 1;
    }
    out
}

/// Enforce `x < m` (`(m-1) - x` produces no final borrow). `x`'s limbs must be
/// range-checked first.
pub fn assert_lt<const LIMBS: usize, const BITS: usize>(
    x: [Field; LIMBS],
    m_minus_1: [Field; LIMBS],
) {
    let two_b = two_pow::<BITS>();
    let mut borrow = Field::from(0u8);
    let mut i = 0usize;
    while i < LIMBS {
        let d_i = m_minus_1[i] - x[i] - borrow + two_b;
        let bits = decompose_top::<BITS, 1>(d_i);
        let no_borrow = bits[BITS];
        borrow = Field::from(1u8) - no_borrow;
        i += 1;
    }
    assert_eq(borrow, Field::from(0u8));
}

/// Return a pinned boolean `lt ∈ {0,1}` with `lt == 1` **iff** `a < b`, comparing
/// two canonical `LIMBS × BITS`-bit limb vectors (each limb assumed `< 2^BITS`).
///
/// Same sound subtract-with-borrow as [`assert_lt`] — it computes `a − b` limb by
/// limb, where each `d_i = a[i] − b[i] − borrow + 2^BITS ∈ [0, 2^(BITS+1))` is
/// bit-decomposed (`decompose_top` pins it) and its top bit is `no_borrow`. Every
/// term stays `< 2^(BITS+1)`, so nothing wraps the field, and the final borrow is
/// exactly the `a < b` bit — no full-width value is ever reconstructed. Unlike
/// `assert_lt` (which asserts the borrow is `0`), this **returns** it, so a caller
/// can branch/mux on the comparison and derive advice (rounding carries, GLV
/// signs) in-circuit instead of passing it as a witness input.
pub fn is_lt<const LIMBS: usize, const BITS: usize>(a: [Field; LIMBS], b: [Field; LIMBS]) -> Field {
    let two_b = two_pow::<BITS>();
    let mut borrow = Field::from(0u8);
    let mut i = 0usize;
    while i < LIMBS {
        let d_i = a[i] - b[i] - borrow + two_b;
        let bits = decompose_top::<BITS, 1>(d_i);
        let no_borrow = bits[BITS];
        borrow = Field::from(1u8) - no_borrow;
        i += 1;
    }
    borrow
}

/// Pinned `a ≥ b` bit (`1 − is_lt`). Canonical limb-vector precondition as [`is_lt`].
pub fn is_ge<const LIMBS: usize, const BITS: usize>(a: [Field; LIMBS], b: [Field; LIMBS]) -> Field {
    Field::from(1u8) - is_lt::<LIMBS, BITS>(a, b)
}

/// Assert the limbs encode a nonzero value (not all zero). Assumes range-checked limbs.
pub fn assert_nonzero_limbs<const LIMBS: usize>(limbs: [Field; LIMBS]) {
    // all_zero = AND of isZero(limbᵢ); assert it is 0 to forbid value 0
    let mut all_zero = Field::from(1u8);
    let mut i = 0usize;
    while i < LIMBS {
        all_zero = all_zero.and(Field::from(limbs[i].is_zero()));
        i += 1;
    }
    assert_eq(all_zero, Field::from(0u8));
}

/// Shared column/carry identity `a·b == q·m + r`. `q`, `r` are the caller-supplied
/// (and separately range-checked) quotient/remainder; `q_i·m_j` folds since `m` is
/// constant. Biased signed carries keep every intermediate `< 2^(2·BITS + slack)`.
fn mulmod_columns<const LIMBS: usize, const BITS: usize>(
    a: [Field; LIMBS],
    b: [Field; LIMBS],
    q: [Field; LIMBS],
    r: [Field; LIMBS],
    m: [Field; LIMBS],
) {
    let two_b = two_pow::<BITS>(); // 2^BITS
    let bias = Field::from(1u128 << (BITS + 4)); // 2^(BITS+4)
    let bias_shift = two_b * two_b * Field::from(1u128 << 4); // 2^(2·BITS+4)

    let mut lhs = [Field::from(0u8); MAX_COLS];
    let mut rhs = [Field::from(0u8); MAX_COLS];
    let mut i = 0usize;
    while i < LIMBS {
        let mut j = 0usize;
        while j < LIMBS {
            lhs[i + j] = lhs[i + j] + a[i] * b[j];
            rhs[i + j] = rhs[i + j] + q[i] * m[j];
            j += 1;
        }
        i += 1;
    }
    let mut c = 0usize;
    while c < LIMBS {
        rhs[c] = rhs[c] + r[c];
        c += 1;
    }

    // Biased signed-carry chain (columns 0..2·LIMBS-2 range-checked, top direct).
    let mut cb_prev = bias;
    let mut c = 0usize;
    while c < 2 * LIMBS - 2 {
        let num = lhs[c] - rhs[c] + cb_prev + bias_shift - bias;
        let dr = Field::hint_div_rem(num, two_b);
        let cb = dr[0];
        let rem = dr[1];
        assert_eq(num, two_b * cb + rem);
        assert_eq(rem, Field::from(0u8));
        range_bits_carry::<BITS>(cb);
        cb_prev = cb;
        c += 1;
    }
    let num_top = lhs[2 * LIMBS - 2] - rhs[2 * LIMBS - 2] + cb_prev + bias_shift - bias;
    assert_eq(num_top, bias_shift);
}

/// Non-native modular multiplication `(a·b) mod m` over `LIMBS` × `BITS`-bit limbs.
///
/// SOUNDNESS BUDGET: the schoolbook column products `Σ a_i·b_j` (and `Σ q_i·m_j`)
/// plus biased carries must not wrap BN254 `Fr` (~2^254). A single product is
/// `< 2^(2·BITS)`; summed across a column with carry/bias headroom, `2·BITS + slack`
/// bits must stay below the field. The `const` assertion below fails to compile for
/// any unsound `(LIMBS, BITS)`. For `<3, 86>`: `172 + 8 = 180 < 253`.
pub const P_25519_L: [Field; 3] = modulus_limbs::<3, 85>(
    "57896044618658097711785492504343953926634992332820282019728792003956564819949",
);

/// SOUND lazy multiply mod (2^255-19), 3x85. Pseudo-Mersenne fold with carries
/// range-checked (deterministic — NO free choice), NO quotient, NO canonical
/// reduce. Output ≡ a·b (mod p), limbs < 2^86. Accepts inputs up to < 2^88.
pub fn mul_lazy_25519(a: [Field; 3], b: [Field; 3]) -> [Field; 3] {
    let two85 = Field::from(1u128 << 85);
    let c19 = Field::from(19u8);
    let mut cols = [Field::from(0u8); 5];
    let mut i = 0usize;
    while i < 3usize {
        let mut j = 0usize;
        while j < 3usize {
            cols[i + j] = cols[i + j] + a[i] * b[j];
            j += 1;
        }
        i += 1;
    }
    let t0 = cols[0] + c19 * cols[3];
    let t1 = cols[1] + c19 * cols[4];
    let t2 = cols[2];
    let d0 = Field::hint_div_rem(t0, two85);
    let c0 = d0[0];
    let r0 = d0[1];
    assert_eq(t0, two85 * c0 + r0);
    range_bits::<85>(r0);
    range_bits::<101>(c0);
    let x1 = t1 + c0;
    let d1 = Field::hint_div_rem(x1, two85);
    let c1 = d1[0];
    let r1 = d1[1];
    assert_eq(x1, two85 * c1 + r1);
    range_bits::<85>(r1);
    range_bits::<101>(c1);
    let x2 = t2 + c1;
    let d2 = Field::hint_div_rem(x2, two85);
    let c2 = d2[0];
    let r2 = d2[1];
    assert_eq(x2, two85 * c2 + r2);
    range_bits::<85>(r2);
    range_bits::<96>(c2);
    let u0 = r0 + c19 * c2;
    let e0 = Field::hint_div_rem(u0, two85);
    let k0 = e0[0];
    let s0 = e0[1];
    assert_eq(u0, two85 * k0 + s0);
    range_bits::<85>(s0);
    range_bits::<16>(k0);
    let s1 = r1 + k0;
    [s0, s1, r2]
}

/// SOUND weak reduce: carry-normalize a positive limb array (limbs < 2^89) to a
/// loosely-reduced 3x85 value (limbs < 2^86, ≡ input mod p). Carries range-checked
/// (deterministic). NO canonical reduce. Used after biased subtractions.
pub const M_K1: [Field; 4] =
    modulus_limbs::<4, 64>("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F");

/// Sound 4×64 lazy multiply mod secp256k1 p (fold ×c, c=2^32+977). Inputs <2^70;
/// carries range-checked (sound); output ≡ a·b (mod p), limbs <2^65.
pub fn mul_lazy_k1(a: [Field; 4], b: [Field; 4]) -> [Field; 4] {
    let two64 = Field::from(1u128 << 64);
    let c = Field::from(4294968273u128);
    let mut cols = [Field::from(0u8); 7];
    let mut i = 0usize;
    while i < 4usize {
        let mut j = 0usize;
        while j < 4usize {
            cols[i + j] = cols[i + j] + a[i] * b[j];
            j += 1;
        }
        i += 1;
    }
    let t0 = cols[0] + c * cols[4];
    let t1 = cols[1] + c * cols[5];
    let t2 = cols[2] + c * cols[6];
    let t3 = cols[3];
    let d0 = Field::hint_div_rem(t0, two64);
    let c0 = d0[0];
    let r0 = d0[1];
    assert_eq(t0, two64 * c0 + r0);
    range_bits::<64>(r0);
    range_bits::<112>(c0);
    let x1 = t1 + c0;
    let d1 = Field::hint_div_rem(x1, two64);
    let c1 = d1[0];
    let r1 = d1[1];
    assert_eq(x1, two64 * c1 + r1);
    range_bits::<64>(r1);
    range_bits::<112>(c1);
    let x2 = t2 + c1;
    let d2 = Field::hint_div_rem(x2, two64);
    let c2 = d2[0];
    let r2 = d2[1];
    assert_eq(x2, two64 * c2 + r2);
    range_bits::<64>(r2);
    range_bits::<112>(c2);
    let x3 = t3 + c2;
    let d3 = Field::hint_div_rem(x3, two64);
    let c3 = d3[0];
    let r3 = d3[1];
    assert_eq(x3, two64 * c3 + r3);
    range_bits::<64>(r3);
    range_bits::<82>(c3);
    let u0 = r0 + c * c3;
    let e0 = Field::hint_div_rem(u0, two64);
    let k0 = e0[0];
    let s0 = e0[1];
    assert_eq(u0, two64 * k0 + s0);
    range_bits::<64>(s0);
    range_bits::<52>(k0);
    let s1 = r1 + k0;
    [s0, s1, r2, r3]
}

/// Sound weak reduce for secp256k1: positive limbs < 2^72 → loosely-reduced <2^65.
pub fn weak_reduce_k1(v: [Field; 4]) -> [Field; 4] {
    let two64 = Field::from(1u128 << 64);
    let c = Field::from(4294968273u128);
    let d0 = Field::hint_div_rem(v[0], two64);
    let c0 = d0[0];
    let r0 = d0[1];
    assert_eq(v[0], two64 * c0 + r0);
    range_bits::<64>(r0);
    range_bits::<10>(c0);
    let x1 = v[1] + c0;
    let d1 = Field::hint_div_rem(x1, two64);
    let c1 = d1[0];
    let r1 = d1[1];
    assert_eq(x1, two64 * c1 + r1);
    range_bits::<64>(r1);
    range_bits::<10>(c1);
    let x2 = v[2] + c1;
    let d2 = Field::hint_div_rem(x2, two64);
    let c2 = d2[0];
    let r2 = d2[1];
    assert_eq(x2, two64 * c2 + r2);
    range_bits::<64>(r2);
    range_bits::<10>(c2);
    let x3 = v[3] + c2;
    let d3 = Field::hint_div_rem(x3, two64);
    let c3 = d3[0];
    let r3 = d3[1];
    assert_eq(x3, two64 * c3 + r3);
    range_bits::<64>(r3);
    range_bits::<10>(c3);
    let u0 = r0 + c * c3;
    let e0 = Field::hint_div_rem(u0, two64);
    let k0 = e0[0];
    let s0 = e0[1];
    assert_eq(u0, two64 * k0 + s0);
    range_bits::<64>(s0);
    range_bits::<40>(k0);
    let s1 = r1 + k0;
    [s0, s1, r2, r3]
}

/// Canonical (< p) reduction of a loosely-reduced secp256k1 value.
pub fn finalize_k1(v: [Field; 4]) -> [Field; 4] {
    reduce_once::<4, 64>(v, M_K1)
}

/// Sound lazy modular inverse mod secp256k1 p: hint w, range-check canonical,
/// assert a·w ≡ 1 (mod p) via lazy multiply. `a` may be loosely-reduced (≠ 0).
pub fn inv_lazy_k1(a: [Field; 4]) -> [Field; 4] {
    let w = Field::hint_mod_inverse::<4>(a, M_K1, 64);
    range_check_limbs::<4, 64>(w);
    let prod = finalize_k1(mul_lazy_k1(a, w));
    assert_eq(prod[0], Field::from(1u8));
    assert_eq(prod[1], Field::from(0u8));
    assert_eq(prod[2], Field::from(0u8));
    assert_eq(prod[3], Field::from(0u8));
    w
}

/// Sound lazy incomplete affine doubling on secp256k1 (a=0). Loosely-reduced in/out.
pub fn ec_double_k1(x: [Field; 4], y: [Field; 4]) -> ([Field; 4], [Field; 4]) {
    let two = Field::from(2u8);
    let three = Field::from(3u8);
    let b8 = [
        Field::from(8u8) * M_K1[0],
        Field::from(8u8) * M_K1[1],
        Field::from(8u8) * M_K1[2],
        Field::from(8u8) * M_K1[3],
    ];
    let x2 = mul_lazy_k1(x, x);
    let num = [three * x2[0], three * x2[1], three * x2[2], three * x2[3]];
    let two_y = [two * y[0], two * y[1], two * y[2], two * y[3]];
    let inv = inv_lazy_k1(two_y);
    let lam = mul_lazy_k1(num, inv);
    let lam2 = mul_lazy_k1(lam, lam);
    let x3 = weak_reduce_k1([
        b8[0] + lam2[0] - two * x[0],
        b8[1] + lam2[1] - two * x[1],
        b8[2] + lam2[2] - two * x[2],
        b8[3] + lam2[3] - two * x[3],
    ]);
    let xmx3 = weak_reduce_k1([
        b8[0] + x[0] - x3[0],
        b8[1] + x[1] - x3[1],
        b8[2] + x[2] - x3[2],
        b8[3] + x[3] - x3[3],
    ]);
    let lt = mul_lazy_k1(lam, xmx3);
    let y3 = weak_reduce_k1([
        b8[0] + lt[0] - y[0],
        b8[1] + lt[1] - y[1],
        b8[2] + lt[2] - y[2],
        b8[3] + lt[3] - y[3],
    ]);
    (x3, y3)
}

/// Sound lazy incomplete affine addition on secp256k1 (px ≠ qx). Loosely-reduced.
pub fn ec_add_k1(
    px: [Field; 4],
    py: [Field; 4],
    qx: [Field; 4],
    qy: [Field; 4],
) -> ([Field; 4], [Field; 4]) {
    let b8 = [
        Field::from(8u8) * M_K1[0],
        Field::from(8u8) * M_K1[1],
        Field::from(8u8) * M_K1[2],
        Field::from(8u8) * M_K1[3],
    ];
    let dx = weak_reduce_k1([
        b8[0] + qx[0] - px[0],
        b8[1] + qx[1] - px[1],
        b8[2] + qx[2] - px[2],
        b8[3] + qx[3] - px[3],
    ]);
    let dy = weak_reduce_k1([
        b8[0] + qy[0] - py[0],
        b8[1] + qy[1] - py[1],
        b8[2] + qy[2] - py[2],
        b8[3] + qy[3] - py[3],
    ]);
    let inv = inv_lazy_k1(dx);
    let lam = mul_lazy_k1(dy, inv);
    let lam2 = mul_lazy_k1(lam, lam);
    let x3 = weak_reduce_k1([
        b8[0] + lam2[0] - px[0] - qx[0],
        b8[1] + lam2[1] - px[1] - qx[1],
        b8[2] + lam2[2] - px[2] - qx[2],
        b8[3] + lam2[3] - px[3] - qx[3],
    ]);
    let xmx3 = weak_reduce_k1([
        b8[0] + px[0] - x3[0],
        b8[1] + px[1] - x3[1],
        b8[2] + px[2] - x3[2],
        b8[3] + px[3] - x3[3],
    ]);
    let lt = mul_lazy_k1(lam, xmx3);
    let y3 = weak_reduce_k1([
        b8[0] + lt[0] - py[0],
        b8[1] + lt[1] - py[1],
        b8[2] + lt[2] - py[2],
        b8[3] + lt[3] - py[3],
    ]);
    (x3, y3)
}

/// Sound on-curve check for secp256k1 (y² = x³ + 7), loosely-reduced coords.
pub fn on_curve_k1(x: [Field; 4], y: [Field; 4]) {
    range_check_limbs::<4, 64>(x);
    range_check_limbs::<4, 64>(y);
    let y2 = mul_lazy_k1(y, y);
    let x2 = mul_lazy_k1(x, x);
    let x3 = mul_lazy_k1(x2, x);
    let rhs = [x3[0] + Field::from(7u8), x3[1], x3[2], x3[3]];
    let lf = finalize_k1(y2);
    let rf = finalize_k1(rhs);
    let mut i = 0usize;
    while i < 4usize {
        assert_eq(lf[i], rf[i]);
        i += 1;
    }
}

/// Decompose a 4×64-bit value into 256 little-endian pinned bits (`< 2^256`).
pub fn scalar_to_bits_256(u: [Field; 4]) -> [Field; 256] {
    let mut bits = [Field::from(0u8); 256];
    let mut l = 0usize;
    while l < 4usize {
        let mut acc = Field::from(0u8);
        let mut pow = Field::from(1u8);
        let mut j = 0usize;
        while j < 64usize {
            let b = Field::hint_bit(u[l], j);
            b.assert_bool();
            bits[l * 64 + j] = b;
            acc = acc + b * pow;
            pow = pow + pow;
            j += 1;
        }
        assert_eq(acc, u[l]);
        l += 1;
    }
    bits
}

pub fn weak_reduce_25519(v: [Field; 3]) -> [Field; 3] {
    let two85 = Field::from(1u128 << 85);
    let c19 = Field::from(19u8);
    let d0 = Field::hint_div_rem(v[0], two85);
    let c0 = d0[0];
    let r0 = d0[1];
    assert_eq(v[0], two85 * c0 + r0);
    range_bits::<85>(r0);
    range_bits::<8>(c0);
    let x1 = v[1] + c0;
    let d1 = Field::hint_div_rem(x1, two85);
    let c1 = d1[0];
    let r1 = d1[1];
    assert_eq(x1, two85 * c1 + r1);
    range_bits::<85>(r1);
    range_bits::<8>(c1);
    let x2 = v[2] + c1;
    let d2 = Field::hint_div_rem(x2, two85);
    let c2 = d2[0];
    let r2 = d2[1];
    assert_eq(x2, two85 * c2 + r2);
    range_bits::<85>(r2);
    range_bits::<8>(c2);
    let u0 = r0 + c19 * c2;
    let e0 = Field::hint_div_rem(u0, two85);
    let k0 = e0[0];
    let s0 = e0[1];
    assert_eq(u0, two85 * k0 + s0);
    range_bits::<85>(s0);
    range_bits::<8>(k0);
    let s1 = r1 + k0;
    [s0, s1, r2]
}

/// Canonical (< p) reduction of a loosely-reduced value — the BOUNDARY reduce.
pub fn finalize_25519(v: [Field; 3]) -> [Field; 3] {
    reduce_once::<3, 85>(v, P_25519_L)
}

/// SOUND lazy extended-coordinate doubling, twisted Edwards a=-1 (dbl-2008-hwcd,
/// d-independent). Inputs/outputs loosely-reduced (limbs < 2^86). Only the final
/// coordinates need a boundary reduce; per-op there is NONE.
pub fn ext_double_25519(
    x: [Field; 3],
    y: [Field; 3],
    z: [Field; 3],
) -> ([Field; 3], [Field; 3], [Field; 3], [Field; 3]) {
    let two = Field::from(2u8);
    // bias = 8p (limbs < 2^88, ≡ 0 mod p) to keep every subtraction positive.
    let b8 = [
        Field::from(8u8) * P_25519_L[0],
        Field::from(8u8) * P_25519_L[1],
        Field::from(8u8) * P_25519_L[2],
    ];
    let aa = mul_lazy_25519(x, x); // A = X^2
    let bb = mul_lazy_25519(y, y); // B = Y^2
    let zz = mul_lazy_25519(z, z); // Z^2
    let xy = mul_lazy_25519(x, y); // XY
    let e = [two * xy[0], two * xy[1], two * xy[2]]; // E = 2XY
    let c = [two * zz[0], two * zz[1], two * zz[2]]; // C = 2Z^2
                                                     // G = B - A
    let g = [
        b8[0] + bb[0] - aa[0],
        b8[1] + bb[1] - aa[1],
        b8[2] + bb[2] - aa[2],
    ];
    // H = -(A + B)
    let h = [
        b8[0] - aa[0] - bb[0],
        b8[1] - aa[1] - bb[1],
        b8[2] - aa[2] - bb[2],
    ];
    // F = G - C  (bias twice since G is already at 8p)
    let f = [
        b8[0] + g[0] - c[0],
        b8[1] + g[1] - c[1],
        b8[2] + g[2] - c[2],
    ];
    let x3 = mul_lazy_25519(e, f);
    let y3 = mul_lazy_25519(g, h);
    let t3 = mul_lazy_25519(e, h);
    let z3 = mul_lazy_25519(f, g);
    (x3, y3, z3, t3)
}

pub const D_25519: [Field; 3] = modulus_limbs::<3, 85>(
    "37095705934669439343138083508754565189542113879843219016388785533085940283555",
);

/// SOUND lazy extended-coordinate addition, twisted Edwards a=-1 (add-2008-hwcd).
/// Inputs/outputs loosely-reduced (limbs < 2^86). 10 lazy muls + 2 weak reduces,
/// NO per-op canonical reduction.
#[allow(clippy::too_many_arguments)]
pub fn ext_add_25519(
    x1: [Field; 3],
    y1: [Field; 3],
    z1: [Field; 3],
    t1: [Field; 3],
    x2: [Field; 3],
    y2: [Field; 3],
    z2: [Field; 3],
    t2: [Field; 3],
) -> ([Field; 3], [Field; 3], [Field; 3], [Field; 3]) {
    let b8 = [
        Field::from(8u8) * P_25519_L[0],
        Field::from(8u8) * P_25519_L[1],
        Field::from(8u8) * P_25519_L[2],
    ];
    let a = mul_lazy_25519(x1, x2); // A = X1·X2
    let b = mul_lazy_25519(y1, y2); // B = Y1·Y2
    let d = mul_lazy_25519(z1, z2); // D = Z1·Z2
    let tt = mul_lazy_25519(t1, t2); // T1·T2
    let c = mul_lazy_25519(D_25519, tt); // C = d·T1·T2
    let x1y1 = [x1[0] + y1[0], x1[1] + y1[1], x1[2] + y1[2]];
    let x2y2 = [x2[0] + y2[0], x2[1] + y2[1], x2[2] + y2[2]];
    let xy = mul_lazy_25519(x1y1, x2y2); // (X1+Y1)(X2+Y2)
                                         // E = xy - A - B
    let e = [
        b8[0] + xy[0] - a[0] - b[0],
        b8[1] + xy[1] - a[1] - b[1],
        b8[2] + xy[2] - a[2] - b[2],
    ];
    // F = D - C
    let f = [
        b8[0] + d[0] - c[0],
        b8[1] + d[1] - c[1],
        b8[2] + d[2] - c[2],
    ];
    let g = [d[0] + c[0], d[1] + c[1], d[2] + c[2]]; // G = D + C
    let h = [b[0] + a[0], b[1] + a[1], b[2] + a[2]]; // H = B + A (a=-1)
    let x3 = mul_lazy_25519(e, f);
    let y3 = mul_lazy_25519(g, h);
    let t3 = mul_lazy_25519(e, h);
    let z3 = mul_lazy_25519(f, g);
    (x3, y3, z3, t3)
}

pub fn mod_mul<const LIMBS: usize, const BITS: usize>(
    a: [Field; LIMBS],
    b: [Field; LIMBS],
    m: [Field; LIMBS],
    m_minus_1: [Field; LIMBS],
) -> [Field; LIMBS] {
    mul_divmod::<LIMBS, BITS>(a, b, m, m_minus_1).1
}

/// Non-native `a·b` exposing **both** halves of the division: returns
/// `(q, r)` with `q = ⌊a·b / m⌋` and `r = a·b mod m`. Both are range-checked to
/// `LIMBS × BITS` bits, `r` is `assert_lt`'d canonical, and the pair is pinned by
/// `mulmod_columns` (`a·b == q·m + r`), so the quotient is as sound as the
/// remainder. [`mod_mul`] is `.1` of this.
///
/// The quotient is what lets a scaled-division advice (e.g. a GLV lattice
/// reduction's `⌊b·u / n⌋`) be *derived in-circuit* from its inputs rather than
/// supplied as a witness input.
pub fn mul_divmod<const LIMBS: usize, const BITS: usize>(
    a: [Field; LIMBS],
    b: [Field; LIMBS],
    m: [Field; LIMBS],
    m_minus_1: [Field; LIMBS],
) -> ([Field; LIMBS], [Field; LIMBS]) {
    const {
        assert!(
            2 * BITS + 8 < 253,
            "Bignum<LIMBS,BITS>: column products would overflow BN254 Fr"
        );
    }
    let (q, r) = Field::hint_mulmod_divmod::<LIMBS>(a, b, m, BITS);
    let mut i = 0usize;
    while i < LIMBS {
        range_bits::<BITS>(q[i]);
        range_bits::<BITS>(r[i]);
        i += 1;
    }
    assert_lt::<LIMBS, BITS>(r, m_minus_1);
    mulmod_columns::<LIMBS, BITS>(a, b, q, r, m);
    (q, r)
}

/// Non-native modular inverse `a⁻¹ mod m` over `LIMBS` × `BITS`-bit limbs. Output
/// is `≡ a⁻¹` (not forced canonical — benign, as it only feeds a `mod_mul`).
///
/// Specialized: the reduction remainder is *known* to be exactly `1`, so `r` is
/// pinned to the constant `[1,0,…]` instead of being range-checked and
/// canonical-checked as advice — saving the per-inverse range/`assert_lt` work.
pub fn mod_inverse<const LIMBS: usize, const BITS: usize>(
    a: [Field; LIMBS],
    m: [Field; LIMBS],
) -> [Field; LIMBS] {
    const {
        assert!(
            2 * BITS + 8 < 253,
            "Bignum<LIMBS,BITS>: column products would overflow BN254 Fr"
        );
    }
    let w = Field::hint_mod_inverse::<LIMBS>(a, m, BITS);
    range_check_limbs::<LIMBS, BITS>(w);

    let (q, r_hint) = Field::hint_mulmod_divmod::<LIMBS>(a, w, m, BITS);
    range_check_limbs::<LIMBS, BITS>(q);
    // r is exactly 1: pin the hint's remainder outputs to the constant (no range
    // check / assert_lt needed — 1 is trivially a canonical limb).
    let mut r = [Field::from(0u8); LIMBS];
    r[0] = Field::from(1u8);
    let mut i = 0usize;
    while i < LIMBS {
        assert_eq(r_hint[i], r[i]);
        i += 1;
    }
    mulmod_columns::<LIMBS, BITS>(a, w, q, r, m);
    w
}

/// Fused modular subtract `(a - b - c) mod m`, canonical. Precondition
/// `a, b, c < m`. Hints `(qabs ∈ {0,1,2}, r = (a-b-c) mod m)` and verifies the
/// **linear** identity `a + qabs·m == b + c + r` with biased carries — one
/// reduction's worth of work instead of two `mod_sub`.
///
/// SOUNDNESS: `r` is range-checked + `assert_lt`'d (canonical, unique). `qabs` is
/// pinned to `{0,1,2}` (2 bits with the `(1,1)` pattern excluded), so each
/// `lhs[i] = a[i] + qabs·m[i] < 3·2^BITS` and the signed carry stays `|t| ≤ 3`
/// (`cb = t+4 ∈ [1,7]`, range-checked `< 8`).
pub fn sub2<const LIMBS: usize, const BITS: usize>(
    a: [Field; LIMBS],
    b: [Field; LIMBS],
    c: [Field; LIMBS],
    m: [Field; LIMBS],
    m_minus_1: [Field; LIMBS],
) -> [Field; LIMBS] {
    let two_b = two_pow::<BITS>(); // 2^BITS
    let bias = Field::from(4u8);
    let bias_shift = two_pow::<BITS>() * Field::from(4u8); // 4·2^BITS

    let (qabs, r) = Field::hint_sub2::<LIMBS>(a, b, c, m, BITS);
    range_check_limbs::<LIMBS, BITS>(r);
    assert_lt::<LIMBS, BITS>(r, m_minus_1);

    // qabs ∈ {0,1,2}: two bits, exclude the (1,1)=3 pattern.
    let q0 = Field::hint_bit(qabs, 0);
    let q1 = Field::hint_bit(qabs, 1);
    q0.assert_bool();
    q1.assert_bool();
    assert_eq(q0 + q1 + q1, qabs);
    assert_eq(q0 * q1, Field::from(0u8));

    // Column identity a + qabs·m == b + c + r (columns 0..LIMBS-1 hinted; top direct).
    let mut cb_prev = bias;
    let mut i = 0usize;
    while i < LIMBS - 1 {
        let lhs = a[i] + qabs * m[i];
        let rhs = b[i] + c[i] + r[i];
        let num = lhs - rhs + cb_prev + bias_shift - bias;
        let dr = Field::hint_div_rem(num, two_b);
        let cb = dr[0];
        let rem = dr[1];
        assert_eq(num, two_b * cb + rem);
        assert_eq(rem, Field::from(0u8));
        range_lt_8(cb);
        cb_prev = cb;
        i += 1;
    }
    let lhs2 = a[LIMBS - 1] + qabs * m[LIMBS - 1];
    let rhs2 = b[LIMBS - 1] + c[LIMBS - 1] + r[LIMBS - 1];
    let num2 = lhs2 - rhs2 + cb_prev + bias_shift - bias;
    assert_eq(num2, bias_shift);

    r
}

// ===========================================================================
// 3-limb-specific helpers (256-bit scalar layout / affine-point muxes). Not
// width-generalized (tied to the 86+86+84 bit split and affine point shape).
// ===========================================================================

/// 4-bit (16-entry) affine-point mux tree, 3-limb. `b3` is the MSB.
pub fn select16_affine(
    table: [[[Field; 3]; 2]; 16],
    b3: Field,
    b2: Field,
    b1: Field,
    b0: Field,
) -> [[Field; 3]; 2] {
    let mut l1 = [[[Field::from(0u8); 3]; 2]; 8];
    let mut j = 0usize;
    while j < 8usize {
        l1[j] = point_select_affine(b0, table[2 * j + 1], table[2 * j]);
        j += 1;
    }
    let mut l2 = [[[Field::from(0u8); 3]; 2]; 4];
    let mut j = 0usize;
    while j < 4usize {
        l2[j] = point_select_affine(b1, l1[2 * j + 1], l1[2 * j]);
        j += 1;
    }
    let mut l3 = [[[Field::from(0u8); 3]; 2]; 2];
    let mut j = 0usize;
    while j < 2usize {
        l3[j] = point_select_affine(b2, l2[2 * j + 1], l2[2 * j]);
        j += 1;
    }
    point_select_affine(b3, l3[1], l3[0])
}

/// Decompose a 3×86-bit scalar (`< 2^256`) into 256 little-endian pinned bits
/// (`86 + 86 + 84`), enforcing `< 2^256`.
pub fn scalar_to_bits(u: [Field; 3]) -> [Field; 256] {
    let mut bits = [Field::from(0u8); 256];
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 86usize {
        let b = Field::hint_bit(u[0], i);
        b.assert_bool();
        bits[i] = b;
        acc = acc + b * pow;
        pow = pow + pow;
        i += 1;
    }
    assert_eq(acc, u[0]);
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 86usize {
        let b = Field::hint_bit(u[1], i);
        b.assert_bool();
        bits[86 + i] = b;
        acc = acc + b * pow;
        pow = pow + pow;
        i += 1;
    }
    assert_eq(acc, u[1]);
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 84usize {
        let b = Field::hint_bit(u[2], i);
        b.assert_bool();
        bits[172 + i] = b;
        acc = acc + b * pow;
        pow = pow + pow;
        i += 1;
    }
    assert_eq(acc, u[2]);
    bits
}

/// Boolean-gated select between two affine points (`[[Field;3];2]`, 3-limb).
pub fn point_select_affine(
    bit: Field,
    if_true: [[Field; 3]; 2],
    if_false: [[Field; 3]; 2],
) -> [[Field; 3]; 2] {
    bit.assert_bool();
    let mut out = [[Field::from(0u8); 3]; 2];
    let mut c = 0usize;
    while c < 2usize {
        let mut i = 0usize;
        while i < 3usize {
            out[c][i] = if_false[c][i] + bit * (if_true[c][i] - if_false[c][i]);
            i += 1;
        }
        c += 1;
    }
    out
}
