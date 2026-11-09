//! `xark-bignum`: non-native ("foreign field") arithmetic over a 256-bit prime
//! modulus, shared by the secp256k1 / secp256r1 curve gadgets.
//!
//! A field element is a width-generic `Bignum`: `LIMBS` little-endian `BITS`-bit
//! limbs (value `Σ limb[i]·2^(BITS·i)`); callers pick the width (e.g. `<3, 86>`).
//! Every op takes the modulus explicitly (`m` limbs), so one set of routines serves
//! any prime field.
//!
//! Every op assumes its operands' limbs are `< 2^BITS`: its rows prove the integer
//! relation it documents only then. A typed input (`Bignum`, or a type from [`fp!`])
//! is range-checked when it's read, and every op's result is range-checked, so only
//! limbs a circuit builds itself (`Bignum::new`, a `[Field; LIMBS]` parameter) need
//! [`range_check_limbs`] first.
//!
//! In range isn't canonical: only [`mod_mul`]'s and [`sub2`]'s results are `< m`.
//! An input, an inverse, or a sum or difference of them may be `≥ m` while congruent
//! to the right value; check it canonical (`assert_canonical`) before comparing it,
//! testing it for zero, or exposing its limbs.
//!
//! Arithmetic is limb-wise with explicit carry/borrow propagation; carries are
//! range-checked so no intermediate term wraps the BN254 modulus the circuit is
//! proven over (which would silently break the integer identity). A per-instance
//! `const` budget assertion (see [`mod_mul`]) rejects any `(LIMBS, BITS)` whose
//! schoolbook column products could overflow BN254 `Fr`.

#![no_std]
// Gadget code keeps the `x = x + y` style it was written in (the old compiler
// rejected `+=` on `Field`; the wasm frontend accepts both).
#![allow(clippy::assign_op_pattern)]

/// Re-exported so the [`fp!`] macro can name `$crate::Field`.
pub use xark::Field;
use xark::require_eq;

/// Re-exported so the [`fp!`] macro can name `xark` items (`Input`, the host
/// helpers) from the caller's crate.
#[doc(hidden)]
pub use xark as __xark;

// Width-generic non-native modular arithmetic (`Bignum<LIMBS, BITS>`).

/// Max limb count / bit width the fixed decomposition buffers accommodate. Only
/// the first `BITS`/`LIMBS` slots are used; unused constant-zero slots are pruned
/// from the R1CS, so oversizing is free. (Avoids `[Field; BITS + 1]`, which needs
/// unstable `generic_const_exprs`.)
const MAX_BITS: usize = 128;
/// 32 limbs of 86 bits is 2752 bits: room for RSA-2048 (24 limbs) and
/// RSA-2560. Widths above 16 limbs get one more bit of carry headroom (see
/// [`carry_headroom`]); up to 16 the geometry, and so the R1CS, is unchanged.
const MAX_LIMBS: usize = 32;
const MAX_COLS: usize = 2 * MAX_LIMBS - 1;

/// Bits of signed-carry headroom above `BITS` for a `LIMBS`-wide schoolbook
/// column: a column sums up to `LIMBS` products below `2^(2·BITS)`, so its
/// signed carry is below `LIMBS · 2^BITS`. `4` covers `LIMBS ≤ 16`; `5`
/// covers `LIMBS ≤ 32`.
fn carry_headroom<const LIMBS: usize>() -> usize {
    if LIMBS > 16usize { 5usize } else { 4usize }
}

/// Width-generic non-native field element: `LIMBS` little-endian `BITS`-bit limbs
/// (value `Σ limb[i]·2^(BITS·i)`). A zero-cost newtype over `[Field; LIMBS]` whose
/// methods forward to the free functions, so the emitted R1CS is byte-identical.
/// Callers alias a concrete width, e.g. `type Fp = Bignum<3, 86>`.
#[derive(Clone, Copy, Debug)]
pub struct Bignum<const LIMBS: usize, const BITS: usize> {
    pub limbs: [Field; LIMBS],
}

/// A circuit input given as a whole number (a decimal or `0x`-hex string in a
/// client), split into `LIMBS` little-endian `BITS`-bit limbs `<name>.limbs[i]`.
/// Each limb is range-checked as it's read: the prover chooses the limbs, whatever
/// a client's encoder did, and every op assumes them `< 2^BITS`.
impl<const LIMBS: usize, const BITS: usize> xark::Input for Bignum<LIMBS, BITS> {
    const TYPE: xark::input::Type = crate::number_type!("Bignum", LIMBS, BITS);
    fn read(r: &mut xark::input::Reader<'_>) -> Self {
        let limbs = r.read();
        range_check_limbs::<LIMBS, BITS>(limbs);
        Bignum { limbs }
    }
    fn write(&self, w: &mut xark::input::Writer<'_>) {
        w.write(&self.limbs)
    }
}

/// The `Input::TYPE` of a limbed number type `$name`: `{ limbs: [Field; $limbs] }`,
/// given as a whole number of `$bits`-bit limbs. What [`fp!`] types use.
#[doc(hidden)]
#[macro_export]
macro_rules! number_type {
    ($name:expr, $limbs:expr, $bits:expr) => {
        $crate::__xark::input::Type::Named(&$crate::__xark::input::Named {
            name: $name,
            arg: ::core::option::Option::None,
            layout: $crate::__xark::input::Layout::Struct(&[$crate::__xark::input::Member::new(
                "limbs",
                <[$crate::Field; $limbs] as $crate::__xark::Input>::TYPE,
            )]),
            encoding: $crate::__xark::input::Encoding::Number { bits: $bits },
        })
    };
}

// Host side: a `Bignum` value is one whole number, from a decimal or `0x`-hex string
// or its big-endian bytes, split into `LIMBS` little-endian `BITS`-bit limbs: callers
// pass the value, never hand-decompose. `std` is pulled in inside an anonymous const
// (this crate is `#![no_std]`).
#[cfg(not(xark))]
const _: () = {
    extern crate std;
    use std::string::String;
    impl<const LIMBS: usize, const BITS: usize> xark::host::FromBeBytes for Bignum<LIMBS, BITS> {
        const BYTES: usize = xark::host::natural_bytes(LIMBS, BITS);
        fn from_be_bytes(bytes: &[u8]) -> Self {
            Bignum {
                limbs: xark::host::limb_fields::<LIMBS>(bytes, BITS as u32),
            }
        }
    }
    impl<const LIMBS: usize, const BITS: usize> From<&str> for Bignum<LIMBS, BITS> {
        fn from(value: &str) -> Self {
            Bignum {
                limbs: xark::host::limb_fields_str::<LIMBS>(value, BITS as u32),
            }
        }
    }
    impl<const LIMBS: usize, const BITS: usize> From<String> for Bignum<LIMBS, BITS> {
        fn from(value: String) -> Self {
            Self::from(value.as_str())
        }
    }
    impl<const LIMBS: usize, const BITS: usize> From<u128> for Bignum<LIMBS, BITS> {
        fn from(value: u128) -> Self {
            <Self as xark::host::FromBeBytes>::from_be_bytes(&value.to_be_bytes())
        }
    }
    impl<const LIMBS: usize, const BITS: usize> From<u64> for Bignum<LIMBS, BITS> {
        fn from(value: u64) -> Self {
            Self::from(value as u128)
        }
    }
    /// An untyped literal (`Bignum::from(6)`); panics on a negative value.
    impl<const LIMBS: usize, const BITS: usize> From<i32> for Bignum<LIMBS, BITS> {
        fn from(value: i32) -> Self {
            Self::from(u128::try_from(value).expect("a bignum value is non-negative"))
        }
    }
};

impl<const LIMBS: usize, const BITS: usize> Bignum<LIMBS, BITS> {
    /// Limb count and bit width, exposed so `fp!(Name, "0x…", ThisType)` can read
    /// the geometry off a `Bignum<LIMBS, BITS>` alias.
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

    /// `(self · rhs) mod m`.
    pub fn mul(self, rhs: Self, m: Self) -> Self {
        let limbs = mod_mul::<LIMBS, BITS>(self.limbs, rhs.limbs, m.limbs);
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
    pub fn sub2(self, b: Self, c: Self, m: Self) -> Self {
        let limbs = sub2::<LIMBS, BITS>(self.limbs, b.limbs, c.limbs, m.limbs);
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

/// The headroom an [`fp!`] field needs: `3·m < 2^(N·BITS)`. `mod_add` sums two
/// canonical values and `triple` / `sub2` build `3·v` / `a + 2m` in `N` limbs, each
/// with its top carry required to be zero, so a modulus closer to the limb capacity
/// would make honest operations fail (a completeness bug, not a soundness one).
/// Checked on the top limb (`(top + 1)·3 ≤ 2^BITS` implies it); every curve field
/// here (≤ 256 bits in 3 × 86) has two bits to spare. A compile error otherwise.
pub const fn assert_fp_headroom<const N: usize, const BITS: usize>(s: &str) {
    let v = parse_limbs::<N, BITS>(s);
    assert!(
        N > 0 && v[N - 1] < ((1u128 << BITS) - 1) / 3,
        "fp!: modulus too close to the limb capacity — need 3·m < 2^(LIMBS·BITS)"
    );
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
/// Give it the name and the modulus (decimal or `0x`-hex); a `~256`-bit field
/// defaults to the `3 × 86`-bit layout. An optional trailing `LIMBS, BITS` picks a
/// different geometry: `fp!(Fp, "0x…", 4, 64)`. The limb split, `m − 1`, and the
/// `2^(BITS·LIMBS) − m` subtraction complement are derived at compile time; the
/// generated type is a zero-cost `[Field; LIMBS]` newtype forwarding to the
/// width-generic free functions.
#[macro_export]
macro_rules! fp {
    // Two-arg form: ~256-bit prime field, default 3 × 86-bit layout (86 bits is
    // multiply-optimal over BN254).
    ($vis:vis $name:ident, $modulus:literal) => {
        $crate::fp!(@build checked $vis $name, $modulus, 3, 86);
        $crate::fp!(@host $name, 3, 86);
    };
    // Inputs read WITHOUT the limb range check, for code that checks every input it
    // takes itself (the curve gadgets pin each coordinate and scalar canonical before
    // any arithmetic), so the check isn't paid twice.
    (unchecked_input $vis:vis $name:ident, $modulus:literal) => {
        $crate::fp!(@build raw $vis $name, $modulus, 3, 86);
        $crate::fp!(@host $name, 3, 86);
    };
    (unchecked_input $vis:vis $name:ident, $modulus:literal, $limbs:literal, $bits:literal) => {
        $crate::fp!(@build raw $vis $name, $modulus, $limbs, $bits);
        $crate::fp!(@host $name, $limbs, $bits);
    };
    // Same, but WITHOUT the host conversions: for callers that supply their own (e.g.
    // curves give a byte host via `curve_host_inputs!`), so the two don't clash.
    (no_host $vis:vis $name:ident, $modulus:literal) => {
        $crate::fp!(@build checked $vis $name, $modulus, 3, 86);
    };
    // Storage only: `LIMBS` × `BITS`-bit limbs with no modulus and no arithmetic — an
    // input wrapper for code that does its own limb arithmetic (e.g. a lazy-reduction
    // path whose modulus has no headroom for `fp!`'s operators).
    (storage $vis:vis $name:ident, $limbs:literal, $bits:literal) => {
        #[derive(Clone, Copy, Debug)]
        $vis struct $name {
            pub limbs: [$crate::Field; $limbs],
        }
        $crate::fp!(@input raw $name, $limbs, $bits);
        #[allow(dead_code)]
        impl $name {
            /// Wrap `LIMBS` little-endian `BITS`-bit limbs.
            pub fn new(limbs: [$crate::Field; $limbs]) -> Self {
                Self { limbs }
            }
            /// Range-check every limb to `[0, 2^BITS)`.
            pub fn range_check(self) {
                $crate::range_check_limbs::<{ $limbs }, { $bits }>(self.limbs)
            }
        }
        $crate::fp!(@host $name, $limbs, $bits);
    };
    // `no_host` with an explicit limb layout.
    (no_host $vis:vis $name:ident, $modulus:literal, $limbs:literal, $bits:literal) => {
        $crate::fp!(@build checked $vis $name, $modulus, $limbs, $bits);
    };
    // Geometry from a `Bignum<LIMBS, BITS>` type — `fp!(Fp, "0x…", Scalar)`.
    ($vis:vis $name:ident, $modulus:literal, $geom:ty) => {
        $crate::fp!(@build checked $vis $name, $modulus, { <$geom>::LIMBS }, { <$geom>::BITS });
        $crate::fp!(@host $name, { <$geom>::LIMBS }, { <$geom>::BITS });
    };
    // Explicit limb layout: `fp!(Fp, "0x…", 4, 64)`.
    ($vis:vis $name:ident, $modulus:literal, $limbs:literal, $bits:literal) => {
        $crate::fp!(@build checked $vis $name, $modulus, $limbs, $bits);
        $crate::fp!(@host $name, $limbs, $bits);
    };
    // A circuit input given as one whole number (a decimal or `0x`-hex string in a
    // client), split into `$limbs` little-endian `$bits`-bit limbs `<name>.limbs[i]`.
    // `checked`: each limb is range-checked as it's read (the prover chooses the
    // limbs, whatever the client encoded); `raw`: the caller checks.
    (@input checked $name:ident, $limbs:expr, $bits:expr) => {
        $crate::fp!(@input_impl $name, $limbs, $bits, |limbs| {
            $crate::range_check_limbs::<{ $limbs }, { $bits }>(limbs)
        });
    };
    (@input raw $name:ident, $limbs:expr, $bits:expr) => {
        $crate::fp!(@input_impl $name, $limbs, $bits, |_limbs| {});
    };
    (@input_impl $name:ident, $limbs:expr, $bits:expr, $check:expr) => {
        impl $crate::__xark::Input for $name {
            const TYPE: $crate::__xark::input::Type =
                $crate::number_type!(stringify!($name), $limbs, $bits);
            fn read(r: &mut $crate::__xark::input::Reader<'_>) -> Self {
                let limbs: [$crate::Field; $limbs] = r.read();
                let check: fn([$crate::Field; $limbs]) = $check;
                check(limbs);
                Self { limbs }
            }
            fn write(&self, w: &mut $crate::__xark::input::Writer<'_>) {
                w.write(&self.limbs)
            }
        }
    };
    // Host conversions: the element from its 32 big-endian bytes, a decimal (or
    // `0x`-hex) string, or an integer, split into `$limbs` little-endian `$bits`-bit
    // limbs. Host-only.
    (@host $name:ident, $limbs:expr, $bits:expr) => {
        #[cfg(not(xark))]
        const _: () = {
            extern crate std;
            use std::string::String;
            impl $crate::__xark::host::FromBeBytes for $name {
                const BYTES: usize = 32;
                fn from_be_bytes(bytes: &[u8]) -> Self {
                    Self { limbs: $crate::__xark::host::limb_fields::<{ $limbs }>(bytes, $bits as u32) }
                }
            }
            /// From the value's 32 big-endian bytes.
            impl From<[u8; 32]> for $name {
                fn from(bytes: [u8; 32]) -> Self {
                    <Self as $crate::__xark::host::FromBeBytes>::from_be_bytes(&bytes)
                }
            }
            /// From a decimal or `0x`-hex string.
            impl From<&str> for $name {
                fn from(value: &str) -> Self {
                    Self { limbs: $crate::__xark::host::limb_fields_str::<{ $limbs }>(value, $bits as u32) }
                }
            }
            impl From<String> for $name {
                fn from(value: String) -> Self {
                    Self::from(value.as_str())
                }
            }
            impl From<u128> for $name {
                fn from(value: u128) -> Self {
                    Self { limbs: $crate::__xark::host::limb_fields::<{ $limbs }>(&value.to_be_bytes(), $bits as u32) }
                }
            }
            impl From<u64> for $name {
                fn from(value: u64) -> Self {
                    Self::from(value as u128)
                }
            }
            /// An untyped literal; panics on a negative value.
            impl From<i32> for $name {
                fn from(value: i32) -> Self {
                    Self::from(u128::try_from(value).expect("a field value is non-negative"))
                }
            }
        };
    };
    (@build $check:ident $vis:vis $name:ident, $modulus:literal, $limbs:expr, $bits:expr) => {
        #[derive(Clone, Copy, Debug)]
        $vis struct $name {
            pub limbs: [$crate::Field; $limbs],
        }
        $crate::fp!(@input $check $name, $limbs, $bits);
        #[allow(dead_code)]
        impl $name {
            const M: [$crate::Field; $limbs] = {
                $crate::assert_fp_headroom::<{ $limbs }, { $bits }>($modulus);
                $crate::modulus_limbs::<{ $limbs }, { $bits }>($modulus)
            };
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
                Self::new($crate::sub2_bounded::<{ $limbs }, { $bits }>(self.limbs, b.limbs, c.limbs, Self::M, Self::M1))
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
                $crate::require_lt::<{ $limbs }, { $bits }>(self.limbs, Self::M1);
            }
            /// Assert this element is nonzero mod `m`. It's checked canonical (`< m`)
            /// first: a range-checked value can be `m` itself, whose limbs aren't zero
            /// though it is. (Its limbs must be range-checked, as inputs and results are.)
            pub fn assert_nonzero(self) {
                $crate::require_lt::<{ $limbs }, { $bits }>(self.limbs, Self::M1);
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
                Self::new($crate::mod_mul_bounded::<{ $limbs }, { $bits }>(self.limbs, rhs.limbs, Self::M, Self::M1))
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

/// Decompose `v` into `BITS + EXTRA` little-endian bits (boolean-constrained and
/// recomposition-pinned; top borrow/carry bit at index `BITS`). `EXTRA` is the
/// headroom above `BITS`: `1` for a single carry bit, `2` for a doubled term.
fn decompose_top<const BITS: usize, const EXTRA: usize>(v: Field) -> [Field; MAX_BITS] {
    let mut bits = [Field::from(0u8); MAX_BITS];
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < BITS + EXTRA {
        let bit = Field::hint_bit(v, i);
        bit.require_bool();
        bits[i] = bit;
        acc = acc + bit * pow;
        pow = pow + pow;
        i += 1;
    }
    require_eq(acc, v);
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
        bit.require_bool();
        acc = acc + bit * pow;
        pow = pow + pow;
        i += 1;
    }
    require_eq(acc, v);
}

/// Range-check a biased column carry `v < 2^(BITS + headroom + 2)` (the
/// `mulmod_columns` carries: a signed carry in `[−2^(BITS+headroom),
/// 2^(BITS+headroom))` biased by `2^(BITS+headroom)`, with a bit to spare).
fn range_bits_carry<const LIMBS: usize, const BITS: usize>(v: Field) {
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < BITS + carry_headroom::<LIMBS>() + 2usize {
        let bit = Field::hint_bit(v, i);
        bit.require_bool();
        acc = acc + bit * pow;
        pow = pow + pow;
        i += 1;
    }
    require_eq(acc, v);
}

/// Range-check `v < 2^3` (small biased `sub2` carries, width-independent).
fn range_lt_8(v: Field) {
    let b0 = Field::hint_bit(v, 0);
    let b1 = Field::hint_bit(v, 1);
    let b2 = Field::hint_bit(v, 2);
    b0.require_bool();
    b1.require_bool();
    b2.require_bool();
    require_eq(b0 + b1 + b1 + b2 + b2 + b2 + b2, v);
}

/// Range-check each limb of `x` to `[0, 2^BITS)` (proven: `formal/Formal/RangeCheckLimbs.lean`).
#[xark::gadget]
pub fn range_check_limbs<const LIMBS: usize, const BITS: usize>(x: [Field; LIMBS]) {
    let mut i = 0usize;
    while i < LIMBS {
        range_bits::<BITS>(x[i]);
        i += 1;
    }
}

/// Modular negation `(m - b) mod m`, canonical (enforces `b <= m`; `b = 0` and
/// `b = m` give `0`). `b`'s limbs must be range-checked (`< 2^BITS`): `b ≤ m` is
/// read off the borrow chain, which assumes them.
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
    require_eq(borrow, Field::from(0u8));
    // `b = 0` gives `out = m`: map it to the canonical `0`. `out = m` is tested
    // limb-wise — `Σ (out[i] − m[i])²` is an integer below Fr (every `out[i]` is
    // range-checked, so each square is `< 2^(2·BITS)`), hence zero exactly when every
    // limb matches. (Comparing the two recompositions in Fr is not exact: 256-bit
    // values wrap, so `b = k·Fr` would also match.)
    const {
        assert!(
            2 * BITS + ((usize::BITS - LIMBS.leading_zeros()) as usize) < 253,
            "mod_neg: the limb-difference sum must stay below Fr"
        )
    };
    let mut sq = Field::from(0u8);
    let mut i = 0usize;
    while i < LIMBS {
        let d = out[i] - m[i];
        sq = sq + d * d;
        i += 1;
    }
    let is_m = Field::from(sq == Field::from(0u8));
    let mut i = 0usize;
    while i < LIMBS {
        out[i] = out[i] - is_m * m[i];
        i += 1;
    }
    out
}

/// Modular addition `(a + b) mod m`. Precondition `a, b < m`, so `a+b < 2m` fits
/// in `LIMBS` limbs and one conditional subtraction of `m` suffices; the output is
/// then canonical. Outside it (a non-canonical operand, e.g. a `mod_inverse`
/// output), a sum that overflows the limbs is rejected (its top carry is pinned to
/// 0) rather than wrapped, so the result is always `≡ a + b (mod m)`.
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
    require_eq(carry, Field::from(0u8));
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

/// Modular subtraction `(a - b) mod m`. Two-pass: `diff = a - b` (borrow = `[a<b]`),
/// then `result = diff - borrow·comp`, where `comp = 2^(BITS·LIMBS) − m` is the
/// caller-supplied complement of `m`.
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
    require_eq(borrow2, Field::from(0u8));
    result
}

/// `(3·v) mod m` for `v < m`. Forms the exact triple `3v < 3m` (per-limb
/// `3·v[i] + carry < 2^(BITS+2)`, `carry ∈ [0,3]`) in one scaling pass, then reduces
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
    require_eq(carry, Field::from(0u8)); // 3v < 2^(BITS·LIMBS) ⇒ no top overflow
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

/// Enforce `x < m`, i.e. `x ≤ m − 1` (`m_minus_1`), compared lexicographically from
/// the top limb. `x`'s limbs must be `< 2^BITS`, range-checked by the caller; `m − 1`'s
/// limbs `< 2^BITS` too for an honest `x` to be accepted (completeness only).
///
/// A chunked comparison (zkGolf RSA record 31516100, "chunked lexicographic
/// `sig < n`"): instead of a full borrow chain (`LIMBS·(BITS+1)` bits), the prover
/// names the top limb `k` where `x` and `m − 1` differ; the rows check that every
/// limb above `k` is equal and that `m₋₁[k] − 1 − x[k]` is a `BITS`-bit number. The
/// hint `n[j]` is `1` iff they differ at limb `j` or above; `f[k] = n[k] − n[k+1]`
/// is the one-hot "first difference at `k`" (`n[0] = 0`: they are equal). Cost
/// `4·LIMBS + BITS` rows. Proven sound and complete over its exact rows at the widths
/// production uses, 3 × 86, 3 × 85 and 4 × 64 (`formal/Formal/RequireLt*.lean`); a
/// constant `m − 1` is that template with constant plugs (`cargo xtask lean-export
/// --coverage`). Other widths are not exported.
#[xark::gadget]
pub fn require_lt<const LIMBS: usize, const BITS: usize>(
    x: [Field; LIMBS],
    m_minus_1: [Field; LIMBS],
) {
    // The hint operand below is `< 2^(BITS+3)`, and the selected difference must not
    // wrap the field from below (`−2^BITS − 1 + r ≥ 2^BITS`).
    const { assert!(BITS + 3 < 253, "require_lt: limbs too wide for BN254 Fr") };
    let one = Field::from(1u8);
    let zero = Field::from(0u8);
    // n[j] = bit BITS+2 of `d_j − 1 + 2^(BITS+1)·n[j+1] + 2^(BITS+2)`, `d_j = m₋₁[j] − x[j]`:
    // with the limbs above equal (`n[j+1] = 0`, so `d_j ≥ 0` for an honest `x`) it is
    // `[d_j > 0]`; once they differ it stays `1`.
    let mut n = [zero; LIMBS];
    let mut above = zero;
    let mut j = LIMBS;
    while j > 0 {
        j -= 1;
        let t = m_minus_1[j] - x[j] - one + above * two_pow_big(BITS + 1) + two_pow_big(BITS + 2);
        n[j] = Field::hint_bit(t, BITS + 2);
        above = n[j];
    }
    // Every n[j] is a bit, and f[k] = n[k] − n[k+1] is a bit: going up, the flags fall
    // from 1 to 0 at most once, so at most one f[k] is 1. (Each flag gets its own
    // booleanity row, so the witness search sees its domain.)
    let mut j = 0usize;
    while j < LIMBS {
        n[j].require_bool();
        j += 1;
    }
    let mut k = 0usize;
    while k + 1 < LIMBS {
        (n[k] - n[k + 1]).require_bool();
        k += 1;
    }
    // Where n[j] = 0 (no difference at j or above), the limbs are equal.
    let mut j = 0usize;
    while j < LIMBS {
        require_eq((one - n[j]) * (x[j] - m_minus_1[j]), zero);
        j += 1;
    }
    // At the first difference k: m₋₁[k] − 1 − x[k] ∈ [0, 2^BITS), i.e. x[k] < m₋₁[k].
    let mut d = zero;
    let mut k = 0usize;
    while k < LIMBS {
        let up = if k + 1 < LIMBS { n[k + 1] } else { zero };
        d = d + (n[k] - up) * (m_minus_1[k] - one - x[k]);
        k += 1;
    }
    range_bits::<BITS>(d);
}

/// `2^e` as a field constant, for `e < 253`.
fn two_pow_big(e: usize) -> Field {
    let mut p = Field::from(1u8);
    let mut i = 0usize;
    while i < e {
        p = p + p;
        i += 1;
    }
    p
}

/// Pinned boolean `lt ∈ {0,1}`, `1` iff `a < b`, over two canonical limb vectors
/// (each limb `< 2^BITS`).
///
/// A subtract-with-borrow: each
/// `d_i = a[i] − b[i] − borrow + 2^BITS ∈ [0, 2^(BITS+1))` is bit-decomposed, so
/// every term stays `< 2^(BITS+1)` (nothing wraps the field) and the final borrow
/// is exactly the `a < b` bit. Unlike [`require_lt`], which only asserts the order,
/// this returns it, so a caller can mux/derive advice (rounding carries, GLV signs)
/// in-circuit rather than take it as a witness input.
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

/// Assert the limbs encode a nonzero value (not all zero). Assumes range-checked limbs,
/// and says nothing mod `m`: `m` itself passes. For "nonzero mod `m`", check the value
/// canonical first (`require_lt` against `m − 1`), as `fp!`'s `assert_nonzero` does.
pub fn assert_nonzero_limbs<const LIMBS: usize>(limbs: [Field; LIMBS]) {
    // all_zero = AND of isZero(limbᵢ); require == 0 to forbid value 0.
    let mut all_zero = Field::from(1u8);
    let mut i = 0usize;
    while i < LIMBS {
        all_zero = all_zero.and(Field::from(limbs[i].is_zero()));
        i += 1;
    }
    require_eq(all_zero, Field::from(0u8));
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
    const {
        assert!(LIMBS <= MAX_LIMBS, "Bignum<LIMBS,BITS>: at most 32 limbs");
    }
    let headroom = carry_headroom::<LIMBS>();
    let two_b = two_pow::<BITS>(); // 2^BITS
    let bias = Field::from(1u128 << (BITS + headroom)); // 2^(BITS+h)
    let bias_shift = two_b * two_b * Field::from(1u128 << headroom); // 2^(2·BITS+h)

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
        require_eq(num, two_b * cb + rem);
        require_eq(rem, Field::from(0u8));
        range_bits_carry::<LIMBS, BITS>(cb);
        cb_prev = cb;
        c += 1;
    }
    let num_top = lhs[2 * LIMBS - 2] - rhs[2 * LIMBS - 2] + cb_prev + bias_shift - bias;
    require_eq(num_top, bias_shift);
}

/// `2^255 − 19 − 1` in 3 × 85 bits (the canonical-coordinate bound).
pub const P1_25519_L: [Field; 3] = modulus_minus_1::<3, 85>(
    "57896044618658097711785492504343953926634992332820282019728792003956564819949",
);

/// secp256k1's `p = 2²⁵⁶ − 2³² − 977`.
const P_K1: &str = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F";
/// secp256k1's `p` as 8 × 32-bit limbs.
pub const M_K1: [Field; 8] = modulus_limbs::<8, 32>(P_K1);
/// secp256k1 `p − 1` (the canonical-coordinate bound).
pub const M1_K1: [Field; 8] = modulus_minus_1::<8, 32>(P_K1);

/// `L` and `H` read off `mul_cert_k1`'s 15 products (the points of `mul_cert_r1`):
/// `CERT_K1_LO[i] = Σₘ ℓₘ·V[m][i]`, `CERT_K1_HI[i] = Σₘ hₘ·V[m][i]`, where
/// `ℓₘ + 2¹⁹²·hₘ ≡ 2³²ᵐ (mod p)` is `Y^m mod (Y⁸ − Y − 977)` at `Y = 2³²` split after its
/// sixth word. `formal/Formal/MulCertK1.lean` checks both against `ℓₘ`, `hₘ`.
const CERT_K1_LO: [Field; 15] = [
    Field::constant("1185733791817175022924712974372438372930331471981874800876400346553703665820"),
    Field::constant("7532377983992352815137279022198273432546786243903279580690534117658497852353"),
    Field::constant(
        "10237718478628148948426570229423619173256326742102272297913238835664122004457",
    ),
    Field::constant(
        "10850163885430594293735379828443965351958623545011669517140021837554759680171",
    ),
    Field::constant(
        "10691117041282485274483783370715796550464560397292781489540265443495529268402",
    ),
    Field::constant(
        "10860315677969016130201661141405999631129693614428688990903574755512392632291",
    ),
    Field::constant(
        "16845418279115332233300572511199137856384274120405836469367313639984371187519",
    ),
    Field::constant("7928773172434777067688383830053622879226049343510124887642735433025465636762"),
    Field::constant(
        "16522777449214461328590402147427895175322553478147089556486169886447861666155",
    ),
    Field::constant(
        "19933809010125723664382691202677368595697780682608913001042218029890503837260",
    ),
    Field::constant("877666827331549468968552482651778577334417800136540938553767841025196345246"),
    Field::constant("6186660721010143203533947949968427630060060682098791620460582437277471902486"),
    Field::constant("6903521529107129656182174853046909266036249220349851901115147460033591939641"),
    Field::constant(
        "21684874967306821419958251029878516373870424578988495502089209256327725947614",
    ),
    Field::constant("4976771288109216028210477643337176753620418881946029852066249985579465903143"),
];
const CERT_K1_HI: [Field; 15] = [
    Field::constant(
        "13664932669112099558665935279408846895990012125573381725638317743123828173913",
    ),
    Field::constant(
        "21017012331653453178142334382536636896629931490715088662321988677576698930358",
    ),
    Field::constant(
        "21223929151411029362292121161716184372091884541167847631164253095832745299952",
    ),
    Field::constant("987216774258473263016157449014370990855809970460967348519945688807136144636"),
    Field::constant("2202970899181122291888048653488803474052057403070825878671174453476841147902"),
    Field::constant(
        "13736900096536105253864899174170296302103524093497413289595852738235375547592",
    ),
    Field::constant("259611743084534558328784880018628833317462659541925602081610242809938929632"),
    Field::constant(
        "19603223048775668526003641225862530649311861795096711982004773914503699124534",
    ),
    Field::constant(
        "20387273191593784122466225645866680361756505342368749425139765072786670327490",
    ),
    Field::constant("6356916758059472108445955439562923497540805376917122688284337237921240484164"),
    Field::constant("1126245767620976072817494277447469608899171266077625386795617102904432169773"),
    Field::constant(
        "14938918974887429192259175206759202241312708206213877778090414796067169259856",
    ),
    Field::constant(
        "18975171280271419092692614814171024569928375879885914690398587556454867393181",
    ),
    Field::constant("1445234999368244946873091531628341940124632218446465639779110317152194271662"),
    Field::constant(
        "19180385288900390250214766840406260074472172834294357021099884854953630760291",
    ),
];
/// Limb bound `mul_cert_k1` assumes of `a`, `b` and `t` (`< 2^CERT_K1_IN`, caller-enforced).
const CERT_K1_IN: usize = 34;
/// Widths of the range-checked `K + 8` and `T + 8`.
const CERT_K1_K: usize = 40;
const CERT_K1_T: usize = 47;

/// Assert `a·b ≡ t (mod p)` for secp256k1's `p = 2²⁵⁶ − c`, `c = 2³² + 977`, over 8 × 32-bit
/// limbs that may be unreduced (each limb of `a`, `b`, `t` in `[0, 2^34)`, which the caller
/// enforces). The limb products come from the 15 rows of [`mul_cert_r1`] (interpolation at
/// small points, linear; Winograd/Toom); folding each column `2³²ᵐ` mod `Y⁸ − Y − 977`
/// (`= p` at `Y = 2³²`, coefficients in `[0, 977²]`) splits `E ≡ a·b − t` as `L + 2¹⁹²·H`,
/// `L < 2²³⁹`, `|H| < 2¹⁰⁴`. Since `p = 2²⁵⁶ − c`, `E = K·p` iff `L + c·K = 2¹⁹²·(2⁶⁴·K − H)`:
/// one row, with `K + 8` and `T + 8` (`T = 2⁶⁴·K − H`) range-checked in 40 and 47 bits. The
/// honest `K = ⌊(H + 2⁶³)/2⁶⁴⌋` comes from one `div_rem`. `15 + 40 + 47 + 1` rows. Proven
/// sound and complete over its exported rows (`formal/Formal/MulCertK1.lean`).
#[xark::gadget]
pub fn mul_cert_k1(a: [Field; 8], b: [Field; 8], t: [Field; 8]) {
    // No-wrap budget (bug checklist 5), proven exactly in MulCertK1.lean: a column is
    // `< 8·2^(2·CERT_K1_IN)` and `Σ ℓₘ·cntₘ < 2^171`, so `0 ≤ L + 2^198 < 2^240`,
    // `|H| < 2^104`, `c·|K|`, `2^192·|T|` stay far below `r/2`; the honest `K + 8`, `T + 8`
    // lie in `[0, 2^40)`, `[0, 2^47)` (MulCertK1.int_complete).
    const {
        assert!(2 * CERT_K1_IN + 3 + 171 < 252 && 192 + CERT_K1_T < 252);
        assert!(64 + CERT_K1_K < 252 && 33 + CERT_K1_K < 252);
    };
    let (mut lo, mut hi) = cert_products(a, b, CERT_K1_LO, CERT_K1_HI);
    let two32 = Field::from(1u64 << 32);
    let mut w = Field::from(1u8);
    let mut k = 0usize;
    while k < 6 {
        lo -= w * t[k];
        w *= two32;
        k += 1;
    }
    hi = hi - t[6] - two32 * t[7];
    // `K + 8 = ⌊(H + 2⁶³ + 2⁶⁷)/2⁶⁴⌋`; the `div_rem` remainder is scratch.
    xark::witness_begin();
    let q = Field::hint_div_rem(hi + two_pow_big(63) + two_pow_big(67), two_pow_big(64))[0];
    xark::witness_end();
    let kk = q - Field::from(8u8);
    let tt = kk * two_pow_big(64) - hi;
    let _ = (kk + Field::from(8u8)).to_bits::<CERT_K1_K>();
    let _ = (tt + Field::from(8u8)).to_bits::<CERT_K1_T>();
    require_eq(lo + Field::from(4294968273u64) * kk, two_pow_big(192) * tt);
}

/// `(a·b) mod p` and `(a − b − c) mod p` as hints (no rows); the caller pins them.
fn hint_mul_k1(a: [Field; 8], b: [Field; 8]) -> [Field; 8] {
    Field::hint_mulmod_divmod::<8>(a, b, M_K1, 32).1
}
fn hint_sub2_k1(a: [Field; 8], b: [Field; 8], c: [Field; 8]) -> [Field; 8] {
    Field::hint_sub2::<8>(a, b, c, M_K1, 32).1
}
/// `2p` limb-wise (each limb in `[2³³ − 1954, 2³³)`): a bias keeping `2p + u − v` limbs in
/// `[0, 2^34)` for `u` limbs `< 2^33` and `v` limbs `< 2^32`. A caller may pass `2p − y` for
/// `−y`.
pub fn b2_k1() -> [Field; 8] {
    let two = Field::from(2u8);
    let mut out = M_K1;
    let mut i = 0usize;
    while i < 8 {
        out[i] = two * M_K1[i];
        i += 1;
    }
    out
}

/// Incomplete affine addition on secp256k1: the honest `w = (x_Q − x_P)⁻¹`, `λ`, `x₃`, `y₃`
/// as hints in a witness region, pinned by [`ec_add_k1_check`]. Inputs: `P`'s and `x_Q`'s
/// limbs `< 2^32`, `y_Q`'s `< 2^33` (so a caller can pass `2p − y` for `−Q`); outputs: limbs
/// `< 2^32`, canonical for an honest prover.
pub fn ec_add_k1(
    px: [Field; 8],
    py: [Field; 8],
    qx: [Field; 8],
    qy: [Field; 8],
) -> ([Field; 8], [Field; 8]) {
    let (one, m1) = (Field::from(1u8), Field::from(0u8) - Field::from(1u8));
    let b2 = b2_k1();
    let zero8 = [Field::from(0u8); 8];
    xark::witness_begin();
    let w = Field::hint_mod_inverse::<8>(lin8(b2, qx, one, px, m1), M_K1, 32);
    let lam = hint_mul_k1(lin8(b2, qy, one, py, m1), w);
    let x3 = hint_sub2_k1(hint_mul_k1(lam, lam), px, qx);
    let y3 = hint_sub2_k1(hint_mul_k1(lam, hint_sub2_k1(px, x3, zero8)), py, zero8);
    xark::witness_end();
    ec_add_k1_check(px, py, qx, qy, w, lam, x3, y3);
    (x3, y3)
}

/// The rows of [`ec_add_k1`]: `w`, `λ`, `x₃`, `y₃` range-checked below `2^32` and the
/// certificates `w·Δx ≡ 1` (the chord guard: it rules out `x_P ≡ x_Q`, where the slope
/// certificate would leave `λ` free, bug checklist 1), `λ·Δx ≡ Δy`, `λ² ≡ x₃ + x_P + x_Q`,
/// `λ·(2p + x_P − x₃) ≡ y₃ + y_P`, with `Δ = 2p + Q − P` limb-wise (the bias keeps every
/// operand limb non-negative). Proven in `formal/Formal/EcK1Check.lean`: on `P`, `x_Q` limbs
/// `< 2^32` and `y_Q` limbs `< 2^33`, every satisfying assignment has `x_P ≢ x_Q` and
/// `(x₃, y₃) = P + Q` for affine `P`, `Q`, with limbs `< 2^32`.
#[xark::gadget]
#[allow(clippy::too_many_arguments)]
pub fn ec_add_k1_check(
    px: [Field; 8],
    py: [Field; 8],
    qx: [Field; 8],
    qy: [Field; 8],
    w: [Field; 8],
    lam: [Field; 8],
    x3: [Field; 8],
    y3: [Field; 8],
) {
    let (z, one, m1) = (
        Field::from(0u8),
        Field::from(1u8),
        Field::from(0u8) - Field::from(1u8),
    );
    let b2 = b2_k1();
    let zero8 = [z; 8];
    range32(w);
    range32(lam);
    range32(x3);
    range32(y3);
    let dx = lin8(b2, qx, one, px, m1);
    let mut unit = zero8;
    unit[0] = one;
    mul_cert_k1(w, dx, unit);
    mul_cert_k1(lam, dx, lin8(b2, qy, one, py, m1));
    mul_cert_k1(lam, lam, lin8(x3, px, one, qx, one));
    mul_cert_k1(lam, lin8(b2, px, one, x3, m1), lin8(y3, py, one, zero8, z));
}

/// The fused incomplete step `(A + S) + A = 2A + S` on secp256k1, without `A + S`'s `y`
/// (Eisenträger–Lauter–Montgomery, arXiv math/0208038; gnark `doubleAndAdd`; zkGolf
/// 9489f82f): `w = (x_S − x_A)⁻¹`, the slopes `λ₁`, `λ₂`, `x_R` and the result as hints in a
/// witness region, pinned by [`ec_double_add_k1_check`]. `A`'s and `x_S`'s limbs are below
/// `2^32`; `y_S`'s may be up to `2^33`, so a caller can pass `2p − y` for `−S`.
pub fn ec_double_add_k1(
    ax: [Field; 8],
    ay: [Field; 8],
    sx: [Field; 8],
    sy: [Field; 8],
) -> ([Field; 8], [Field; 8]) {
    let (z, one, m1) = (
        Field::from(0u8),
        Field::from(1u8),
        Field::from(0u8) - Field::from(1u8),
    );
    let b2 = b2_k1();
    let zero8 = [z; 8];
    xark::witness_begin();
    let w = Field::hint_mod_inverse::<8>(lin8(b2, sx, one, ax, m1), M_K1, 32);
    let l1 = hint_mul_k1(lin8(b2, sy, one, ay, m1), w);
    let xr = hint_sub2_k1(hint_mul_k1(l1, l1), ax, sx);
    let ar = hint_sub2_k1(ax, xr, zero8);
    let two_ay = lin8(zero8, ay, Field::from(2u8), zero8, z);
    let l2 = hint_sub2_k1(
        hint_mul_k1(two_ay, Field::hint_mod_inverse::<8>(ar, M_K1, 32)),
        l1,
        zero8,
    );
    let x3 = hint_sub2_k1(hint_mul_k1(l2, l2), xr, ax);
    let y3 = hint_sub2_k1(hint_mul_k1(l2, hint_sub2_k1(ax, x3, zero8)), ay, zero8);
    xark::witness_end();
    ec_double_add_k1_check(ax, ay, sx, sy, w, l1, xr, l2, x3, y3);
    (x3, y3)
}

/// The rows of [`ec_double_add_k1`]: `w`, `λ₁`, `x_R`, `λ₂`, `x₃`, `y₃` range-checked below
/// `2^32` and the certificates `w·(x_S − x_A) ≡ 1` (the guard, bug checklist 1),
/// `λ₁·(x_S − x_A) ≡ y_S − y_A`, `λ₁² ≡ x_R + x_A + x_S`, `(λ₁ + λ₂)·(x_A − x_R) ≡ 2y_A`,
/// `λ₂² ≡ x₃ + x_R + x_A`, `λ₂·(x_A − x₃) ≡ y₃ + y_A`, differences biased by `2p`. The
/// fourth needs no guard: at `x_A ≡ x_R` it would say `2y_A ≡ 0`, and secp256k1 has no
/// 2-torsion. Proven in `formal/Formal/EcK1Check.lean`: on `A`, `x_S` limbs `< 2^32` and
/// `y_S` limbs `< 2^33`, every satisfying assignment has `x_A ≢ x_S` and
/// `(x₃, y₃) = (A + S) + A` for affine `A`, `S`, with limbs `< 2^32`.
#[xark::gadget]
#[allow(clippy::too_many_arguments)]
pub fn ec_double_add_k1_check(
    ax: [Field; 8],
    ay: [Field; 8],
    sx: [Field; 8],
    sy: [Field; 8],
    w: [Field; 8],
    l1: [Field; 8],
    xr: [Field; 8],
    l2: [Field; 8],
    x3: [Field; 8],
    y3: [Field; 8],
) {
    let (z, one, m1) = (
        Field::from(0u8),
        Field::from(1u8),
        Field::from(0u8) - Field::from(1u8),
    );
    let b2 = b2_k1();
    let zero8 = [z; 8];
    range32(w);
    range32(l1);
    range32(xr);
    range32(l2);
    range32(x3);
    range32(y3);
    let dx = lin8(b2, sx, one, ax, m1);
    let mut unit = zero8;
    unit[0] = one;
    mul_cert_k1(w, dx, unit);
    mul_cert_k1(l1, dx, lin8(b2, sy, one, ay, m1));
    mul_cert_k1(l1, l1, lin8(xr, ax, one, sx, one));
    mul_cert_k1(
        lin8(l1, l2, one, zero8, z),
        lin8(b2, ax, one, xr, m1),
        lin8(zero8, ay, Field::from(2u8), zero8, z),
    );
    mul_cert_k1(l2, l2, lin8(x3, xr, one, ax, one));
    mul_cert_k1(l2, lin8(b2, ax, one, x3, m1), lin8(y3, ay, one, zero8, z));
}

/// On-curve check for secp256k1 (`y² = x³ + 7`), sound only on range-checked limbs: every
/// limb of `x` and `y` must already be range-checked below `2^32` by the caller, which owns
/// that check (bug checklist 6: one validating owner per coordinate; for ECDSA,
/// `xark_secp256k1`'s `unpack8`). The coordinates must be canonical (`< p`), so each point
/// has exactly one accepted encoding, as for secp256r1 and Edwards curves.
pub fn on_curve_k1(x: [Field; 8], y: [Field; 8]) {
    require_lt::<8, 32>(x, M1_K1);
    require_lt::<8, 32>(y, M1_K1);
    xark::witness_begin();
    let s = hint_mul_k1(x, x);
    let z = hint_mul_k1(y, y);
    xark::witness_end();
    on_curve_k1_check(x, y, s, z);
}

/// The rows of [`on_curve_k1`]'s curve equation: `s`, `z` range-checked below `2^32` and the
/// certificates `x·x ≡ s`, `y·y ≡ z`, `s·x ≡ z − 7` (as `2p + z − 7` limb-wise), so
/// `y² ≡ x³ + 7 (mod p)`. Proven in `formal/Formal/EcK1Check.lean`: on `x`, `y` limbs
/// `< 2^32`, every satisfying assignment has `(x, y)` on secp256k1 in `ZMod p`.
/// (Canonicity is [`require_lt`]'s, called by [`on_curve_k1`].)
#[xark::gadget]
pub fn on_curve_k1_check(x: [Field; 8], y: [Field; 8], s: [Field; 8], z: [Field; 8]) {
    range32(s);
    range32(z);
    mul_cert_k1(x, x, s);
    mul_cert_k1(y, y, z);
    let mut c = b2_k1();
    c[0] -= Field::from(7u8);
    let zero8 = [Field::from(0u8); 8];
    mul_cert_k1(s, x, lin8(c, z, Field::from(1u8), zero8, Field::from(0u8)));
}

// ===========================================================================
// secp256r1 (NIST P-256) point arithmetic over 8 × 32-bit limbs, by certificates.
// ===========================================================================

/// secp256r1's `p = 2²⁵⁶ − 2²²⁴ + 2¹⁹² + 2⁹⁶ − 1` as 8 × 32-bit limbs.
pub const M_R1: [Field; 8] =
    modulus_limbs::<8, 32>("0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF");
/// secp256r1 `p − 1` (the canonical-coordinate bound).
pub const M1_R1: [Field; 8] =
    modulus_minus_1::<8, 32>("0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF");

/// The 15 evaluation points of `mul_cert_r1`'s products.
const CERT_R1_PTS: [i64; 15] = [0, 1, -1, 2, -2, 3, -3, 4, -4, 5, -5, 6, -6, 7, -7];
/// `L` and `H` read off the 15 products: column `m` of `a·b` (`Σ_{i+j=m} aᵢbⱼ`) is
/// `Σᵢ V[m][i]·Pᵢ` (inverse Vandermonde of the points), and `CERT_R1_LO[i] =
/// Σₘ ℓₘ·V[m][i]`, `CERT_R1_HI[i] = Σₘ hₘ·V[m][i]`, where `ℓₘ + 2⁹⁶·hₘ ≡ 2³²ᵐ (mod p)`
/// is `Y^m mod (Y⁸ − Y⁷ + Y⁶ + Y³ − 1)` at `Y = 2³²` split after its third word.
/// `formal/Formal/MulCertR1.lean` checks both against `ℓₘ`, `hₘ`.
const CERT_R1_LO: [Field; 15] = [
    Field::constant("9363695963018136371772207501888011185057361295673458298760118506927698404381"),
    Field::constant("3101071155502605351026484082051190841481527969099589744492656422263611879870"),
    Field::constant(
        "21197337903973721314227396382249703249619478934780272100039472390038301301758",
    ),
    Field::constant("256225885409253718062557022574936405035467193120491463903323163317571138900"),
    Field::constant("887497334438707814991195163580610633139029299892521034645282519898879885554"),
    Field::constant("2181101555989893254135221809418113128195011863720505735598176604469702270361"),
    Field::constant("6350696313857077509226549995570063385292215994858482729831480464349624893139"),
    Field::constant("7976670793853647505480671914368216556543358684113142538090307562902073820475"),
    Field::constant(
        "19626091022576317606446736688975739543102327882427679145911888680060699327075",
    ),
    Field::constant(
        "20574505555318491748463830943421725001697670292894024191886748720111751221575",
    ),
    Field::constant(
        "19541704953953767424502724639783047701528996098911763768062403523289956055126",
    ),
    Field::constant(
        "14448463183696943128604708744492998269775383910372129714894147307889591144299",
    ),
    Field::constant("7789229095286828943191255023306409733993036010958532347169306130958930965552"),
    Field::constant(
        "21724227873626453284752979642940546878233506429044833699710731712131689712499",
    ),
    Field::constant(
        "20087424384212356803086726407436888195692543343460848236589589783996385944373",
    ),
];
const CERT_R1_HI: [Field; 15] = [
    Field::constant("1011728051526495070430399616529842720778787803040074331232270180561418765911"),
    Field::constant(
        "19744570474549393079922979966533697461147104043859476936889883051141598816419",
    ),
    Field::constant(
        "21859758389108923040443149608150997717393548751786418322234209022783658594634",
    ),
    Field::constant(
        "15666666059474643735149875544307665963918319094701319466115831002753719218030",
    ),
    Field::constant("4471381942475191821641329605165599412181420495324749025246455615776461844075"),
    Field::constant(
        "19201803314441416707144589747053876010621873214879839525321790178407079160879",
    ),
    Field::constant(
        "11124337178978912744892621940801999800533818977729610133356075549780469157123",
    ),
    Field::constant(
        "13342343217332340450723886862279789915416170463204047011136657164251232967442",
    ),
    Field::constant("2603900754342303388331934728689637114610062599098757882361910687811558547087"),
    Field::constant("4570305160136366643975041522131053535870439368061723394964113354022547770337"),
    Field::constant(
        "19901294705143205314610607660495439235543179494194327232418528267025671209772",
    ),
    Field::constant("3287327061506095839027523073285627398746012351398081048246495227756153619192"),
    Field::constant("4799062079688944208046447727706920064275310183731841173320189888946735507325"),
    Field::constant(
        "16636718668458145549991910924360642308019972821585257186965161289237518955040",
    ),
    Field::constant(
        "16884745917551824183638947434565412049330895540732752079776063012350643831670",
    ),
];

/// The 15 products `A(ωᵢ)·B(ωᵢ)` at `CERT_R1_PTS` (one row each) of two 8 × 32-bit values,
/// read through the coefficient vectors `lo` and `hi` (linear): `(Σᵢ loᵢ·Pᵢ, Σᵢ hiᵢ·Pᵢ)`.
/// Shared by [`mul_cert_r1`] and [`mul_cert_k1`].
#[inline(always)]
fn cert_products(a: [Field; 8], b: [Field; 8], lo: [Field; 15], hi: [Field; 15]) -> (Field, Field) {
    let z = Field::from(0u8);
    let (mut l, mut h) = (z, z);
    let mut i = 0usize;
    while i < 15 {
        let (mut pa, mut pb, mut c) = (z, z, 1i64);
        let mut j = 0usize;
        while j < 8 {
            let f = if c < 0 {
                z - Field::from((-c) as u64)
            } else {
                Field::from(c as u64)
            };
            pa += f * a[j];
            pb += f * b[j];
            c *= CERT_R1_PTS[i];
            j += 1;
        }
        let prod = pa * pb;
        l += lo[i] * prod;
        h += hi[i] * prod;
        i += 1;
    }
    (l, h)
}

/// `p′ = (p + 1)/2⁹⁶`, so `p = 2⁹⁶·p′ − 1`.
const CERT_R1_PP: Field = Field::constant("1461501636990620551361974531767172749817708281857");
/// Limb bound `mul_cert_r1` assumes of `a`, `b` and `t` (`< 2^CERT_R1_IN`, caller-enforced).
const CERT_R1_IN: usize = 35;
/// Width of the range-checked `K + 2⁴²` and `T + 2⁴²`.
const CERT_R1_W: usize = 43;

/// Assert `a·b ≡ t (mod p)` for secp256r1's Solinas `p`, over 8 × 32-bit limbs that may be
/// unreduced (each limb of `a`, `b`, `t` in `[0, 2^35)`, which the caller enforces). The
/// limb products come from 15 rows `A(ωᵢ)·B(ωᵢ)` at small points (interpolation, linear;
/// Winograd/Toom); folding each column `2³²ᵐ` mod `Y⁸ − Y⁷ + Y⁶ + Y³ − 1` (`= p` at
/// `Y = 2³²`, coefficients in `[−1, 3]`) splits `E ≡ a·b − t` as `L + 2⁹⁶·H`, `|L| < 2¹³⁸`,
/// `|H| < 2²⁰²`. Since `p = 2⁹⁶·p′ − 1`, `E = K·p` iff `L + K = 2⁹⁶·(K·p′ − H)`: one row,
/// with `K` and the linear form `T = K·p′ − H` range-checked in `(−2⁴², 2⁴²)`. The honest
/// `K ≡ −L (mod 2⁹⁶)` comes from one `div_rem`. `15 + 43 + 43 + 1` rows. Proven sound and
/// complete over its exported rows (`formal/Formal/MulCertR1.lean`).
#[xark::gadget]
pub fn mul_cert_r1(a: [Field; 8], b: [Field; 8], t: [Field; 8]) {
    // No-wrap budget (bug checklist 5), proven exactly in MulCertR1.lean: a column is
    // `< 8·2^(2·CERT_R1_IN)`, `Σ|ℓₘ| < 2^67` and `Σ|hₘ| < 2^133`, so `|L|`, `|K|`,
    // `2^96·|T|` and `|K·p′|`, `|H|` stay far below `r/2`; the honest `K`, `T` lie in
    // `(−2^42, 2^42)` (MulCertR1.int_complete).
    const {
        assert!(2 * CERT_R1_IN + 3 + 67 < 252 && 96 + CERT_R1_W < 252);
        assert!(2 * CERT_R1_IN + 3 + 133 < 252 && CERT_R1_W + 160 < 252);
    };
    let (mut lo, mut hi) = cert_products(a, b, CERT_R1_LO, CERT_R1_HI);
    let two32 = Field::from(1u64 << 32);
    lo = lo - t[0] - two32 * t[1] - two32 * two32 * t[2];
    let mut w = Field::from(1u8);
    let mut k = 3usize;
    while k < 8 {
        hi -= w * t[k];
        w *= two32;
        k += 1;
    }
    // `K + 2⁴² ≡ 2¹⁴⁰ + 2⁴² − L (mod 2⁹⁶)`; the `div_rem` quotient is scratch.
    let n = two_pow_big(140) + two_pow_big(42) - lo;
    xark::witness_begin();
    let q = Field::hint_div_rem(n, two_pow_big(96))[0];
    xark::witness_end();
    let kb = n - two_pow_big(96) * q;
    let kk = kb - two_pow_big(42);
    let tt = kk * CERT_R1_PP - hi;
    let _ = kb.to_bits::<CERT_R1_W>();
    let _ = (tt + two_pow_big(42)).to_bits::<CERT_R1_W>();
    require_eq(lo + kk, two_pow_big(96) * tt);
}

fn hint_mul_r1(a: [Field; 8], b: [Field; 8]) -> [Field; 8] {
    Field::hint_mulmod_divmod::<8>(a, b, M_R1, 32).1
}
fn hint_sub2_r1(a: [Field; 8], b: [Field; 8], c: [Field; 8]) -> [Field; 8] {
    Field::hint_sub2::<8>(a, b, c, M_R1, 32).1
}
/// Range-check each limb below `2^32` (`to_bits::<32>`, `formal/Formal/ToBits32.lean`).
fn range32(v: [Field; 8]) {
    let mut i = 0usize;
    while i < 8 {
        let _ = v[i].to_bits::<32>();
        i += 1;
    }
}
/// `2p` limb-wise, each limb in `[2³³ − 5, 2³⁴)`: a bias keeping `2p + u − v` limbs in
/// `[0, 2^35)` for `u` limbs `< 2^34` and `v` limbs `< 2^32`. A caller may pass `2p − y`
/// for `−y`.
pub fn b2_r1() -> [Field; 8] {
    let l = [
        12884901886u64,
        12884901885,
        12884901885,
        12884901887,
        12884901885,
        12884901885,
        12884901887,
        8589934587,
    ];
    let mut out = [Field::from(0u8); 8];
    let mut i = 0usize;
    while i < 8 {
        out[i] = Field::from(l[i]);
        i += 1;
    }
    out
}
/// `c + su·u + sv·v` limb-wise (linear).
fn lin8(c: [Field; 8], u: [Field; 8], su: Field, v: [Field; 8], sv: Field) -> [Field; 8] {
    let mut out = [Field::from(0u8); 8];
    let mut i = 0usize;
    while i < 8 {
        out[i] = c[i] + su * u[i] + sv * v[i];
        i += 1;
    }
    out
}

/// Incomplete affine addition on secp256r1: the honest `w = (x_Q − x_P)⁻¹`, `λ`, `x₃`, `y₃`
/// as hints in a witness region, pinned by [`ec_add_r1_check`]. Inputs: `P`'s and `x_Q`'s
/// limbs `< 2^32`, `y_Q`'s `< 2^34` (so a caller can pass `2p − y` for `−Q`); outputs:
/// limbs `< 2^32`, canonical for an honest prover.
pub fn ec_add_r1(
    px: [Field; 8],
    py: [Field; 8],
    qx: [Field; 8],
    qy: [Field; 8],
) -> ([Field; 8], [Field; 8]) {
    let (one, m1) = (Field::from(1u8), Field::from(0u8) - Field::from(1u8));
    let b2 = b2_r1();
    let zero8 = [Field::from(0u8); 8];
    xark::witness_begin();
    let w = Field::hint_mod_inverse::<8>(lin8(b2, qx, one, px, m1), M_R1, 32);
    let lam = hint_mul_r1(lin8(b2, qy, one, py, m1), w);
    let x3 = hint_sub2_r1(hint_mul_r1(lam, lam), px, qx);
    let y3 = hint_sub2_r1(hint_mul_r1(lam, hint_sub2_r1(px, x3, zero8)), py, zero8);
    xark::witness_end();
    ec_add_r1_check(px, py, qx, qy, w, lam, x3, y3);
    (x3, y3)
}

/// The rows of [`ec_add_r1`]: `w`, `λ`, `x₃`, `y₃` range-checked below `2^32` and the
/// certificates `w·Δx ≡ 1` (the chord guard, bug checklist 1), `λ·Δx ≡ Δy`,
/// `λ² ≡ x₃ + x_P + x_Q`, `λ·(2p + x_P − x₃) ≡ y₃ + y_P`, with `Δ = 2p + Q − P`
/// limb-wise. Proven in `formal/Formal/EcR1Check.lean`: on `P`, `x_Q` limbs `< 2^32` and
/// `y_Q` limbs `< 2^34`, every satisfying assignment has `x_P ≢ x_Q` and `(x₃, y₃) = P + Q`
/// for affine `P`, `Q`, with limbs `< 2^32`.
#[xark::gadget]
#[allow(clippy::too_many_arguments)]
pub fn ec_add_r1_check(
    px: [Field; 8],
    py: [Field; 8],
    qx: [Field; 8],
    qy: [Field; 8],
    w: [Field; 8],
    lam: [Field; 8],
    x3: [Field; 8],
    y3: [Field; 8],
) {
    let (z, one, m1) = (
        Field::from(0u8),
        Field::from(1u8),
        Field::from(0u8) - Field::from(1u8),
    );
    let b2 = b2_r1();
    let zero8 = [z; 8];
    range32(w);
    range32(lam);
    range32(x3);
    range32(y3);
    let dx = lin8(b2, qx, one, px, m1);
    let mut unit = zero8;
    unit[0] = one;
    mul_cert_r1(w, dx, unit);
    mul_cert_r1(lam, dx, lin8(b2, qy, one, py, m1));
    mul_cert_r1(lam, lam, lin8(x3, px, one, qx, one));
    mul_cert_r1(lam, lin8(b2, px, one, x3, m1), lin8(y3, py, one, zero8, z));
}

/// The fused incomplete step `(A + S) + A` on secp256r1, without `A + S`'s `y`
/// (Eisenträger–Lauter–Montgomery, arXiv math/0208038; gnark `doubleAndAdd`): `w`, `λ₁`,
/// `x_R`, `λ₂` and the result as hints in a witness region, pinned by
/// [`ec_double_add_r1_check`]. `A`'s and `x_S`'s limbs are below `2^32`; `y_S`'s may be up
/// to `2^34`, so a caller can pass `2p − y` for `−S`.
pub fn ec_double_add_r1(
    ax: [Field; 8],
    ay: [Field; 8],
    sx: [Field; 8],
    sy: [Field; 8],
) -> ([Field; 8], [Field; 8]) {
    let (z, one, m1) = (
        Field::from(0u8),
        Field::from(1u8),
        Field::from(0u8) - Field::from(1u8),
    );
    let b2 = b2_r1();
    let zero8 = [z; 8];
    xark::witness_begin();
    let w = Field::hint_mod_inverse::<8>(lin8(b2, sx, one, ax, m1), M_R1, 32);
    let l1 = hint_mul_r1(lin8(b2, sy, one, ay, m1), w);
    let xr = hint_sub2_r1(hint_mul_r1(l1, l1), ax, sx);
    let ar = hint_sub2_r1(ax, xr, zero8);
    let two_ay = lin8(zero8, ay, Field::from(2u8), zero8, z);
    let l2 = hint_sub2_r1(
        hint_mul_r1(two_ay, Field::hint_mod_inverse::<8>(ar, M_R1, 32)),
        l1,
        zero8,
    );
    let x3 = hint_sub2_r1(hint_mul_r1(l2, l2), xr, ax);
    let y3 = hint_sub2_r1(hint_mul_r1(l2, hint_sub2_r1(ax, x3, zero8)), ay, zero8);
    xark::witness_end();
    ec_double_add_r1_check(ax, ay, sx, sy, w, l1, xr, l2, x3, y3);
    (x3, y3)
}

/// The rows of [`ec_double_add_r1`]: `w`, `λ₁`, `x_R`, `λ₂`, `x₃`, `y₃` range-checked below
/// `2^32` and the certificates `w·(x_S − x_A) ≡ 1` (the guard, bug checklist 1),
/// `λ₁·(x_S − x_A) ≡ y_S − y_A`, `λ₁² ≡ x_R + x_A + x_S`, `(λ₁ + λ₂)·(x_A − x_R) ≡ 2y_A`,
/// `λ₂² ≡ x₃ + x_R + x_A`, `λ₂·(x_A − x₃) ≡ y₃ + y_A`, differences biased by `2p`. The
/// fourth needs no guard: at `x_A ≡ x_R` it would say `2y_A ≡ 0`, and P-256 has no
/// 2-torsion. Proven in `formal/Formal/EcR1Check.lean`: on `A`, `x_S` limbs `< 2^32` and
/// `y_S` limbs `< 2^34`, every satisfying assignment has `x_A ≢ x_S` and
/// `(x₃, y₃) = (A + S) + A` for affine `A`, `S`, with limbs `< 2^32`.
#[xark::gadget]
#[allow(clippy::too_many_arguments)]
pub fn ec_double_add_r1_check(
    ax: [Field; 8],
    ay: [Field; 8],
    sx: [Field; 8],
    sy: [Field; 8],
    w: [Field; 8],
    l1: [Field; 8],
    xr: [Field; 8],
    l2: [Field; 8],
    x3: [Field; 8],
    y3: [Field; 8],
) {
    let (z, one, m1) = (
        Field::from(0u8),
        Field::from(1u8),
        Field::from(0u8) - Field::from(1u8),
    );
    let b2 = b2_r1();
    let zero8 = [z; 8];
    range32(w);
    range32(l1);
    range32(xr);
    range32(l2);
    range32(x3);
    range32(y3);
    let dx = lin8(b2, sx, one, ax, m1);
    let mut unit = zero8;
    unit[0] = one;
    mul_cert_r1(w, dx, unit);
    mul_cert_r1(l1, dx, lin8(b2, sy, one, ay, m1));
    mul_cert_r1(l1, l1, lin8(xr, ax, one, sx, one));
    mul_cert_r1(
        lin8(l1, l2, one, zero8, z),
        lin8(b2, ax, one, xr, m1),
        lin8(zero8, ay, Field::from(2u8), zero8, z),
    );
    mul_cert_r1(l2, l2, lin8(x3, xr, one, ax, one));
    mul_cert_r1(l2, lin8(b2, ax, one, x3, m1), lin8(y3, ay, one, zero8, z));
}

/// On-curve check for secp256r1 (`y² = x³ − 3x + b`), sound only on range-checked limbs:
/// every limb of `x` and `y` must already be range-checked below `2^32` by the caller,
/// which owns that check (bug checklist 6). The coordinates must be canonical (`< p`), so
/// each point has exactly one accepted encoding.
pub fn on_curve_r1(x: [Field; 8], y: [Field; 8]) {
    require_lt::<8, 32>(x, M1_R1);
    require_lt::<8, 32>(y, M1_R1);
    xark::witness_begin();
    let s = hint_mul_r1(x, x);
    let z = hint_mul_r1(y, y);
    xark::witness_end();
    on_curve_r1_check(x, y, s, z);
}

/// `2p − b` limb-wise (each limb in `[2³², 2³³)`), for the curve equation's `−b`.
const B2_MINUS_B_R1: [u64; 8] = [
    7921835955, 7586563008, 5161897736, 6893533520, 6600227138, 5571363497, 5733968921, 7066995236,
];

/// The rows of [`on_curve_r1`]'s curve equation: `s`, `z` range-checked below `2^32` and the
/// certificates `x·x ≡ s`, `y·y ≡ z`, `s·x ≡ z + 3x − b` (as `z + 3x + (2p − b)`
/// limb-wise), so `y² ≡ x³ − 3x + b (mod p)`. Proven in `formal/Formal/EcR1Check.lean`: on
/// `x`, `y` limbs `< 2^32`, every satisfying assignment has `(x, y)` on secp256r1 in
/// `ZMod p`. (Canonicity is [`require_lt`]'s, called by [`on_curve_r1`].)
#[xark::gadget]
pub fn on_curve_r1_check(x: [Field; 8], y: [Field; 8], s: [Field; 8], z: [Field; 8]) {
    range32(s);
    range32(z);
    mul_cert_r1(x, x, s);
    mul_cert_r1(y, y, z);
    let mut c = [Field::from(0u8); 8];
    let mut i = 0usize;
    while i < 8 {
        c[i] = Field::from(B2_MINUS_B_R1[i]);
        i += 1;
    }
    mul_cert_r1(s, x, lin8(c, z, Field::from(1u8), x, Field::from(3u8)));
}

/// Non-native modular multiplication `(a·b) mod m` over `LIMBS` × `BITS`-bit limbs.
///
/// SOUNDNESS BUDGET: the schoolbook column products `Σ a_i·b_j` (and `Σ q_i·m_j`)
/// plus biased carries must not wrap BN254 `Fr` (~2^254). A single product is
/// `< 2^(2·BITS)`; summed across a column with carry/bias headroom, `2·BITS + slack`
/// bits must stay below the field. The `const` assertion below fails to compile for
/// any unsound `(LIMBS, BITS)`. For `<3, 86>`: `172 + 8 = 180 < 253`.
///
/// `a`, `b` and `m` must have limbs `< 2^BITS` (see the crate docs), and `m ≥ 1`.
pub fn mod_mul<const LIMBS: usize, const BITS: usize>(
    a: [Field; LIMBS],
    b: [Field; LIMBS],
    m: [Field; LIMBS],
) -> [Field; LIMBS] {
    mul_divmod::<LIMBS, BITS>(a, b, m).1
}

/// [`mod_mul`] with `m − 1` given: for a constant modulus, whose `m − 1` is a
/// constant too (what [`fp!`] uses). `m_minus_1` must be exactly `m − 1`: it bounds
/// the remainder, and a larger one admits `r + m` as well as `r`.
#[doc(hidden)]
pub fn mod_mul_bounded<const LIMBS: usize, const BITS: usize>(
    a: [Field; LIMBS],
    b: [Field; LIMBS],
    m: [Field; LIMBS],
    m_minus_1: [Field; LIMBS],
) -> [Field; LIMBS] {
    mul_divmod_bounded::<LIMBS, BITS>(a, b, m, m_minus_1).1
}

/// `m − 1`, limb by limb with its borrow: the bound [`require_lt`] takes for
/// `x < m`, computed from `m` by constrained rows, never taken from the prover.
/// `m`'s limbs must be `< 2^BITS`, and `m ≥ 1` is required; the result's limbs are
/// then `< 2^BITS` too.
pub fn minus_one<const LIMBS: usize, const BITS: usize>(m: [Field; LIMBS]) -> [Field; LIMBS] {
    let zero = Field::from(0u8);
    let mut out = m;
    // Subtract 1 at limb 0; a limb borrows from the next exactly when it's 0 and a
    // borrow reaches it.
    let mut borrow = Field::from(1u8);
    let mut i = 0usize;
    while i < LIMBS {
        let next = borrow * Field::from(m[i] == zero);
        out[i] = m[i] - borrow + next * two_pow::<BITS>();
        borrow = next;
        i += 1;
    }
    // A borrow out of the top limb: `m` was 0.
    require_eq(borrow, zero);
    out
}

/// Non-native `a·b` exposing **both** halves of the division: returns
/// `(q, r)` with `q = ⌊a·b / m⌋` and `r = a·b mod m`. Both are range-checked to
/// `LIMBS × BITS` bits, `r` is `require_lt`'d canonical, and the pair is pinned by
/// `mulmod_columns` (`a·b == q·m + r`), so the quotient is as sound as the
/// remainder. [`mod_mul`] is `.1` of this.
///
/// The quotient is what lets a scaled-division advice (e.g. a GLV lattice
/// reduction's `⌊b·u / n⌋`) be *derived in-circuit* from its inputs rather than
/// supplied as a witness input.
///
/// `a`, `b` and `m` must have limbs `< 2^BITS` (see the crate docs), and `m ≥ 1`.
pub fn mul_divmod<const LIMBS: usize, const BITS: usize>(
    a: [Field; LIMBS],
    b: [Field; LIMBS],
    m: [Field; LIMBS],
) -> ([Field; LIMBS], [Field; LIMBS]) {
    mul_divmod_bounded::<LIMBS, BITS>(a, b, m, minus_one::<LIMBS, BITS>(m))
}

/// [`mul_divmod`] with `m − 1` given, as [`mod_mul_bounded`].
#[doc(hidden)]
pub fn mul_divmod_bounded<const LIMBS: usize, const BITS: usize>(
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
    require_lt::<LIMBS, BITS>(r, m_minus_1);
    mulmod_columns::<LIMBS, BITS>(a, b, q, r, m);
    (q, r)
}

/// Non-native modular inverse `a⁻¹ mod m` over `LIMBS` × `BITS`-bit limbs. Output
/// is `≡ a⁻¹` but not forced canonical: fine as a [`mod_mul`] operand, whose result
/// is canonical; anything that compares it, tests it for zero or exposes its limbs
/// needs it canonical first (`assert_canonical`, or a multiply by one).
///
/// Specialized: the reduction remainder is *known* to be exactly `1`, so `r` is
/// pinned to the constant `[1,0,…]` instead of being range-checked and
/// canonical-checked as advice — saving the per-inverse range/`require_lt` work.
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
    // check / require_lt needed — 1 is trivially a canonical limb).
    let mut r = [Field::from(0u8); LIMBS];
    r[0] = Field::from(1u8);
    let mut i = 0usize;
    while i < LIMBS {
        require_eq(r_hint[i], r[i]);
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
/// SOUNDNESS: `r` is range-checked + `require_lt`'d (canonical, unique). `qabs` is
/// pinned to `{0,1,2}` (2 bits with the `(1,1)` pattern excluded), so each
/// `lhs[i] = a[i] + qabs·m[i] < 3·2^BITS` and the signed carry stays `|t| ≤ 3`
/// (`cb = t+4 ∈ [1,7]`, range-checked `< 8`).
///
/// `a`, `b`, `c` and `m` must have limbs `< 2^BITS` (see the crate docs).
pub fn sub2<const LIMBS: usize, const BITS: usize>(
    a: [Field; LIMBS],
    b: [Field; LIMBS],
    c: [Field; LIMBS],
    m: [Field; LIMBS],
) -> [Field; LIMBS] {
    sub2_bounded::<LIMBS, BITS>(a, b, c, m, minus_one::<LIMBS, BITS>(m))
}

/// [`sub2`] with `m − 1` given, as [`mod_mul_bounded`].
#[doc(hidden)]
pub fn sub2_bounded<const LIMBS: usize, const BITS: usize>(
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
    require_lt::<LIMBS, BITS>(r, m_minus_1);

    // qabs ∈ {0,1,2}: two bits, exclude the (1,1)=3 pattern.
    let q0 = Field::hint_bit(qabs, 0);
    let q1 = Field::hint_bit(qabs, 1);
    q0.require_bool();
    q1.require_bool();
    require_eq(q0 + q1 + q1, qabs);
    require_eq(q0 * q1, Field::from(0u8));

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
        require_eq(num, two_b * cb + rem);
        require_eq(rem, Field::from(0u8));
        range_lt_8(cb);
        cb_prev = cb;
        i += 1;
    }
    let lhs2 = a[LIMBS - 1] + qabs * m[LIMBS - 1];
    let rhs2 = b[LIMBS - 1] + c[LIMBS - 1] + r[LIMBS - 1];
    let num2 = lhs2 - rhs2 + cb_prev + bias_shift - bias;
    require_eq(num2, bias_shift);

    r
}

// 3-limb-specific helpers (256-bit scalar layout / affine-point muxes). Not
// width-generalized (tied to the 86+86+84 bit split and affine point shape).

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
#[xark::gadget]
pub fn scalar_to_bits(u: [Field; 3]) -> [Field; 256] {
    let mut bits = [Field::from(0u8); 256];
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 86usize {
        let b = Field::hint_bit(u[0], i);
        b.require_bool();
        bits[i] = b;
        acc = acc + b * pow;
        pow = pow + pow;
        i += 1;
    }
    require_eq(acc, u[0]);
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 86usize {
        let b = Field::hint_bit(u[1], i);
        b.require_bool();
        bits[86 + i] = b;
        acc = acc + b * pow;
        pow = pow + pow;
        i += 1;
    }
    require_eq(acc, u[1]);
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 84usize {
        let b = Field::hint_bit(u[2], i);
        b.require_bool();
        bits[172 + i] = b;
        acc = acc + b * pow;
        pow = pow + pow;
        i += 1;
    }
    require_eq(acc, u[2]);
    bits
}

/// Boolean-gated select between two affine points (`[[Field;3];2]`, 3-limb).
pub fn point_select_affine(
    bit: Field,
    if_true: [[Field; 3]; 2],
    if_false: [[Field; 3]; 2],
) -> [[Field; 3]; 2] {
    bit.require_bool();
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
/// The one-hot vector of the byte `b₀ + 2b₁ + … + 2⁷b₇` over boolean `bits`: `out[v] = 1`
/// at `v = Σ 2ⁱbᵢ` and `0` elsewhere, built a bit at a time (`out[v + 2ⁱ] = old[v]·bᵢ`,
/// `out[v] = old[v] − out[v + 2ⁱ]`): 254 rows. Proven in `formal/Formal/OneHot8.lean`
/// on boolean bits (its callers': `xark_secp256k1::fake_glv_check_k1`'s `to_bits` rows).
#[xark::gadget]
pub fn one_hot8(bits: [Field; 8]) -> [Field; 256] {
    let mut out = [Field::from(0u8); 256];
    out[0] = Field::from(1u8);
    let mut i = 0usize;
    while i < 8 {
        let mut v = 0usize;
        while v < 1usize << i {
            let hi = out[v] * bits[i];
            out[v + (1usize << i)] = hi;
            out[v] -= hi;
            v += 1;
        }
        i += 1;
    }
    out
}

/// The gadget's public API plus the xark circuit essentials, so a circuit crate
/// needs a single `use xark_bignum::prelude::*;`. `Field` comes via `crate::*`, so
/// the `xark` essentials are listed explicitly to avoid a duplicate-`Field` glob.
pub mod prelude {
    pub use crate::*;
    pub use xark::prelude::{
        Private, Public, circuit, require, require_eq, require_ge, require_gt, require_le,
        require_lt, witness_begin, witness_end,
    };
}
