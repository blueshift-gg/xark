//! Everyday input types with a natural form on both sides: a short [`Text`], one
//! variant of an [`Enum`] ([`Choice`]) and a set of them ([`Bitfield`]). Each is one
//! `Field` in the circuit and its plain value off it (`"A1938274"`, `Country::US`),
//! with its standard type recorded in `schema.json`. Times are in [`crate::time`].

use core::marker::PhantomData;

use crate::input::{Encoding, Enum, Input, Layout, Reader, Type, Writer};
use crate::lang::{Field, require, require_eq};

// ---- Text ---------------------------------------------------------------------

/// Up to 31 bytes of UTF-8 (a document number, a ticker), packed little-endian into
/// one `Field`: `Text::new("A1938274")`. Compared and hashed as that field.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Text(Field);

impl Text {
    /// The string's bytes, little-endian, or `None` past 31 bytes.
    pub const fn checked(s: &str) -> Option<Text> {
        if s.len() > 31 {
            return None;
        }
        Some(Text(Field::from_le_bytes(s.as_bytes())))
    }

    /// The string's bytes, little-endian. Panics past 31 bytes.
    pub const fn new(s: &str) -> Text {
        assert!(
            s.len() <= 31,
            "text longer than 31 bytes doesn't fit a field"
        );
        Text(Field::from_le_bytes(s.as_bytes()))
    }

    /// The text's `Field`.
    pub const fn field(self) -> Field {
        self.0
    }
}

// ---- Choice and Bitfield ----------------------------------------------------------

/// One variant of an [`Enum`] in one `Field` (its position): a status, a document
/// kind. Off-circuit it's built from the variant (`Kind::Passport.into()`); a
/// generated client takes its name (`"Passport"`).
///
/// In the circuit, [`Choice::is`] compares it with a variant. A value outside the
/// enum equals none of them; [`Choice::require_valid`] rules it out.
pub struct Choice<E: Enum>(Field, PhantomData<E>);

impl<E: Enum> Clone for Choice<E> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<E: Enum> Copy for Choice<E> {}

impl<E: Enum> Choice<E> {
    /// The choice of `variant`.
    pub fn of(variant: E) -> Self {
        Choice(Field::from_u64(variant.index() as u64), PhantomData)
    }

    /// Whether this is `variant`: a `{0, 1}` circuit wire.
    pub fn is(self, variant: E) -> bool {
        self.0 == Field::from_u64(variant.index() as u64)
    }

    /// Constrain this to be `variant`.
    pub fn require_is(self, variant: E) {
        require_eq(self.0, Field::from_u64(variant.index() as u64));
    }

    /// Constrain this to be one of the enum's variants (`< 2⁶⁴` and below the
    /// variant count: about 70 constraints).
    pub fn require_valid(self) {
        require(
            self.0
                .lt::<64>(Field::from_u64(E::VARIANTS.names.len() as u64)),
        );
    }

    /// Constrain this to be in `allowed` (so a valid variant too).
    ///
    /// `∏ᵢ (self − i + (1 − allowedᵢ)·2ʷ) = 0` with `self < 2ʷ` checked, `2ʷ` the
    /// least power of two at or above the variant count: a factor vanishes only where
    /// `self` is variant `i` and `i` is allowed, since a disallowed one's lies in
    /// `(2ʷ − n, 2ʷ⁺¹)`. About `2n + w` constraints for `n` variants (510 over
    /// [`Country`](crate::Country), 10 for three).
    pub fn require_in(self, allowed: Bitfield<E>) {
        let n = E::VARIANTS.names.len();
        let a = allowed.bits();
        let w = if n <= 1 {
            0
        } else {
            (usize::BITS - (n - 1).leading_zeros()) as usize
        };
        let _ = self.0.to_bits_n(w);
        let k = Field::from_u64(1 << w);
        let mut product = Field::from_u8(1);
        let mut i = 0;
        while i < n {
            product *= self.0 - Field::from_u64(i as u64) + (Field::from_u8(1) - a[i]) * k;
            i += 1;
        }
        require_eq(product, Field::from_u8(0));
    }

    /// The choice's `Field` (the variant's position).
    pub const fn field(self) -> Field {
        self.0
    }
}

/// Constant sets (an allow-list fixed in the circuit, or a value on the host).
impl<E: Enum> Bitfield<E> {
    /// No variants set.
    pub fn empty() -> Self {
        Bitfield(Field::from_u8(0), PhantomData)
    }
    /// Every variant set (an allow-list that allows everything).
    pub fn all() -> Self {
        Self::from_bits(0..E::VARIANTS.names.len())
    }
    /// These variants set.
    pub fn of(variants: impl IntoIterator<Item = E>) -> Self {
        Self::from_bits(variants.into_iter().map(E::index))
    }
    fn from_bits(bits: impl Iterator<Item = usize>) -> Self {
        let mut b = [0u8; 32];
        for i in bits {
            b[i / 8] |= 1 << (i % 8);
        }
        Bitfield(Field::from_le_bytes(&b), PhantomData)
    }
}

impl<E: Enum> From<E> for Bitfield<E> {
    fn from(variant: E) -> Self {
        Self::of([variant])
    }
}

impl<E: Enum, const N: usize> From<[E; N]> for Bitfield<E> {
    fn from(variants: [E; N]) -> Self {
        Self::of(variants)
    }
}

impl<E: Enum> From<E> for Choice<E> {
    fn from(variant: E) -> Self {
        Self::of(variant)
    }
}

/// A set of an [`Enum`]'s variants in one `Field` (bit `i` = variant `i`): a holder's
/// nationality, a verifier's allow-list. Off-circuit it's built from variants
/// (`Bitfield::of([US, GB])`, `Country::US.into()`); a generated client takes `"US"`
/// or `["US", "GB"]`.
///
/// In the circuit, each check decomposes the value into its bits (253 constraints) and
/// proves no bit outside the enum is set, so a value can't name a variant that isn't
/// declared.
pub struct Bitfield<E: Enum>(Field, PhantomData<E>);

impl<E: Enum> Clone for Bitfield<E> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<E: Enum> Copy for Bitfield<E> {}

impl<E: Enum> Bitfield<E> {
    const FITS: () = assert!(
        E::VARIANTS.names.len() <= 253,
        "a Bitfield holds at most 253 variants"
    );

    /// The value's bits, one per variant: decomposing it into exactly that many
    /// proves no bit past the declared variants is set (one constraint per variant,
    /// plus one).
    fn bits(self) -> [Field; 253] {
        let () = Self::FITS;
        self.0.to_bits_n(E::VARIANTS.names.len())
    }

    /// Constrain exactly one variant to be set (a one-hot value: one nationality).
    pub fn require_single(self) {
        let bits = self.bits();
        let mut n = Field::from_u8(0);
        let mut i = 0;
        while i < E::VARIANTS.names.len() {
            n += bits[i];
            i += 1;
        }
        require_eq(n, Field::from_u8(1));
    }

    /// Constrain exactly one variant to be set, and that one to be in `allowed` (a
    /// holder's one nationality against an allow-list: 2 × 253 constraints, plus one
    /// per variant).
    pub fn require_one_of(self, allowed: Bitfield<E>) {
        let (c, a) = (self.bits(), allowed.bits());
        let (mut hot, mut hit) = (Field::from_u8(0), Field::from_u8(0));
        let mut i = 0;
        while i < E::VARIANTS.names.len() {
            hot += c[i];
            hit += c[i] * a[i];
            i += 1;
        }
        require_eq(hot, Field::from_u8(1)); // exactly one variant
        require_eq(hit, Field::from_u8(1)); // and it is allowed
    }

    /// Constrain every variant set in `self` to be set in `other` too.
    pub fn require_subset_of(self, other: Bitfield<E>) {
        let (a, b) = (self.bits(), other.bits());
        let mut i = 0;
        while i < E::VARIANTS.names.len() {
            require_eq(a[i] * b[i], a[i]); // a ⇒ b
            i += 1;
        }
    }

    /// Whether `variant` is set: a `{0, 1}` circuit wire.
    pub fn contains(self, variant: E) -> bool {
        !self.bits()[variant.index()].is_zero()
    }

    /// Constrain `variant` to be set.
    pub fn require_contains(self, variant: E) {
        require(self.contains(variant));
    }

    /// The set's `Field`.
    pub const fn field(self) -> Field {
        self.0
    }
}

// ---- inputs ---------------------------------------------------------------------

impl Input for Text {
    const TYPE: Type =
        Type::Named(&Type::named("Text", Layout::Newtype(Type::Field)).encoded(Encoding::Text(31)));
    fn read(r: &mut Reader<'_>) -> Self {
        Text(r.field())
    }
    fn write(&self, w: &mut Writer<'_>) {
        w.field(self.0)
    }
}

impl<E: Enum> Input for Choice<E> {
    const TYPE: Type = Type::Named(
        &Type::named("Choice", Layout::Newtype(Type::Field))
            .with_arg(E::VARIANTS.name)
            .encoded(Encoding::Choice(&E::VARIANTS)),
    );
    fn read(r: &mut Reader<'_>) -> Self {
        Choice(r.field(), PhantomData)
    }
    fn write(&self, w: &mut Writer<'_>) {
        w.field(self.0)
    }
}

impl<E: Enum> Input for Bitfield<E> {
    const TYPE: Type = Type::Named(
        &Type::named("Bitfield", Layout::Newtype(Type::Field))
            .with_arg(E::VARIANTS.name)
            .encoded(Encoding::Set(&E::VARIANTS)),
    );
    fn read(r: &mut Reader<'_>) -> Self {
        Bitfield(r.field(), PhantomData)
    }
    fn write(&self, w: &mut Writer<'_>) {
        w.field(self.0)
    }
}

// ---- equality -------------------------------------------------------------------

// Each is one field, so `==` and `require_eq` compare that field: one equality
// constraint (`==` gives a `{0, 1}` wire, as on `Field`).
macro_rules! one_field_eq {
    ($($t:ident $(<$g:ident: $b:ident>)?),*) => {$(
        impl$(<$g: $b>)? crate::RequireEqCircuit<$t$(<$g>)?> for $t$(<$g>)? {
            #[inline]
            #[cfg_attr(not(xark), track_caller)]
            fn require_eq_circuit(self, rhs: Self) {
                crate::lang::__xark_require_eq_scalar(self.0, rhs.0)
            }
        }
    )*};
}
one_field_eq!(Text, Choice<E: Enum>, Bitfield<E: Enum>);

macro_rules! one_field_partial_eq {
    ($($t:ident $(<$g:ident: $b:ident>)?),*) => {$(
        impl$(<$g: $b>)? PartialEq for $t$(<$g>)? {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }
    )*};
}
one_field_partial_eq!(Text, Choice<E: Enum>, Bitfield<E: Enum>);

/// `choice == Country::US`: whether it is that variant (see [`Choice::is`]).
impl<E: Enum> PartialEq<E> for Choice<E> {
    fn eq(&self, variant: &E) -> bool {
        self.is(*variant)
    }
}

// In the circuit build `Debug` only has to exist (a derived `Debug` on a struct of
// these compiles there too); the host's renders the value.
#[cfg(xark)]
mod circuit_debug {
    use core::fmt;

    use super::*;

    impl fmt::Debug for Text {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "Text({:?})", self.0)
        }
    }
    impl<E: Enum> fmt::Debug for Choice<E> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "Choice({:?})", self.0)
        }
    }
    impl<E: Enum> fmt::Debug for Bitfield<E> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "Bitfield({:?})", self.0)
        }
    }
}

#[cfg(not(xark))]
pub use host::InvalidValue;

#[cfg(not(xark))]
mod host {
    use alloc::string::String;
    use core::fmt;

    use super::*;

    /// A value that isn't one of its type: a malformed date, text too long.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct InvalidValue(pub(crate) String);

    impl fmt::Display for InvalidValue {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str(&self.0)
        }
    }

    impl core::error::Error for InvalidValue {}

    impl Text {
        /// The string, checked to fit (at most 31 UTF-8 bytes).
        pub fn parse(s: &str) -> Result<Text, InvalidValue> {
            Text::checked(s)
                .ok_or_else(|| InvalidValue(alloc::format!("{s:?} is longer than 31 bytes")))
        }
    }

    /// The string, as [`Text::parse`]. Panics past 31 bytes.
    impl From<&str> for Text {
        fn from(s: &str) -> Text {
            Text::new(s)
        }
    }

    impl From<String> for Text {
        fn from(s: String) -> Text {
            Text::new(&s)
        }
    }

    impl fmt::Debug for Text {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let b = le_bytes(self.0);
            let n = b.iter().rposition(|&x| x != 0).map_or(0, |i| i + 1);
            write!(f, "Text({:?})", String::from_utf8_lossy(&b[..n]))
        }
    }

    /// A constant `Field`'s 32 little-endian bytes.
    fn le_bytes(f: Field) -> [u8; 32] {
        use ark_ff::{BigInteger, PrimeField};
        let fr: ark_bn254::Fr = f.into();
        let mut b = [0u8; 32];
        b.copy_from_slice(&fr.into_bigint().to_bytes_le());
        b
    }

    impl<E: Enum> Choice<E> {
        /// The variant chosen (`None` for a value outside the enum).
        pub fn variant(self) -> Option<E> {
            let l = self.0.to_limbs();
            if l[1..].iter().any(|&x| x != 0) {
                return None;
            }
            E::from_index(usize::try_from(l[0]).ok()?)
        }
    }

    impl<E: Enum + fmt::Debug> fmt::Debug for Choice<E> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self.variant() {
                Some(v) => write!(f, "Choice({v:?})"),
                None => write!(f, "Choice({:?})", self.0),
            }
        }
    }

    impl<E: Enum> Bitfield<E> {
        /// The variants set, in order.
        pub fn variants(self) -> alloc::vec::Vec<E> {
            let b = le_bytes(self.0);
            (0..E::VARIANTS.names.len())
                .filter(|&i| b[i / 8] >> (i % 8) & 1 == 1)
                .filter_map(E::from_index)
                .collect()
        }
        /// The names of the variants set, in order.
        pub fn names(self) -> alloc::vec::Vec<&'static str> {
            self.variants().into_iter().map(E::name).collect()
        }
    }

    impl<E: Enum> fmt::Debug for Bitfield<E> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "Bitfield{:?}", self.names())
        }
    }
}

#[cfg(all(test, not(xark)))]
mod tests {
    use super::*;

    #[crate::input]
    enum Color {
        Red,
        Green,
        Blue,
    }

    #[test]
    fn parsing_returns_errors() {
        assert!(Text::parse(&"x".repeat(32)).is_err() && Text::parse("A1").is_ok());
    }

    #[test]
    fn text_choices_and_sets() {
        assert_eq!(
            alloc::format!("{:?}", Text::from("A1938274")),
            "Text(\"A1938274\")"
        );
        let s = Bitfield::of([Color::Red, Color::Blue]);
        assert_eq!(s.field().to_decimal(), "5");
        assert_eq!(s.names(), ["Red", "Blue"]);
        assert_eq!(Bitfield::from(Color::Green).field().to_decimal(), "2");
        assert_eq!(Bitfield::<Color>::all().names().len(), 3);
        let c = Choice::from(Color::Blue);
        assert_eq!(c.field().to_decimal(), "2");
        assert_eq!(alloc::format!("{c:?}"), "Choice(Blue)");
        assert!(c.is(Color::Blue) && !c.is(Color::Red));
        assert_eq!(Color::from_name("Green"), Some(Color::Green));
        assert_eq!(
            crate::input::schema_json("c", &[("c", true, <Choice<Color>>::TYPE)]),
            concat!(
                r#"{"version":2,"xark":""#,
                env!("CARGO_PKG_VERSION"),
                r#"","circuit":"c","inputs":[{"name":"c","visibility":"public","type":{"ref":"Choice<Color>"}}],"types":{"Choice<Color>":{"newtype":"field","encoding":{"choice":"Color"}},"Color":{"enum":["Red","Green","Blue"]}},"public_inputs":["c"]}"#
            )
        );
    }
}
