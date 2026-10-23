//! Field constants: coefficients in a prime field `F_p`, stored as *exact signed
//! big integers* (not reduced to `[0, p)`).
//!
//! Storing exact integers keeps readable coefficients (`-1`, `2`) and full
//! field-sized round constants (~254-bit). Since `(a mod p) + (b mod p) ≡ (a + b)
//! mod p` (and likewise for `*`), exact integer arithmetic preserves the field
//! element; a backend reduces into `[0, p)` once it knows the modulus.
//!
//! Values are overwhelmingly tiny, so we store an `i64` inline and fall back to a
//! shared heap `BigInt` only for rare field-sized values. The `Small`/`Big` split
//! is *canonical* (a value is `Small` iff it fits in `i64`), so derived `Eq` is
//! correct and the serialized decimal is byte-identical.
//!
//! A big value is unreduced and can be far wider than the field (folded MDS
//! products in Poseidon run to thousands of bits), so reducing it is costly. Its
//! BN254 reduction is computed once and cached on the shared allocation: every
//! clone (each template call's copy of a coefficient) reuses it.

use std::sync::{Arc, OnceLock};

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Repr {
    /// A value that fits in `i64` (the common case: coefficients, small consts).
    Small(i64),
    /// A value outside `i64` range (e.g. a ~254-bit round constant). Maintained
    /// so that it never holds a value representable as `Small` (canonical).
    Big(Arc<Big>),
}

/// A big value and its BN254 reduction (computed on first use). Compared,
/// ordered and printed by `value` alone.
struct Big {
    value: BigInt,
    bn254: OnceLock<ark_bn254::Fr>,
}

impl PartialEq for Big {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
impl Eq for Big {}
impl PartialOrd for Big {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Big {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.value.cmp(&other.value)
    }
}
impl std::fmt::Debug for Big {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(f)
    }
}

/// A field constant, serialized transparently as the bare decimal string
/// (`"123"`).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FieldConst {
    repr: Repr,
}

/// Normalize a `BigInt` into the canonical `Repr` (`Small` iff it fits in `i64`).
fn norm(v: BigInt) -> Repr {
    match v.to_i64() {
        Some(i) => Repr::Small(i),
        None => Repr::Big(Arc::new(Big {
            value: v,
            bn254: OnceLock::new(),
        })),
    }
}

/// `v mod r` for BN254's scalar field `r` (any sign or width).
fn reduce_bn254(v: &BigInt) -> ark_bn254::Fr {
    use ark_bn254::Fr;
    use ark_ff::{BigInt as Limbs, BigInteger, PrimeField};
    static R: OnceLock<num_bigint::BigUint> = OnceLock::new();
    let r = R.get_or_init(|| num_bigint::BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le()));
    let m = v.magnitude() % r;
    let mut l = [0u64; 4];
    for (d, x) in l.iter_mut().zip(m.to_u64_digits()) {
        *d = x;
    }
    let f = Fr::from_bigint(Limbs::new(l)).expect("reduced below the modulus");
    if v.is_negative() { -f } else { f }
}

impl FieldConst {
    /// This constant reduced into BN254's scalar field — computed once per big
    /// value and shared by its clones.
    pub fn to_bn254_fr(&self) -> ark_bn254::Fr {
        use ark_bn254::Fr;
        match &self.repr {
            Repr::Small(i) if *i < 0 => -Fr::from(i.unsigned_abs()),
            Repr::Small(i) => Fr::from(*i as u64),
            Repr::Big(b) => *b.bn254.get_or_init(|| reduce_bn254(&b.value)),
        }
    }

    /// The value as a `BigInt` (allocates only for the `Big` case).
    pub fn big(&self) -> BigInt {
        match &self.repr {
            Repr::Small(i) => BigInt::from(*i),
            Repr::Big(b) => b.value.clone(),
        }
    }

    /// The value as a borrowed `BigInt` when it is outside `i64` range (`None` for
    /// a small value) — for callers that only inspect it.
    pub fn as_big(&self) -> Option<&BigInt> {
        match &self.repr {
            Repr::Small(_) => None,
            Repr::Big(b) => Some(&b.value),
        }
    }

    /// The value as a `BigInt`, borrowed when already big (no clone).
    fn big_cow(&self) -> std::borrow::Cow<'_, BigInt> {
        match &self.repr {
            Repr::Small(i) => std::borrow::Cow::Owned(BigInt::from(*i)),
            Repr::Big(b) => std::borrow::Cow::Borrowed(&b.value),
        }
    }

    pub fn from_bigint(value: BigInt) -> Self {
        FieldConst { repr: norm(value) }
    }

    pub fn from_i64(value: i64) -> Self {
        FieldConst {
            repr: Repr::Small(value),
        }
    }

    /// Build from a decimal string, validating that it parses.
    pub fn from_decimal(s: &str) -> Option<Self> {
        let value: BigInt = s.trim().parse().ok()?;
        Some(FieldConst::from_bigint(value))
    }

    pub fn zero() -> Self {
        FieldConst::from_i64(0)
    }

    pub fn one() -> Self {
        FieldConst::from_i64(1)
    }

    /// The canonical decimal string.
    pub fn decimal(&self) -> String {
        match &self.repr {
            Repr::Small(i) => i.to_string(),
            Repr::Big(b) => b.value.to_string(),
        }
    }

    /// Best-effort narrow to `i64` (used only where small values are expected).
    pub fn as_i64(&self) -> Option<i64> {
        match &self.repr {
            Repr::Small(i) => Some(*i),
            Repr::Big(_) => None,
        }
    }

    pub fn is_zero(&self) -> bool {
        matches!(self.repr, Repr::Small(0))
    }

    pub fn is_one(&self) -> bool {
        matches!(self.repr, Repr::Small(1))
    }

    pub fn is_neg_one(&self) -> bool {
        matches!(self.repr, Repr::Small(-1))
    }

    pub fn is_negative(&self) -> bool {
        match &self.repr {
            Repr::Small(i) => *i < 0,
            Repr::Big(b) => b.value.is_negative(),
        }
    }

    pub fn add(&self, other: &FieldConst) -> FieldConst {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.repr, &other.repr)
            && let Some(s) = a.checked_add(*b)
        {
            return FieldConst {
                repr: Repr::Small(s),
            };
        }
        FieldConst::from_bigint(&*self.big_cow() + &*other.big_cow())
    }

    pub fn mul(&self, other: &FieldConst) -> FieldConst {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.repr, &other.repr)
            && let Some(p) = a.checked_mul(*b)
        {
            return FieldConst {
                repr: Repr::Small(p),
            };
        }
        FieldConst::from_bigint(&*self.big_cow() * &*other.big_cow())
    }

    pub fn neg(&self) -> FieldConst {
        if let Repr::Small(a) = &self.repr
            && let Some(n) = a.checked_neg()
        {
            return FieldConst {
                repr: Repr::Small(n),
            };
        }
        FieldConst::from_bigint(-&*self.big_cow())
    }

    /// If this constant fits in `n` bits (non-negative, `< 2^n`), return its
    /// little-endian bits; else `None`. Lets `Field::to_bits::<N>` of a constant
    /// const-fold, avoiding booleanity/recomposition constraints.
    pub fn to_bits_le(&self, n: usize) -> Option<Vec<bool>> {
        // `to_biguint` is `None` for a negative value (cannot fit in `n` unsigned bits).
        let v = self.big().to_biguint()?;
        if v.bits() as usize > n {
            return None;
        }
        Some((0..n).map(|i| v.bit(i as u64)).collect())
    }

    /// Single-parse rendering helper: returns `(is_negative, abs_is_one,
    /// |value| as a decimal)`. Cheap for the common `Small` case (no BigInt at all).
    pub fn render_parts(&self) -> (bool, bool, String) {
        match &self.repr {
            Repr::Small(i) => (*i < 0, i.unsigned_abs() == 1, i.unsigned_abs().to_string()),
            Repr::Big(b) => {
                let abs = b.value.abs();
                (b.value.is_negative(), abs.is_one(), abs.to_string())
            }
        }
    }
}

// Serialize transparently as the bare decimal string, and parse it back.
impl Serialize for FieldConst {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.decimal())
    }
}

impl<'de> Deserialize<'de> for FieldConst {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = String::deserialize(deserializer)?;
        FieldConst::from_decimal(&s)
            .ok_or_else(|| serde::de::Error::custom(format!("invalid field constant `{s}`")))
    }
}

impl From<i64> for FieldConst {
    fn from(value: i64) -> Self {
        FieldConst::from_i64(value)
    }
}

impl From<&str> for FieldConst {
    fn from(value: &str) -> Self {
        FieldConst::from_decimal(value).unwrap_or_else(FieldConst::zero)
    }
}

impl From<String> for FieldConst {
    fn from(value: String) -> Self {
        FieldConst::from(value.as_str())
    }
}
