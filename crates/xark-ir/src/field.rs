//! Field constants.
//!
//! Coefficients live in a prime field `F_p`, but we store them as *exact signed
//! big integers*, not reduced to `[0, p)`. This keeps readable coefficients like
//! `-1` and `2` while still handling full field-sized round constants (~254-bit)
//! exactly. Because `(a mod p) + (b mod p) ≡ (a + b) mod p` and likewise for
//! multiplication, exact integer arithmetic preserves the represented field
//! element; canonical reduction into `[0, p)` is something a backend does when it
//! knows the modulus.
//!
//! Representation: coefficients are overwhelmingly tiny (`0`, `1`, `-1`, `2`, …),
//! so we store an `i64` inline and only fall back to a heap `BigInt` for the rare
//! field-sized value. This makes cloning a coefficient `Copy`-cheap in the common
//! case (it was the dominant lower-phase cost when every coefficient was a heap
//! `String`) and lets linear-combination arithmetic use native `i64` ops instead
//! of parsing/formatting decimal strings. The `Small`/`Big` split is *canonical*
//! — a value is `Small` iff it fits in `i64` — so derived `PartialEq`/`Eq` are
//! correct and the serialized decimal is unchanged (byte-identical output).

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Repr {
    /// A value that fits in `i64` (the common case: coefficients, small consts).
    Small(i64),
    /// A value outside `i64` range (e.g. a ~254-bit round constant). Maintained
    /// so that it never holds a value representable as `Small` (canonical).
    Big(BigInt),
}

/// A field constant. Serialized transparently as the bare decimal string
/// (`"123"`), since the wrapper key is pure noise in `circuit.json` / `r1cs.json`
/// (every coefficient carries one).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldConst {
    repr: Repr,
}

/// Normalize a `BigInt` into the canonical `Repr` (`Small` iff it fits in `i64`).
fn norm(v: BigInt) -> Repr {
    match v.to_i64() {
        Some(i) => Repr::Small(i),
        None => Repr::Big(v),
    }
}

impl FieldConst {
    /// The value as a `BigInt` (allocates only for the `Big` case).
    pub fn big(&self) -> BigInt {
        match &self.repr {
            Repr::Small(i) => BigInt::from(*i),
            Repr::Big(b) => b.clone(),
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

    /// The canonical decimal string (`BigInt::to_string()` output — unchanged from
    /// the previous string-backed representation, so serialized bytes match).
    pub fn decimal(&self) -> String {
        match &self.repr {
            Repr::Small(i) => i.to_string(),
            Repr::Big(b) => b.to_string(),
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
            Repr::Big(b) => b.is_negative(),
        }
    }

    /// Absolute value, as a decimal string (for rendering `- 5` vs `+ 5`).
    pub fn abs_decimal(&self) -> String {
        match &self.repr {
            // `unsigned_abs` handles `i64::MIN` without overflow.
            Repr::Small(i) => i.unsigned_abs().to_string(),
            Repr::Big(b) => b.abs().to_string(),
        }
    }

    pub fn add(&self, other: &FieldConst) -> FieldConst {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.repr, &other.repr) {
            if let Some(s) = a.checked_add(*b) {
                return FieldConst {
                    repr: Repr::Small(s),
                };
            }
        }
        FieldConst::from_bigint(self.big() + other.big())
    }

    pub fn mul(&self, other: &FieldConst) -> FieldConst {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.repr, &other.repr) {
            if let Some(p) = a.checked_mul(*b) {
                return FieldConst {
                    repr: Repr::Small(p),
                };
            }
        }
        FieldConst::from_bigint(self.big() * other.big())
    }

    pub fn neg(&self) -> FieldConst {
        if let Repr::Small(a) = &self.repr {
            if let Some(n) = a.checked_neg() {
                return FieldConst {
                    repr: Repr::Small(n),
                };
            }
        }
        FieldConst::from_bigint(-self.big())
    }

    /// If this constant is a non-negative integer that fits in `n` bits, return
    /// its little-endian bits (`bits[0]` = LSB, each `false`/`true` = `0`/`1`).
    /// Returns `None` when the value is negative or `>= 2^n` — i.e. it "does not
    /// fit in `n` bits". Used to const-fold `Field::to_bits::<N>` of a constant:
    /// the bits are known, so no booleanity/recomposition constraints are needed.
    pub fn to_bits_le(&self, n: usize) -> Option<Vec<bool>> {
        // `to_biguint` is `None` for a negative value (which cannot fit in `n`
        // unsigned bits); `bits()` is the count of significant bits.
        let v = self.big().to_biguint()?;
        if v.bits() as usize > n {
            return None;
        }
        Some((0..n).map(|i| v.bit(i as u64)).collect())
    }

    /// Single-parse rendering helper: returns `(is_negative, abs_is_one,
    /// abs_decimal)`. Cheap for the common `Small` case (no BigInt at all).
    pub fn render_parts(&self) -> (bool, bool, String) {
        match &self.repr {
            Repr::Small(i) => (*i < 0, i.unsigned_abs() == 1, i.unsigned_abs().to_string()),
            Repr::Big(b) => {
                let abs = b.abs();
                (b.is_negative(), abs.is_one(), abs.to_string())
            }
        }
    }
}

// Serialize transparently as the bare decimal string, and parse it back — keeping
// `circuit.json` / `r1cs.json` byte-identical to the previous representation.
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
