//! Field constants.
//!
//! Coefficients live in a prime field `F_p`, but we store them as *exact signed
//! big integers* (decimal), not reduced to `[0, p)`. This keeps readable
//! coefficients like `-1` and `2` while still handling full field-sized round
//! constants (~254-bit) exactly. Because `(a mod p) + (b mod p) ≡ (a + b) mod p`
//! and likewise for multiplication, exact integer arithmetic preserves the
//! represented field element; canonical reduction into `[0, p)` is something a
//! backend does when it knows the modulus.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FieldConst {
    pub decimal: String,
}

impl FieldConst {
    /// Parse the stored decimal into a `BigInt` (defaults to 0 if malformed,
    /// which cannot happen for values we construct ourselves).
    fn big(&self) -> BigInt {
        self.decimal.parse::<BigInt>().unwrap_or_else(|_| BigInt::zero())
    }

    pub fn from_bigint(value: BigInt) -> Self {
        FieldConst {
            decimal: value.to_string(),
        }
    }

    pub fn from_i64(value: i64) -> Self {
        FieldConst {
            decimal: value.to_string(),
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

    /// Best-effort narrow to `i64` (used only where small values are expected).
    pub fn as_i64(&self) -> Option<i64> {
        self.decimal.parse::<i64>().ok()
    }

    // These check the *canonical* decimal string directly — we always store
    // `BigInt::to_string()` output, so "0"/"1"/"-1" are unambiguous. Avoiding
    // the BigInt parse here matters a lot: `simplified()` calls `is_zero` on
    // every coefficient, and it runs on every linear-combination operation.
    pub fn is_zero(&self) -> bool {
        self.decimal == "0"
    }

    pub fn is_one(&self) -> bool {
        self.decimal == "1"
    }

    pub fn is_neg_one(&self) -> bool {
        self.decimal == "-1"
    }

    pub fn is_negative(&self) -> bool {
        self.big().is_negative()
    }

    /// Absolute value, as a decimal string (for rendering `- 5` vs `+ 5`).
    pub fn abs_decimal(&self) -> String {
        self.big().abs().to_string()
    }

    pub fn add(&self, other: &FieldConst) -> FieldConst {
        FieldConst::from_bigint(self.big() + other.big())
    }

    pub fn mul(&self, other: &FieldConst) -> FieldConst {
        FieldConst::from_bigint(self.big() * other.big())
    }

    pub fn neg(&self) -> FieldConst {
        FieldConst::from_bigint(-self.big())
    }

    /// Single-parse rendering helper: returns `(is_negative, abs_is_one,
    /// abs_decimal)` with exactly one BigInt parse (vs. calling `is_negative` +
    /// `is_neg_one` + `is_one` + `abs_decimal` separately, which parse 4×). This
    /// is on the hot path for debug-note rendering.
    pub fn render_parts(&self) -> (bool, bool, String) {
        let b = self.big();
        let abs = b.abs();
        (b.is_negative(), abs.is_one(), abs.to_string())
    }
}

impl From<i64> for FieldConst {
    fn from(value: i64) -> Self {
        FieldConst::from_i64(value)
    }
}

impl From<&str> for FieldConst {
    fn from(value: &str) -> Self {
        FieldConst {
            decimal: value.to_string(),
        }
    }
}

impl From<String> for FieldConst {
    fn from(value: String) -> Self {
        FieldConst { decimal: value }
    }
}
