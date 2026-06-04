//! Conversion between Noir's `FieldElement` (BN254 scalar) and `ark_bn254::Fr`.
//!
//! Noir's `FieldElement<Fr>` is also backed by Arkworks under the hood for the
//! `bn254` feature, but rather than rely on type identity we convert via the
//! canonical big-endian byte representation. This keeps the boundary explicit
//! and tested.

use acir::{AcirField, FieldElement};
use ark_bn254::Fr;
use ark_ff::PrimeField;
use num_bigint::BigUint;

use crate::error::BackendError;

/// Convert a Noir [`FieldElement`] into an `ark_bn254::Fr`.
pub fn noir_field_to_fr(value: &FieldElement) -> Fr {
    // `to_be_bytes` returns 32 bytes for BN254.
    let bytes = value.to_be_bytes();
    Fr::from_be_bytes_mod_order(&bytes)
}

/// Convert an `ark_bn254::Fr` into its canonical big-endian 32-byte form.
pub fn fr_to_be_bytes(value: &Fr) -> [u8; 32] {
    let big: BigUint = (*value).into();
    let bytes = big.to_bytes_be();
    let mut out = [0u8; 32];
    let pad = 32 - bytes.len();
    out[pad..].copy_from_slice(&bytes);
    out
}

/// Parse a decimal string into an `ark_bn254::Fr`.
pub fn fr_from_decimal_str(s: &str) -> Result<Fr, BackendError> {
    let s = s.trim();
    let big: BigUint = s
        .parse()
        .map_err(|e: num_bigint::ParseBigIntError| BackendError::FieldDecode(e.to_string()))?;
    let bytes = big.to_bytes_be();
    Ok(Fr::from_be_bytes_mod_order(&bytes))
}

/// Format an `ark_bn254::Fr` as a decimal string.
pub fn fr_to_decimal_string(value: &Fr) -> String {
    let big: BigUint = (*value).into();
    big.to_str_radix(10)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_small_value() {
        let f = FieldElement::from(42u128);
        let fr = noir_field_to_fr(&f);
        let s = fr_to_decimal_string(&fr);
        assert_eq!(s, "42");
    }

    #[test]
    fn roundtrip_via_be_bytes() {
        let f = FieldElement::from(123456789u128);
        let fr = noir_field_to_fr(&f);
        let bytes = fr_to_be_bytes(&fr);
        let fr2 = Fr::from_be_bytes_mod_order(&bytes);
        assert_eq!(fr, fr2);
    }

    #[test]
    fn decimal_roundtrip() {
        let fr = fr_from_decimal_str("9").unwrap();
        assert_eq!(fr_to_decimal_string(&fr), "9");
    }
}
