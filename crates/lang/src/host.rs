//! Host-side helpers for building circuit input values: what the gadgets' `From`
//! impls (an Ed25519 key's `[u8; 32]` → `PointL`, a scalar's bytes → `Fq`) and
//! `#[input]`'s `number`/`bytes` encodings use, so every limb split agrees with the
//! circuit's leaves.

use alloc::vec::Vec;

use crate::Field;

/// An input type with a natural big-endian byte encoding of `BYTES` bytes (a
/// scalar's 32 bytes, a point's coordinates back to back, an Ed25519 key's
/// compressed form): what `#[input]`'s `number`/`bytes` encodings build `From<[u8; BYTES]>`
/// from.
pub trait FromBeBytes: Sized {
    /// The encoding's length.
    const BYTES: usize;
    /// Build the value from exactly `BYTES` bytes. Panics on a value the type can't
    /// hold (too large, or not a point).
    fn from_be_bytes(bytes: &[u8]) -> Self;
}

pub use crate::natural_bytes;

/// A big-endian byte string (a scalar's or coordinate's natural encoding) as `N`
/// little-endian `bits`-bit limbs. Panics if the value doesn't fit `N * bits` bits,
/// or if `bits > 248` (a limb must be a field element).
pub fn limb_fields<const N: usize>(be_bytes: &[u8], bits: u32) -> [Field; N] {
    assert!(
        bits <= 248,
        "a limb of {bits} bits doesn't fit a field element"
    );
    let total = be_bytes.len() * 8;
    let bit = |j: usize| j < total && (be_bytes[be_bytes.len() - 1 - j / 8] >> (j % 8)) & 1 == 1;
    let fits = (N * bits as usize..total).all(|j| !bit(j));
    assert!(fits, "value doesn't fit {N} limbs of {bits} bits");
    core::array::from_fn(|i| {
        let mut le = [0u8; 32];
        for k in 0..bits as usize {
            if bit(i * bits as usize + k) {
                le[k / 8] |= 1 << (k % 8);
            }
        }
        Field::from_le_bytes(&le)
    })
}

/// A decimal or `0x`-hex string's big-endian bytes (any size). Panics on anything
/// else.
pub fn be_bytes_of(value: &str) -> Vec<u8> {
    let v = value.trim();
    let (digits, radix) = match v.strip_prefix("0x").or_else(|| v.strip_prefix("0X")) {
        Some(h) => (h, 16u32),
        None => (v, 10u32),
    };
    assert!(
        !digits.is_empty(),
        "invalid value `{value}` (expected decimal or 0x-hex)"
    );
    let mut be: Vec<u8> = Vec::new(); // big-endian magnitude
    for c in digits.chars() {
        let d = c
            .to_digit(radix)
            .unwrap_or_else(|| panic!("invalid value `{value}` (expected decimal or 0x-hex)"));
        let mut carry = d;
        for b in be.iter_mut().rev() {
            let t = *b as u32 * radix + carry;
            *b = t as u8;
            carry = t >> 8;
        }
        while carry > 0 {
            be.insert(0, carry as u8);
            carry >>= 8;
        }
    }
    be
}

/// [`limb_fields`] from a decimal or `0x`-hex string (a bignum's value).
pub fn limb_fields_str<const N: usize>(value: &str, bits: u32) -> [Field; N] {
    limb_fields(&be_bytes_of(value), bits)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::String;

    #[test]
    fn limbs_split_and_parse() {
        // 2^86 + 5 over 3x86-bit limbs: [5, 1, 0].
        let mut be = [0u8; 32];
        be[31] = 5;
        be[31 - 10] = 0x40; // bit 86 = byte 10, bit 6
        let l: [Field; 3] = limb_fields(&be, 86);
        assert_eq!(l.map(|f| f.to_decimal()), ["5", "1", "0"].map(String::from));
        assert_eq!(be_bytes_of("0x0102"), [1, 2]);
        assert_eq!(be_bytes_of("258"), [1, 2]);
        let l: [Field; 2] = limb_fields_str("340282366920938463463374607431768211457", 128); // 2^128 + 1
        assert_eq!(l.map(|f| f.to_decimal()), ["1", "1"].map(String::from));
    }
}
