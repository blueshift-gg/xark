//! RSASSA-PKCS1-v1_5 signature verification for xark circuits.
//!
//! This is the 2048-bit instance: `n` and the signature are 17 little-endian
//! 121-bit limbs (2057 bits, enough for a 2048-bit modulus whose top limb is
//! 112 bits), the public exponent is fixed at 65537, and the hash is SHA-256.
//! The layout follows the zkGolf RSA reference: left-to-right
//! square-and-multiply, `sig < n`, and a full comparison with the
//! EMSA-PKCS1-v1_5 encoded message.
//!
//! Host-side decoding does the JSON, Base64, and DER work. The circuit takes the
//! modulus, the signature, and the 32-byte digest only.
//!
//! ```ignore
//! use xark_rsa::prelude::*;
//!
//! #[circuit]
//! pub fn rsa2048(n: Public<U2048>, sig: Private<U2048>, digest: Public<[u8; 32]>) {
//!     xark_rsa::verify_sha256(n, sig, digest);
//! }
//! ```

#![no_std]
// The xark subset style uses `x = x + y`; the frontend accepts both forms.
#![allow(clippy::assign_op_pattern)]

use xark::{Field, require_eq};
use xark_bignum::{Bignum, minus_one, mod_mul_bounded, require_lt};

/// 17 limbs of 121 bits: 2057 bits. A 2048-bit modulus has a 112-bit top limb.
pub const LIMBS: usize = 17;
/// Bits per limb, the zkGolf RSA-2048 reference width (`2·121 + 8 < 253`).
pub const BITS: usize = 121;

/// A 2048-bit RSA integer in the circuit.
pub type U2048 = Bignum<LIMBS, BITS>;

/// EMSA-PKCS1-v1_5 encoded message for SHA-256, with the digest set to zero.
///
/// The encoded message is 256 bytes:
/// `00 01 FF…FF 00 || SHA-256 DigestInfo || digest`, with 202 `FF` bytes.
/// Only the low 256 bits are variable; the rest is this constant. The three low
/// limbs also contain the low bits of the DigestInfo, so the digest is added to
/// them without carries (the digest occupies bits `0..256`, the DigestInfo
/// starts at bit 256).
const EM_CONST: [Field; LIMBS] = [
    Field::constant("0"),
    Field::constant("0"),
    Field::constant("457603010487612608686275013636521984"),
    Field::constant("2658455991569831745798613544783159489"),
    Field::constant("2658455991569831745807614120560689151"),
    Field::constant("2658455991569831745807614120560689151"),
    Field::constant("2658455991569831745807614120560689151"),
    Field::constant("2658455991569831745807614120560689151"),
    Field::constant("2658455991569831745807614120560689151"),
    Field::constant("2658455991569831745807614120560689151"),
    Field::constant("2658455991569831745807614120560689151"),
    Field::constant("2658455991569831745807614120560689151"),
    Field::constant("2658455991569831745807614120560689151"),
    Field::constant("2658455991569831745807614120560689151"),
    Field::constant("2658455991569831745807614120560689151"),
    Field::constant("2658455991569831745807614120560689151"),
    Field::constant("158456325028528675187087900671"),
];

/// The expected encoded message as limbs, given the 256 digest bits.
///
/// Bit `j` is the `2^j` place of the digest integer; bits `0..256` fill the low
/// limbs, and the rest of the encoded message is the constant PKCS#1 frame.
pub fn sha256_em_bits(bits: [Field; 256]) -> [Field; LIMBS] {
    let mut out = [Field::from(0u8); LIMBS];
    let mut k = 0usize;
    while k < LIMBS {
        let mut v = EM_CONST[k];
        if k < 3usize {
            let mut t = 0usize;
            while t < BITS {
                let j = BITS * k + t;
                if j < 256usize {
                    v = v + bits[j] * Field::from(1u128 << t);
                }
                t += 1;
            }
        }
        out[k] = v;
        k += 1;
    }
    out
}

/// The 256 digest bits of a 32-byte big-endian digest: bit 0 is the
/// least-significant bit of the last byte.
pub fn digest_bits(digest: [Field; 32]) -> [Field; 256] {
    let mut byte_bits = [Field::from(0u8); 256];
    let mut i = 0usize;
    while i < 32usize {
        let bits = digest[i].to_bits::<8>();
        let mut t = 0usize;
        while t < 8usize {
            byte_bits[i * 8 + t] = bits[t];
            t += 1;
        }
        i += 1;
    }
    // Reindex byte-major bits to the digest integer's bit order: bit `j` is
    // bit `j % 8` of byte `31 - j / 8`.
    let mut out = [Field::from(0u8); 256];
    let mut j = 0usize;
    while j < 256usize {
        out[j] = byte_bits[8 * (31 - j / 8) + j % 8];
        j += 1;
    }
    out
}

/// The expected encoded message as limbs, with the 32-byte big-endian digest
/// spliced into its low 256 bits.
pub fn sha256_em(digest: [Field; 32]) -> [Field; LIMBS] {
    sha256_em_bits(digest_bits(digest))
}

/// `base^65537 mod m`, left-to-right square-and-multiply.
///
/// `m_minus_1` must be exactly `m - 1` (from [`minus_one`]); `base` and `m` must
/// have limbs below `2^BITS`.
pub fn mod_exp_65537(
    base: [Field; LIMBS],
    m: [Field; LIMBS],
    m_minus_1: [Field; LIMBS],
) -> [Field; LIMBS] {
    // 65537 = 0b1_0000_0000_0000_0001. Start at the leading 1, square for the
    // 16 remaining bits, and multiply by the base at the final 1.
    let mut acc = base;
    let mut i = 0usize;
    while i < 16usize {
        acc = mod_mul_bounded::<LIMBS, BITS>(acc, acc, m, m_minus_1);
        i += 1;
    }
    mod_mul_bounded::<LIMBS, BITS>(acc, base, m, m_minus_1)
}

/// Verify an RSASSA-PKCS1-v1_5 / SHA-256 signature for a 2048-bit modulus from
/// raw limb arrays, range-checking them first.
///
/// Use this when the circuit takes `[Field; 17]` arrays; a `Bignum` typed input
/// is already range-checked by its input reader, so [`verify_sha256`] skips the
/// duplicate check.
pub fn verify_sha256_limbs(n: [Field; LIMBS], sig: [Field; LIMBS], digest: [Field; 32]) {
    xark_bignum::range_check_limbs::<LIMBS, BITS>(n);
    xark_bignum::range_check_limbs::<LIMBS, BITS>(sig);
    verify_checked(Bignum::new(n), Bignum::new(sig), digest);
}

/// Verify an RSASSA-PKCS1-v1_5 / SHA-256 signature for a 2048-bit modulus.
///
/// `n` and `sig` must come from a range-checked `Bignum` (the `Public<U2048>` /
/// `Private<U2048>` input reader range-checks every limb). The circuit also
/// enforces that `n` has exactly 2048 bits, that `sig < n`, and that
/// `sig^65537 mod n` equals the PKCS#1 v1.5 encoding of `digest`.
pub fn verify_sha256(n: U2048, sig: U2048, digest: [Field; 32]) {
    verify_checked(n, sig, digest)
}

fn verify_checked_bits(n: U2048, sig: U2048, bits: [Field; 256]) {
    // n is exactly 2048 bits: the top limb is below 2^112 and its bit 111 is 1.
    let top = n.limbs[16].to_bits::<112>();
    require_eq(top[111], Field::from(1u8));

    let m_minus_1 = minus_one::<LIMBS, BITS>(n.limbs);
    require_lt::<LIMBS, BITS>(sig.limbs, m_minus_1);

    let recovered = mod_exp_65537(sig.limbs, n.limbs, m_minus_1);
    let expected = sha256_em_bits(bits);
    let mut i = 0usize;
    while i < LIMBS {
        require_eq(recovered[i], expected[i]);
        i += 1;
    }
}

fn verify_checked(n: U2048, sig: U2048, digest: [Field; 32]) {
    verify_checked_bits(n, sig, digest_bits(digest))
}

/// Verify a signature over a SHA-256 digest supplied as the eight big-endian
/// 32-bit words the `xark-sha256` gadget returns.
///
/// Use this in a circuit that hashes the message itself:
///
/// ```ignore
/// let digest = xark_sha256::sha256::<144>(body);
/// xark_rsa::verify_sha256_words(n, sig, digest);
/// ```
pub fn verify_sha256_words(n: U2048, sig: U2048, digest: [[Field; 32]; 8]) {
    // The digest integer's bit `j` is bit `j % 32` of word `7 - j / 32`: the
    // SHA-256 words are big-endian, each word's bits are little-endian.
    let mut bits = [Field::from(0u8); 256];
    let mut j = 0usize;
    while j < 256usize {
        bits[j] = digest[7 - j / 32][j % 32];
        j += 1;
    }
    verify_checked_bits(n, sig, bits);
}

/// The gadget's public API alongside the xark prelude.
pub mod prelude {
    pub use crate::*;
    pub use xark::prelude::*;
}
