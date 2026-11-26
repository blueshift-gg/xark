//! RSASSA-PKCS1-v1_5 signature verification for xark circuits.
//!
//! This is the 2048-bit instance: `n` and the signature are 17 little-endian
//! 121-bit limbs (2057 bits, enough for a 2048-bit modulus whose top limb is
//! 112 bits), the public exponent is fixed at 65537, and the hash is SHA-256.
//! The layout starts from the zkGolf RSA reference: left-to-right
//! square-and-multiply, `sig < n`, and a comparison with the
//! EMSA-PKCS1-v1_5 encoded message (fused into the terminal multiply here).
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

// ---------------------------------------------------------------------------
// The proving path: 25 x 82-bit limbs, lazy reduction, paired-column carries.
//
// `LIMBS x BITS` (17 x 121) is the input and public API layout; the modular
// chain runs in a *wider* limb count (25 x 82) because a group of two 82-bit
// columns has a 164-bit weight, so two columns' products still fit in one
// `Fr` element and can share one carry. A 121-bit limb's product with a
// 121-bit limb is already 242 bits, so no two 121-bit columns can share a
// carry.
//
// Three other things happen here:
//
//   * lazy reduction: an intermediate residue is only proved `< 2^2048`, not
//     `< n`. The chain stays congruent to `sig^(2^i) (mod n)`, and the final
//     fused step pins the canonical target, so canonicality of the
//     intermediates is never needed (see `verify_checked_bits`).
//   * the final multiply's remainder *is* the encoded message: no remainder
//     limbs are witnessed or certified, and the 17-limb equality disappears.
//   * the convolution's columns are paired: a group of two 82-bit columns has
//     a 164-bit weight, so its weighted sum still fits in `Fr` and the pair
//     shares one carry. The carry certificate drops from 32 x 128 bits to
//     24 x 89 bits; the schoolbook products are unchanged.
//
// Soundness bounds are documented on each function; `WIDE_*` are chosen from
// them. The arithmetic below is over `Fr`, so every `const` bound is checked
// against `Fr ~ 2^253.6`.
// ---------------------------------------------------------------------------

/// Limbs of the internal 82-bit representation: 25 * 82 = 2050 bits.
const WIDE_LIMBS: usize = 25;
/// Internal limb width; two columns of it still fit one `Fr` element.
const WIDE_BITS: usize = 82;
/// A pair of internal columns spans `2^(2*82)`.
const GROUP_BITS: usize = 2 * WIDE_BITS;
/// A group carry is below `2^(82 + log2(50)) < 2^87.7`; biased by `2^88`, the
/// witnessed value is below `2^89`.
const GROUP_CARRY_BITS: usize = 89;
/// The group-carry bias, so the witness is non-negative.
const GROUP_BIAS_BITS: usize = 88;
/// Added to a group sum so it is non-negative; `2^252 = 2^88 * 2^164`.
const GROUP_OFF_BITS: usize = 252;
/// A 121-bit input limb shifted by at most 78 bits is below `2^199`, so the
/// conversion carry is below `2^117.1`: 118 bits cover it.
const CONVERT_CARRY_BITS: usize = 118;

/// `2^e` as a compile-time-folded field constant.
fn pow2(e: usize) -> Field {
    let mut p = Field::from(1u8);
    let mut i = 0usize;
    while i < e {
        p = p + p;
        i += 1;
    }
    p
}

/// Prove `v < 2^W` with `W - 1` witnessed bits and the top bit derived
/// affinely: `top = v - Σ_{i<W-1} 2^i b_i` and `top * (top - 2^(W-1)) = 0`
/// forces `top ∈ {0, 2^(W-1)}`, so `v` is the low part or the low part plus
/// `2^(W-1)`, both below `2^W`.
///
/// The measured cost is `W + 1` rows, the same as `bignum::range_check_limbs`
/// and `to_bits`: the frontend turns the affine `top`'s booleanity into two
/// rows. It is kept because it returns the top bit the 2048-bit `n` check needs,
/// not as a row-count saving.
fn range_derived<const W: usize>(v: Field) {
    let _ = range_derived_top::<W>(v);
}

/// [`range_derived`], returning the top bit `top` (an affine expression).
fn range_derived_top<const W: usize>(v: Field) -> Field {
    const { assert!(W >= 1 && W <= 128, "range_derived: W out of range") };
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i + 1 < W {
        let bit = Field::hint_bit(v, i);
        bit.require_bool();
        acc = acc + bit * pow;
        pow = pow + pow;
        i += 1;
    }
    let top = v - acc;
    require_eq(
        top * (top - Field::from(1u128 << (W - 1))),
        Field::from(0u8),
    );
    top
}

/// The internal 82-bit limbs of `n` (digest zero), from `EM_CONST`'s integer.
const EM82_CONST: [Field; WIDE_LIMBS] = [
    Field::constant("0"),
    Field::constant("0"),
    Field::constant("0"),
    Field::constant("1908058575186009548423168"),
    Field::constant("227580944067680599951361"),
    Field::constant("4835703278458516698824640"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("4835703278458516698824703"),
    Field::constant("36893488147419103231"),
];

/// [`sha256_em_bits`] in the internal 82-bit representation.
///
/// The digest's 256 bits live in bits `0..256`: the low 246 fill limbs 0..2,
/// the top 10 are bits `0..10` of limb 3. The rest of limb 3 starts at bit 256
/// (the DigestInfo), so the addition is carry-free.
fn sha256_em_bits_82(bits: [Field; 256]) -> [Field; WIDE_LIMBS] {
    let mut out = EM82_CONST;
    let mut k = 0usize;
    while k < 3usize {
        let mut t = 0usize;
        while t < WIDE_BITS {
            let j = WIDE_BITS * k + t;
            out[k] = out[k] + bits[j] * Field::from(1u128 << t);
            t += 1;
        }
        k += 1;
    }
    let mut t = 0usize;
    while t < 256usize - 3 * WIDE_BITS {
        out[3] = out[3] + bits[3 * WIDE_BITS + t] * Field::from(1u128 << t);
        t += 1;
    }
    out
}

/// Re-limb `x: [Field; 17]` (each limb `< 2^121`) into 25 little-endian 82-bit
/// limbs, proving the value is unchanged. Returns the top bit of limb 24.
///
/// Column `q_i = floor(121 i / 82)` receives `x_i * 2^(121 i - 82 q_i)`. The
/// shifts are at most 78, so a column term is below `2^199` and the carry
/// below `2^118`; every column equation is below `Fr`, hence lifts from `Fr`
/// to the integers. The carry chain telescopes to
/// `Σ y_j 2^(82 j) = Σ x_i 2^(121 i)`; with `y` digits below `2^82` that is
/// the unique base-`2^82` representation of the value.
///
/// Precondition: every `x[i] < 2^121` (the `Bignum` input reader, or
/// `range_check_limbs`, proves it) and the value is below `2^2048` (both
/// callers pass `n`, and `sig < n`). The 80-bit top-limb check is also what
/// makes the output representation exactly 2048 bits.
fn convert_wide(x: [Field; LIMBS]) -> ([Field; WIDE_LIMBS], Field) {
    let mut cols = [Field::from(0u8); WIDE_LIMBS];
    let mut i = 0usize;
    while i < LIMBS {
        let e = BITS * i;
        let q = e / WIDE_BITS;
        let r = e % WIDE_BITS;
        cols[q] = cols[q] + x[i] * Field::from(1u128 << r);
        i += 1;
    }
    let two_b = pow2(WIDE_BITS);
    let mut y = [Field::from(0u8); WIDE_LIMBS];
    let mut carry = Field::from(0u8);
    let mut j = 0usize;
    while j + 1 < WIDE_LIMBS {
        let num = cols[j] + carry;
        let dr = Field::hint_div_rem(num, two_b);
        let (c, limb) = (dr[0], dr[1]);
        require_eq(num, two_b * c + limb);
        range_derived::<WIDE_BITS>(limb);
        range_derived::<CONVERT_CARRY_BITS>(c);
        y[j] = limb;
        carry = c;
        j += 1;
    }
    let num = cols[WIDE_LIMBS - 1] + carry;
    let dr = Field::hint_div_rem(num, two_b);
    require_eq(num, two_b * dr[0] + dr[1]);
    require_eq(dr[0], Field::from(0u8));
    let top = range_derived_top::<80>(dr[1]);
    y[WIDE_LIMBS - 1] = dr[1];
    (y, top)
}

/// Pack the big-endian octet strings used by the zkGolf RSA interface into the
/// 25 x 82-bit internal limbs. Each byte is decomposed with `to_bits::<8>`
/// (which also pins it to a byte); bit `8*(255-i)+t` of the integer is bit `t`
/// of byte `i`. The returned field is the modulus/signature top bit (bit 2047),
/// which is `1` exactly when the integer is 2048 bits.
fn bytes_to_wide(bytes: [Field; 256]) -> ([Field; WIDE_LIMBS], Field) {
    let mut bits = [Field::from(0u8); 2048];
    let mut i = 0usize;
    while i < 256usize {
        let b = bytes[i].to_bits::<8>();
        let mut t = 0usize;
        while t < 8usize {
            // Byte 0 is the most significant octet of the big-endian encoding.
            bits[8 * (255 - i) + t] = b[t];
            t += 1;
        }
        i += 1;
    }
    let mut out = [Field::from(0u8); WIDE_LIMBS];
    let mut q = 0usize;
    while q < WIDE_LIMBS {
        let mut t = 0usize;
        while t < WIDE_BITS {
            let j = WIDE_BITS * q + t;
            if j < 2048 {
                out[q] = out[q] + bits[j] * Field::from(1u128 << t);
            }
            t += 1;
        }
        q += 1;
    }
    (out, bits[2047])
}

/// Range-check an internal quotient: 24 limbs below `2^82`, the top below
/// `2^81` (a lazy residue is below `2^2048`; `a*b - r < 2^4096`, and
/// `n >= 2^2047`, so `q < 2^2049`).
fn range_check_q(q: [Field; WIDE_LIMBS]) {
    let mut i = 0usize;
    while i + 1 < WIDE_LIMBS {
        range_derived::<WIDE_BITS>(q[i]);
        i += 1;
    }
    range_derived::<81>(q[WIDE_LIMBS - 1]);
}

/// Range-check a lazy remainder: 24 limbs below `2^82`, the top below `2^80`
/// (it is only proved `< 2^2048`, not `< n`).
fn range_check_r(r: [Field; WIDE_LIMBS]) {
    let mut i = 0usize;
    while i + 1 < WIDE_LIMBS {
        range_derived::<WIDE_BITS>(r[i]);
        i += 1;
    }
    range_derived::<80>(r[WIDE_LIMBS - 1]);
}

/// The integer identity `a·b == q·m + r` (or `+ em`), one row per pair of
/// columns.
///
/// For columns `c = 2j, 2j+1`, `S_j = d_{2j} + 2^82 d_{2j+1}` with
/// `d_c = Σ_{i+k=c} a_i b_k - Σ_{i+k=c} q_i m_k - rhs_c`. The rows impose
/// `S_j + k_{j-1} = k_j 2^164`, `k_{-1} = k_23 = 0`, so multiplying by
/// `2^(164 j)` and summing telescopes to `Σ_c d_c 2^(82 c) = 0`: the integer
/// identity. The top column closes the chain.
///
/// Bounds (`L = 25`, `B = 82`): `|d_c| <= 2·25·(2^82-1)^2 < 2^169.7`, so
/// `|S_j| < 2^251.7`; the fixed point `|k| < 2^251.7/(2^164-1) < 2^87.7`.
/// With `OFF = 2^252`, a group numerator is `S_j + k_{j-1} + 2^252`, in
/// `(0, 2^253) < Fr`; `cb = k + 2^88` is in `(0, 2^89)`. Both sides of every
/// row are below `Fr`, so the row is an integer equality. A malicious prover
/// cannot make the numerator negative: its `Fr` representative would exceed
/// `cb·2^164 < 2^253`.
fn grouped_columns(
    a: [Field; WIDE_LIMBS],
    b: [Field; WIDE_LIMBS],
    m: [Field; WIDE_LIMBS],
    q: [Field; WIDE_LIMBS],
    rhs_extra: [Field; WIDE_LIMBS],
) {
    let cols = 2 * WIDE_LIMBS - 1;
    let mut lhs = [Field::from(0u8); 2 * WIDE_LIMBS - 1];
    let mut rhs = [Field::from(0u8); 2 * WIDE_LIMBS - 1];
    let mut i = 0usize;
    while i < WIDE_LIMBS {
        let mut k = 0usize;
        while k < WIDE_LIMBS {
            lhs[i + k] = lhs[i + k] + a[i] * b[k];
            rhs[i + k] = rhs[i + k] + q[i] * m[k];
            k += 1;
        }
        i += 1;
    }
    let mut c = 0usize;
    while c < WIDE_LIMBS {
        rhs[c] = rhs[c] + rhs_extra[c];
        c += 1;
    }
    let two_b = pow2(WIDE_BITS);
    let group_mod = pow2(GROUP_BITS);
    let bias = pow2(GROUP_BIAS_BITS);
    let off = pow2(GROUP_OFF_BITS);
    let mut cb_prev = bias;
    let mut j = 0usize;
    while j + 1 < WIDE_LIMBS {
        let c0 = 2 * j;
        let c1 = 2 * j + 1;
        let s = (lhs[c0] - rhs[c0]) + two_b * (lhs[c1] - rhs[c1]);
        let num = s + cb_prev - bias + off;
        let dr = Field::hint_div_rem(num, group_mod);
        require_eq(num, group_mod * dr[0] + dr[1]);
        require_eq(dr[1], Field::from(0u8));
        range_derived::<GROUP_CARRY_BITS>(dr[0]);
        cb_prev = dr[0];
        j += 1;
    }
    // Top column: the last carry must be exactly zero.
    let top = lhs[cols - 1] - rhs[cols - 1];
    require_eq(top + cb_prev - bias, Field::from(0u8));
}

/// `a² mod m` with a lazy remainder: proves `a² = q m + r` and
/// `r < 2^2048`, not `r < m`. Congruent to `a² mod m`, which is all the chain
/// needs.
fn square_lazy(a: [Field; WIDE_LIMBS], m: [Field; WIDE_LIMBS]) -> [Field; WIDE_LIMBS] {
    let (q, r) = Field::hint_mulmod_divmod::<WIDE_LIMBS>(a, a, m, WIDE_BITS);
    range_check_q(q);
    range_check_r(r);
    grouped_columns(a, a, m, q, r);
    r
}

/// The terminal step: `a·b = q n + em`, with `em` a public affine vector (the
/// encoded message). The hint's remainder is only pinned to `em` (25 rows);
/// it is never range-checked, and there is no separate limb-by-limb equality
/// against a computed value.
fn fused_final(
    a: [Field; WIDE_LIMBS],
    b: [Field; WIDE_LIMBS],
    m: [Field; WIDE_LIMBS],
    em: [Field; WIDE_LIMBS],
) {
    let (q, r) = Field::hint_mulmod_divmod::<WIDE_LIMBS>(a, b, m, WIDE_BITS);
    range_check_q(q);
    // Pin the hint's remainder to the public target; the fused identity below
    // then proves the same equation without a remainder range check.
    let mut i = 0usize;
    while i < WIDE_LIMBS {
        require_eq(r[i], em[i]);
        i += 1;
    }
    grouped_columns(a, b, m, q, em);
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
/// `Private<U2048>` input reader range-checks every limb; [`Bignum::new_checked`]
/// does too). The circuit also enforces that `n` has exactly 2048 bits, that
/// `sig < n`, and that `sig^65537 mod n` equals the PKCS#1 v1.5 encoding of
/// `digest`. It does not validate the RSA key structure (oddness/semiprimality);
/// that is the caller's key allowlist.
pub fn verify_sha256(n: U2048, sig: U2048, digest: [Field; 32]) {
    verify_checked(n, sig, digest)
}

/// Verify an RSASSA-PKCS1-v1_5 / SHA-256 signature from the big-endian octet
/// strings used by the zkGolf RSA interface: 256-byte modulus, 256-byte
/// signature, 32-byte digest.
///
/// The bytes are pinned to bytes with `to_bits::<8>` and packed to the 25 x 82
/// internal limbs in the circuit, so the public input is the octet string
/// rather than a limb vector. The host passes the raw certificate integers and
/// the signature bytes; `sig` may be private.
pub fn verify_sha256_bytes(n: [Field; 256], sig: [Field; 256], digest: [Field; 32]) {
    let (n82, n_top_bit) = bytes_to_wide(n);
    let (sig82, _) = bytes_to_wide(sig);
    verify_wide(n82, sig82, n_top_bit * pow2(79), digest_bits(digest));
}

/// The shared 25 x 82-bit verifier. `n_top` is the modulus's top bit at weight
/// `2^79` (so a 2048-bit `n` makes it `2^79`).
fn verify_wide(n: [Field; WIDE_LIMBS], sig: [Field; WIDE_LIMBS], n_top: Field, bits: [Field; 256]) {
    // The top bit at weight 2^79 makes n exactly 2048 bits
    // (2^2047 <= n < 2^2048), the bound every product and `q` estimate uses.
    require_eq(n_top, pow2(79));

    // `sig < n` is the RFC 8017 validity condition. The lazy chain only needs
    // congruence, but a verifier must reject s >= n.
    let m_minus_1 = minus_one::<WIDE_LIMBS, WIDE_BITS>(n);
    require_lt::<WIDE_LIMBS, WIDE_BITS>(sig, m_minus_1);

    // 16 lazy squarings: acc = sig^(2^16) mod n (a representative in
    // [0, 2^2048), not necessarily canonical).
    let mut acc = sig;
    let mut i = 0usize;
    while i < 16usize {
        acc = square_lazy(acc, n);
        i += 1;
    }

    // Terminal fusion: acc * sig = q n + EM, with EM the public affine target.
    // Since acc = sig^(2^16) (mod n), this pins EM = sig^65537 (mod n); EM is
    // the PKCS#1 encoding, below 2^2033 < n, so it is the canonical residue.
    let em = sha256_em_bits_82(bits);
    fused_final(acc, sig, n, em);
}

fn verify_checked_bits(n: U2048, sig: U2048, bits: [Field; 256]) {
    let (n82, n_top) = convert_wide(n.limbs);
    let (sig82, _) = convert_wide(sig.limbs);
    verify_wide(n82, sig82, n_top, bits);
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
    //
    // The words are constrained boolean here. `xark-sha256` already returns
    // bits, but this is a public entry point: without the check a caller could
    // pass non-boolean fields, and the encoded message would no longer be the
    // bounded affine vector the modular identity's soundness proof assumes.
    let mut bits = [Field::from(0u8); 256];
    let mut j = 0usize;
    while j < 256usize {
        let b = digest[7 - j / 32][j % 32];
        b.require_bool();
        bits[j] = b;
        j += 1;
    }
    verify_checked_bits(n, sig, bits);
}

/// The gadget's public API alongside the xark prelude.
pub mod prelude {
    pub use crate::*;
    pub use xark::prelude::*;
}
