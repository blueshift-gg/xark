//! Host-side big-integer input values for non-native gadgets (secp256k1/r1,
//! ed25519, and any future `xark-bignum` circuit).
//!
//! A gadget's 256-bit field elements live in-circuit as **`LIMBS` little-endian
//! `BITS`-bit limbs** (secp/ed25519 use `3 × 86`). A prover has the value in some
//! *natural* form — the raw crypto bytes a signing library emits, a decimal, a
//! hex string, a small integer — and should never hand-decompose it into limbs.
//! [`Uint256`] is that value: it accepts every natural form and owns the one
//! canonical, unit-tested `→ limbs` decomposition, so the three EC vector tests
//! (and real proving inputs) share a single conversion instead of re-deriving the
//! mask/shift each time.
//!
//! ```ignore
//! use xark_test_harness::bignum::Uint256;
//! // bytes (what k256/p256/dalek emit) …
//! let r = Uint256::from_bytes_be(&sig.to_bytes()[..32]);
//! // … or a decimal / 0x-hex literal — same type, same limbs.
//! let e = Uint256::from("12345");
//! assert_eq!(r.limbs(3, 86).len(), 3); // limb0 + limb1·2^86 + limb2·2^172
//! ```

use num_bigint::BigUint;

/// An unsigned big integer (an EC coordinate or scalar) as a host input value.
///
/// Construct it from whichever form you have — raw big-endian bytes
/// ([`from_bytes_be`](Self::from_bytes_be) / `From<[u8; 32]>`), a decimal or
/// `0x`-hex string (`From<&str>`), or a small integer (`From<u128>`) — and read
/// back its circuit [`limbs`](Self::limbs). Bytes are the ergonomic form for
/// crypto inputs; decimal/hex for arithmetic ones.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Uint256(BigUint);

impl Uint256 {
    /// From big-endian bytes (any length ≤ 32 in practice; the SEC1 / RFC-8032
    /// wire form of a scalar or coordinate).
    pub fn from_bytes_be(bytes: &[u8]) -> Self {
        Uint256(BigUint::from_bytes_be(bytes))
    }

    /// From little-endian bytes (e.g. an ed25519 scalar `s`, which is LE on the wire).
    pub fn from_bytes_le(bytes: &[u8]) -> Self {
        Uint256(BigUint::from_bytes_le(bytes))
    }

    /// The value as `count` little-endian `bits`-bit limbs, each a decimal string —
    /// exactly the gadget's limb encoding (`value = Σ limb_i · 2^(i·bits)`). Panics
    /// only if the value does not fit in `count · bits` bits (a caller bug: the
    /// value is wider than the field element it claims to be).
    pub fn limbs(&self, count: usize, bits: u32) -> Vec<String> {
        let mask = (BigUint::from(1u8) << bits) - 1u8;
        let out: Vec<String> = (0..count)
            .map(|i| ((&self.0 >> (i as u32 * bits)) & &mask).to_string())
            .collect();
        // Round-trip guard: the limbs must recompose to the original value, i.e.
        // nothing was truncated above the top limb.
        debug_assert_eq!(
            &(&self.0 >> (count as u32 * bits)),
            &BigUint::from(0u8),
            "Uint256 does not fit in {count} × {bits}-bit limbs"
        );
        out
    }

    /// The underlying big integer (for reference computations in tests).
    pub fn as_biguint(&self) -> &BigUint {
        &self.0
    }
}

impl From<BigUint> for Uint256 {
    fn from(v: BigUint) -> Self {
        Uint256(v)
    }
}

impl From<[u8; 32]> for Uint256 {
    fn from(b: [u8; 32]) -> Self {
        Uint256::from_bytes_be(&b)
    }
}

impl From<u128> for Uint256 {
    fn from(v: u128) -> Self {
        Uint256(BigUint::from(v))
    }
}

/// Parse a decimal or `0x`-prefixed hex string. Panics on a malformed value —
/// these are test-authoring literals, so failing loudly is correct.
impl From<&str> for Uint256 {
    fn from(s: &str) -> Self {
        let t = s.trim();
        let parsed = if let Some(h) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
            BigUint::parse_bytes(h.as_bytes(), 16)
        } else {
            BigUint::parse_bytes(t.as_bytes(), 10)
        };
        Uint256(parsed.unwrap_or_else(|| panic!("invalid Uint256 literal {s:?}")))
    }
}

/// A scalar / coordinate host value — the readable name for a [`Uint256`] used as
/// an `Fq`/`Fp` circuit input (an ECDSA `r`/`s`/`e`, an EdDSA scalar, …).
pub type Scalar = Uint256;

/// An affine curve point as two host coordinate values — sugar for the two
/// [`Uint256`] halves of a public key or signature point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Point {
    pub x: Uint256,
    pub y: Uint256,
}

impl Point {
    /// From a SEC1 encoding: the 65-byte uncompressed form (`0x04 ‖ x ‖ y`) or a
    /// bare 64-byte `x ‖ y` (both big-endian). Panics on any other length.
    pub fn from_sec1(bytes: &[u8]) -> Self {
        let body = match bytes.len() {
            65 if bytes[0] == 0x04 => &bytes[1..],
            64 => bytes,
            n => panic!("Point::from_sec1: expected 64 or 65 (0x04-prefixed) bytes, got {n}"),
        };
        Point {
            x: Uint256::from_bytes_be(&body[..32]),
            y: Uint256::from_bytes_be(&body[32..]),
        }
    }
}

/// A host input value that knows how to fan itself out to the circuit's witness
/// **leaves** — the `(leaf-name, decimal)` pairs the compiler's structural flatten
/// produces for the parameter, so [`Compiled::check`](crate::Compiled::check) can
/// drive a compiled circuit from native values instead of hand-built limb maps.
///
/// The names here are the single source of truth for a type's flatten layout, and
/// `check` resolves them against the *actual* compiled program — a name that
/// doesn't exist is a loud error, never a silent skip.
pub trait LeafInput {
    /// The `(leaf-name, decimal-value)` pairs for this value under `prefix` (the
    /// parameter name), in any order (`check` matches by name).
    fn leaves(&self, prefix: &str) -> Vec<(String, String)>;
}

/// The gadget limb convention for 256-bit field elements: 3 little-endian 86-bit
/// limbs (shared by secp256k1/r1 and ed25519).
const LIMBS: usize = 3;
const BITS: u32 = 86;

/// A scalar/coordinate flattens as an `Fq`/`Fp` struct `{ limbs: [Field; 3] }` →
/// `prefix.limbs[0..3]`.
impl LeafInput for Uint256 {
    fn leaves(&self, prefix: &str) -> Vec<(String, String)> {
        self.limbs(LIMBS, BITS)
            .into_iter()
            .enumerate()
            .map(|(i, l)| (format!("{prefix}.limbs[{i}]"), l))
            .collect()
    }
}

/// A `Point { x: Fp, y: Fp }` flattens to `prefix.x.limbs[..]` then `prefix.y.limbs[..]`.
impl LeafInput for Point {
    fn leaves(&self, prefix: &str) -> Vec<(String, String)> {
        let mut out = self.x.leaves(&format!("{prefix}.x"));
        out.extend(self.y.leaves(&format!("{prefix}.y")));
        out
    }
}

/// An ECDSA signature `(r, s)` in the default 3×86 limb layout — `prefix.r.limbs[..]`
/// then `prefix.s.limbs[..]` (secp256r1's `Signature` compound; secp256k1's 2×128
/// one is [`SignaturePacked`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub r: Uint256,
    pub s: Uint256,
}

impl Signature {
    /// From a 64-byte big-endian `r ‖ s`.
    pub fn from_rs(bytes: &[u8]) -> Self {
        assert_eq!(bytes.len(), 64, "Signature::from_rs expects 64 bytes");
        Self {
            r: Uint256::from_bytes_be(&bytes[..32]),
            s: Uint256::from_bytes_be(&bytes[32..]),
        }
    }
}

impl LeafInput for Signature {
    fn leaves(&self, prefix: &str) -> Vec<(String, String)> {
        let mut out = self.r.leaves(&format!("{prefix}.r"));
        out.extend(self.s.leaves(&format!("{prefix}.s")));
        out
    }
}

/// An affine point whose coordinates flatten as **3×85-bit** limbs — the layout of
/// the lazy Ed25519 path's `PointL`, distinct from the default 3×86 [`Point`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Point85 {
    pub x: Uint256,
    pub y: Uint256,
}

impl LeafInput for Point85 {
    fn leaves(&self, prefix: &str) -> Vec<(String, String)> {
        let coord = |v: &Uint256, name: &str| -> Vec<(String, String)> {
            v.limbs(3, 85)
                .into_iter()
                .enumerate()
                .map(|(i, l)| (format!("{prefix}.{name}.limbs[{i}]"), l))
                .collect()
        };
        let mut out = coord(&self.x, "x");
        out.extend(coord(&self.y, "y"));
        out
    }
}

/// The secp curves' ECDSA path packs each 256-bit value into **2×128-bit** halves
/// (`[lo128, hi128]` — 10 public leaves instead of the default 3×86's 15), matching
/// `xark_secp256k1::Scalar` / `xark_secp256r1::Scalar`. A distinct type, like
/// [`Point85`], so a value's leaf layout stays the single source of truth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarPacked(pub Uint256);

impl ScalarPacked {
    /// From a big-endian byte string (e.g. a signature scalar off the k256 wire).
    pub fn from_bytes_be(bytes: &[u8]) -> Self {
        Self(Uint256::from_bytes_be(bytes))
    }
}

impl LeafInput for ScalarPacked {
    fn leaves(&self, prefix: &str) -> Vec<(String, String)> {
        self.0
            .limbs(2, 128)
            .into_iter()
            .enumerate()
            .map(|(i, l)| (format!("{prefix}.limbs[{i}]"), l))
            .collect()
    }
}

/// An affine point whose coordinates flatten as **2×128-bit** limbs — the layout of
/// the secp256k1 GLV path's `Point`, distinct from the default 3×86 [`Point`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PointPacked {
    pub x: Uint256,
    pub y: Uint256,
}

/// An ECDSA signature `(r, s)` flattening as **2×128-bit** limbs under
/// `<prefix>.r.limbs[i]` / `<prefix>.s.limbs[i]` — secp256k1's `Signature` compound.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignaturePacked {
    pub r: Uint256,
    pub s: Uint256,
}

impl SignaturePacked {
    /// From a 64-byte big-endian `r ‖ s` (the form `k256`'s `Signature::to_bytes`
    /// produces). Panics on any other length.
    pub fn from_rs(bytes: &[u8]) -> Self {
        assert_eq!(bytes.len(), 64, "SignaturePacked::from_rs expects 64 bytes");
        Self {
            r: Uint256::from_bytes_be(&bytes[..32]),
            s: Uint256::from_bytes_be(&bytes[32..]),
        }
    }
}

impl LeafInput for SignaturePacked {
    fn leaves(&self, prefix: &str) -> Vec<(String, String)> {
        let field = |v: &Uint256, name: &str| -> Vec<(String, String)> {
            v.limbs(2, 128)
                .into_iter()
                .enumerate()
                .map(|(i, l)| (format!("{prefix}.{name}.limbs[{i}]"), l))
                .collect()
        };
        let mut out = field(&self.r, "r");
        out.extend(field(&self.s, "s"));
        out
    }
}

impl PointPacked {
    /// From a SEC1 encoding: 65-byte uncompressed (`0x04 ‖ x ‖ y`) or bare 64-byte
    /// `x ‖ y` (both big-endian). Panics on any other length.
    pub fn from_sec1(bytes: &[u8]) -> Self {
        let body = match bytes.len() {
            65 if bytes[0] == 0x04 => &bytes[1..],
            64 => bytes,
            n => panic!("PointPacked::from_sec1: expected 64 or 65 (0x04-prefixed) bytes, got {n}"),
        };
        Self {
            x: Uint256::from_bytes_be(&body[..32]),
            y: Uint256::from_bytes_be(&body[32..]),
        }
    }
}

impl LeafInput for PointPacked {
    fn leaves(&self, prefix: &str) -> Vec<(String, String)> {
        let coord = |v: &Uint256, name: &str| -> Vec<(String, String)> {
            v.limbs(2, 128)
                .into_iter()
                .enumerate()
                .map(|(i, l)| (format!("{prefix}.{name}.limbs[{i}]"), l))
                .collect()
        };
        let mut out = coord(&self.x, "x");
        out.extend(coord(&self.y, "y"));
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn limbs_recompose() {
        // A known 256-bit value, decomposed to 3×86-bit limbs, must recompose.
        let v = Uint256::from("0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
        let limbs = v.limbs(3, 86);
        let recomposed: BigUint = limbs
            .iter()
            .enumerate()
            .map(|(i, l)| l.parse::<BigUint>().unwrap() << (i as u32 * 86))
            .sum();
        assert_eq!(&recomposed, v.as_biguint());
        // Each limb is < 2^86.
        for l in &limbs {
            assert!(l.parse::<BigUint>().unwrap() < (BigUint::from(1u8) << 86u32));
        }
    }

    #[test]
    fn forms_agree() {
        // bytes-BE, decimal, hex, and u128 all reach the same value + limbs.
        let n = 0x1234_5678_9abc_u128;
        let a = Uint256::from(n);
        let b = Uint256::from("20015998343868");
        let c = Uint256::from("0x123456789abc");
        let mut be = [0u8; 32];
        be[26..].copy_from_slice(&n.to_be_bytes()[10..]);
        let d = Uint256::from(be);
        assert_eq!(a, b);
        assert_eq!(a, c);
        assert_eq!(a, d);
        assert_eq!(a.limbs(3, 86), b.limbs(3, 86));
    }

    #[test]
    fn point_sec1_prefixed_and_bare_agree() {
        let mut body = [0u8; 64];
        body[31] = 7; // x = 7
        body[63] = 9; // y = 9
        let mut sec1 = [0u8; 65];
        sec1[0] = 0x04;
        sec1[1..].copy_from_slice(&body);
        let p = Point::from_sec1(&sec1);
        let q = Point::from_sec1(&body);
        assert_eq!(p, q);
        assert_eq!(p.x, Uint256::from(7u128));
        assert_eq!(p.y, Uint256::from(9u128));
    }
}
