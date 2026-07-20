//! `xark-ed25519`: an Ed25519 (twisted-Edwards, `a = −1`) scalar-multiplication
//! and EdDSA signature-verification gadget, over the `xark` `Field` subset.
//!
//! Ed25519 lives over the base field `p = 2^255 − 19` with the curve equation
//! `−x² + y² = 1 + d·x²·y²` and group order `L`. Its ~255-bit coordinates are
//! foreign to the native BN254 proving field, so they use the shared 3 × 86-bit
//! non-native limb arithmetic in [`xark_bignum`]. The whole group law, scalar-mul, and
//! constants are emitted by the shared [`xark_curve::edwards!`] macro — the
//! addition is **complete** (no exceptional cases), so unlike the secp256k1 ECDSA
//! gadget there is no offset accumulator.
//!
//! This crate adds the fixed base point `B` and the EdDSA verification equation
//! `[S]·B == R + [k]·A` (the algebraic core of Ed25519 verification; the SHA-512
//! challenge hash `k = H(R‖A‖M)` is out of scope — `k` is supplied as a witness).

#![no_std]
// Circuit-lowered gadget code: the xark compiler rejects compound assignment on
// `Field` (`+=`/`-=`/`*=`), so `x = x + y` is required — not a clippy oversight.
#![allow(clippy::assign_op_pattern)]

use xark::{assert_eq, Field, Transparent};

// The Ed25519 curve: base field p = 2^255 − 19, scalar order L, constant d.
xark_curve::edwards! {
    base   = "57896044618658097711785492504343953926634992332820282019728792003956564819949",
    scalar = "7237005577332262213973186563042994240857116359379907606001950938285454250989",
    d      = "37095705934669439343138083508754565189542113879843219016388785533085940283555",
}

/// The Ed25519 base point `B` (its two coordinates as compile-time 86-bit limbs).
///   Bx = 15112221349535400772501151409588531511454012693041857206046113283949847762202
///   By = 46316835694926478169428394003475163141307993866256225615783033603165251855960
pub fn base() -> Point {
    Point::new(
        fp(
            45522188556658772877366554,
            10615720421966981067801172,
            2524463244633754693274190,
        ),
        fp(
            46422751473201760308717144,
            30948500982134506872478105,
            7737125245533626718119526,
        ),
    )
}

/// Fixed-base scalar multiplication `[k]·B`, where `k_bits` is the 256-bit
/// little-endian decomposition of the scalar (see [`xark_bignum::scalar_to_bits`]).
pub fn mul_base(k_bits: [Field; 256]) -> Point {
    scalar_mul(k_bits, base())
}

/// Assert `Σ bits[i]·2^i < L` (the ed25519 group order): recompose the bits into
/// the scalar field's `3 × 86`-bit limbs and assert canonical. `bits` must be
/// caller-constrained boolean.
fn assert_scalar_below_order(bits: [Field; 256]) {
    let mut limbs = [Field::from(0u8); 3];
    let mut idx = 0usize;
    let mut l = 0usize;
    while l < 3usize {
        let width = if l == 2 { 84usize } else { 86usize };
        let mut acc = Field::from(0u8);
        let mut pow = Field::from(1u8);
        let mut j = 0usize;
        while j < width {
            acc = acc + bits[idx] * pow;
            pow = pow + pow;
            idx += 1;
            j += 1;
        }
        limbs[l] = acc;
        l += 1;
    }
    Fq::new(limbs).assert_canonical();
}

// ===========================================================================
// SOUND LAZY extended-coordinate path (3×85 pseudo-Mersenne, boundary-only
// reduction). Alongside the affine macro gadget above. Point = [X,Y,Z,T].
// ===========================================================================
use xark_bignum::{
    ext_add_25519 as eadd, ext_double_25519 as edbl, finalize_25519 as fin, modulus_limbs,
    mul_lazy_25519 as mul, range_check_limbs, weak_reduce_25519 as wr, D_25519, P_25519_L as PL,
};

type L3 = [Field; 3];
type Ext = [L3; 4];

// A base-field element in the lazy path's 3×85-bit limb layout (distinct from the
// affine gadget's `Fp` at 3×86). Only used as the input-flatten wrapper so the
// `ed25519_verify` example can take aggregate `Point` coordinates.
xark_bignum::fp!(
    pub FpL,
    "57896044618658097711785492504343953926634992332820282019728792003956564819949",
    3,
    85
);
/// An Ed25519 affine point with 3×85-bit coordinates — the lazy path's public
/// input type (`x`/`y` each flatten to `<name>.x.limbs[0..2]` / `<name>.y.limbs`).
#[derive(Clone, Copy)]
pub struct PointL {
    pub x: FpL,
    pub y: FpL,
}

const BX85: L3 = modulus_limbs::<3, 85>(
    "15112221349535400772501151409588531511454012693041857206046113283949847762202",
);
const BY85: L3 = modulus_limbs::<3, 85>(
    "46316835694926478169428394003475163141307993866256225615783033603165251855960",
);

fn f0() -> Field {
    Field::from(0u8)
}
fn one3() -> L3 {
    [Field::from(1u8), f0(), f0()]
}
fn id_e() -> Ext {
    [[f0(); 3], one3(), one3(), [f0(); 3]]
}

fn to_ext(x: L3, y: L3) -> Ext {
    [x, y, one3(), mul(x, y)]
}
fn dbl_e(p: Ext) -> Ext {
    let (a, b, c, d) = edbl(p[0], p[1], p[2]);
    [a, b, c, d]
}
fn add_e(p: Ext, q: Ext) -> Ext {
    let (a, b, c, d) = eadd(p[0], p[1], p[2], p[3], q[0], q[1], q[2], q[3]);
    [a, b, c, d]
}

fn mux3(s: Field, a: L3, b: L3) -> L3 {
    [
        b[0] + s * (a[0] - b[0]),
        b[1] + s * (a[1] - b[1]),
        b[2] + s * (a[2] - b[2]),
    ]
}
fn mux_e(s: Field, a: Ext, b: Ext) -> Ext {
    [
        mux3(s, a[0], b[0]),
        mux3(s, a[1], b[1]),
        mux3(s, a[2], b[2]),
        mux3(s, a[3], b[3]),
    ]
}
fn select16_e(t: [Ext; 16], b3: Field, b2: Field, b1: Field, b0: Field) -> Ext {
    let mut l1 = [id_e(); 8];
    let mut j = 0usize;
    while j < 8usize {
        l1[j] = mux_e(b0, t[2 * j + 1], t[2 * j]);
        j += 1;
    }
    let mut l2 = [id_e(); 4];
    let mut j = 0usize;
    while j < 4usize {
        l2[j] = mux_e(b1, l1[2 * j + 1], l1[2 * j]);
        j += 1;
    }
    let mut l3 = [id_e(); 2];
    let mut j = 0usize;
    while j < 2usize {
        l3[j] = mux_e(b2, l2[2 * j + 1], l2[2 * j]);
        j += 1;
    }
    mux_e(b3, l3[1], l3[0])
}

/// Sound on-curve check for an affine (x,y): range-check limbs, then
/// −x²+y² == 1 + d·x²·y² (mod p), compared canonically.
fn on_curve_l(x: L3, y: L3) {
    range_check_limbs::<3, 85>(x);
    range_check_limbs::<3, 85>(y);
    let x2 = mul(x, x);
    let y2 = mul(y, y);
    let b8 = [
        Field::from(8u8) * PL[0],
        Field::from(8u8) * PL[1],
        Field::from(8u8) * PL[2],
    ];
    let lhs = wr([
        b8[0] + y2[0] - x2[0],
        b8[1] + y2[1] - x2[1],
        b8[2] + y2[2] - x2[2],
    ]);
    let x2y2 = mul(x2, y2);
    let dxy = mul(D_25519, x2y2);
    let rhs = [one3()[0] + dxy[0], dxy[1], dxy[2]];
    let lf = fin(lhs);
    let rf = fin(rhs);
    let mut i = 0usize;
    while i < 3usize {
        assert_eq(lf[i], rf[i]);
        i += 1;
    }
}

fn eq_mod_p(u: L3, v: L3) {
    let a = fin(u);
    let b = fin(v);
    let mut i = 0usize;
    while i < 3usize {
        assert_eq(a[i], b[i]);
        i += 1;
    }
}

/// Windowed Strauss–Shamir `[k1]P1 + [k2]P2` in extended coords (2+2-bit windows).
fn dsm_l(bits1: [Field; 256], p1: Ext, bits2: [Field; 256], p2: Ext) -> Ext {
    let d1 = dbl_e(p1);
    let jp1 = [p1, d1, add_e(d1, p1)];
    let d2 = dbl_e(p2);
    let jp2 = [p2, d2, add_e(d2, p2)];
    let mut table = [id_e(); 16];
    let mut i = 0usize;
    while i < 4usize {
        let mut j = 0usize;
        while j < 4usize {
            table[i * 4 + j] = if i == 0 {
                if j == 0 {
                    id_e()
                } else {
                    jp2[j - 1]
                }
            } else if j == 0 {
                jp1[i - 1]
            } else {
                add_e(jp1[i - 1], jp2[j - 1])
            };
            j += 1;
        }
        i += 1;
    }
    let mut acc = id_e();
    let mut win = 0usize;
    while win < 128usize {
        acc = dbl_e(dbl_e(acc));
        let top = 255 - win * 2;
        let sel = select16_e(
            table,
            bits1[top],
            bits1[top - 1],
            bits2[top],
            bits2[top - 1],
        );
        acc = add_e(acc, sel);
        win += 1;
    }
    acc
}

/// Ed25519 signature verification `[S]·B == R + [k]·A` — the sound lazy
/// extended-coordinate gadget (3×85 limbs, ~2.40M constraints), ed25519's single
/// `eddsa_verify` (the affine variant was ~4.55M). Point coords are raw 3×85
/// limbs; scalars are 256 caller-decomposed bits.
#[allow(clippy::too_many_arguments)]
/// An Ed25519 signature `(R, S)` — a curve point `R` (compressed `[u8; 32]` on the
/// host) and a scalar `S`. Its `#[derive(Transparent)]` host `NativeInput` composes
/// `PointL`'s (decompressing) leaves with `Scalar`'s, so the host native form is
/// `[u8; 64]` = compressed `R ‖ big-endian S`. Pass it to [`PointL::verify`].
#[derive(Clone, Copy, Transparent)]
pub struct Signature {
    pub r: PointL,
    pub s: Scalar,
}

/// Everything to write an Ed25519 circuit in one import:
/// `use xark_ed25519::prelude::*;` re-exports the `xark` essentials (`circuit`,
/// `Public`, `Field`, `assert_eq`, …) plus the transparent input types [`PointL`],
/// [`Signature`], [`Scalar`]. Verify with `pubkey.verify(sig, digest)`.
pub mod prelude {
    pub use crate::{PointL, Scalar, Signature};
    pub use xark::prelude::*;
}

impl PointL {
    /// Verify an Ed25519 signature against this public key `A` and the challenge
    /// `digest = k = H(R ‖ A ‖ M) mod L` (a [`Scalar`]). Checks the EdDSA equation
    /// `[S]·B == R + [k]·A`. The transparent-type entry point — no limbs:
    ///
    /// ```ignore
    /// #[circuit]
    /// fn ed25519(pubkey: Public<PointL>, sig: Public<Signature>, digest: Public<Scalar>) {
    ///     pubkey.verify(sig, digest);
    /// }
    /// ```
    pub fn verify(self, sig: Signature, digest: Scalar) {
        eddsa_verify(
            self.x.limbs,
            self.y.limbs,
            sig.r.x.limbs,
            sig.r.y.limbs,
            xark_bignum::scalar_to_bits(sig.s.limbs),
            xark_bignum::scalar_to_bits(digest.limbs),
        );
    }
}

/// Ed25519 signature verification core: the EdDSA equation `[S]·B == R + [k]·A`
/// (sound lazy extended-coordinate path, 3×85 limbs). Wrapped by [`PointL::verify`]
/// — callers use that (it takes the transparent [`Signature`] and decomposes the
/// scalars to bits).
pub fn eddsa_verify(ax: L3, ay: L3, rx: L3, ry: L3, s_bits: [Field; 256], k_bits: [Field; 256]) {
    // canonical scalar S < L (else S, S+L, … all verify — EdDSA malleability)
    assert_scalar_below_order(s_bits);
    on_curve_l(ax, ay);
    on_curve_l(rx, ry);
    // −A = (−x, y); base B and −A to extended.
    let neg_ax = wr([
        Field::from(8u8) * PL[0] - ax[0],
        Field::from(8u8) * PL[1] - ax[1],
        Field::from(8u8) * PL[2] - ax[2],
    ]);
    let base_e = to_ext(BX85, BY85);
    let nega_e = to_ext(neg_ax, ay);
    let t = dsm_l(s_bits, base_e, k_bits, nega_e);
    let r_e = to_ext(rx, ry);
    // cofactored: [8]t == [8]R, compared projectively (no inverse).
    let t8 = dbl_e(dbl_e(dbl_e(t)));
    let r8 = dbl_e(dbl_e(dbl_e(r_e)));
    eq_mod_p(mul(t8[0], r8[2]), mul(r8[0], t8[2]));
    eq_mod_p(mul(t8[1], r8[2]), mul(r8[1], t8[2]));
}

/// Host-side `NativeInput` + EdDSA helpers, behind the `host` feature. Ed25519
/// points are natively **compressed** (32-byte little-endian `y` + `x`-sign bit);
/// these recover the affine `(x, y)` per RFC 8032 §5.1.3 so the circuit's
/// transparent types take the exact bytes `ed25519-dalek` emits. Signatures use
/// **little-endian** scalars, so `S`/`k` are byte-reversed to the big-endian form
/// the macro-generated `Fq` `NativeInput` expects.
#[cfg(not(xark))]
mod host {
    extern crate std;
    use super::PointL;
    use num_bigint::BigUint;
    use sha2::{Digest, Sha512};
    use std::{format, string::String, string::ToString, vec::Vec};

    fn dec(s: &str) -> BigUint {
        BigUint::parse_bytes(s.as_bytes(), 10).unwrap()
    }
    // p = 2²⁵⁵−19 ; d = −121665/121666 ; L = group order ; √−1 = 2^((p−1)/4).
    fn p() -> BigUint {
        dec("57896044618658097711785492504343953926634992332820282019728792003956564819949")
    }
    fn d() -> BigUint {
        dec("37095705934669439343138083508754565189542113879843219016388785533085940283555")
    }
    fn order() -> BigUint {
        dec("7237005577332262213973186563042994240857116359379907606001950938285454250989")
    }
    fn sqrt_m1() -> BigUint {
        dec("19681161376707505956807079304988542015446066515923890162744021073123829784752")
    }

    /// Big-endian 32-byte encoding of a scalar/coordinate.
    fn be32(v: &BigUint) -> [u8; 32] {
        let b = v.to_bytes_be();
        let mut out = [0u8; 32];
        out[32 - b.len()..].copy_from_slice(&b);
        out
    }

    /// Decompress an Ed25519 point (32-byte compressed) to affine `(x, y)`.
    fn decompress(comp: &[u8; 32]) -> (BigUint, BigUint) {
        let p = p();
        let mut yb = *comp;
        let sign = (yb[31] >> 7) & 1;
        yb[31] &= 0x7f;
        let y = BigUint::from_bytes_le(&yb) % &p;
        let y2 = (&y * &y) % &p;
        let u = (&y2 + &p - 1u32) % &p; // y² − 1
        let v = (&d() * &y2 + 1u32) % &p; // d·y² + 1
                                          // x = (u/v)^((p+3)/8) via x = u·v³·(u·v⁷)^((p−5)/8)
        let v3 = v.modpow(&BigUint::from(3u32), &p);
        let v7 = v.modpow(&BigUint::from(7u32), &p);
        let pw = ((&u * &v7) % &p).modpow(&((&p - 5u32) / 8u32), &p);
        let mut x = (((&u * &v3) % &p) * pw) % &p;
        if (&v * (&x * &x % &p)) % &p != u {
            x = (x * sqrt_m1()) % &p; // v·x² == −u → multiply by √−1
        }
        if (x.bit(0) as u8) != sign {
            x = (&p - &x) % &p;
        }
        (x, y)
    }

    /// Little-endian 3 × 85-bit limbs of a value, named `<prefix>.limbs[i]`.
    fn limbs85(v: &BigUint, prefix: &str) -> Vec<(String, String)> {
        let mask = (BigUint::from(1u8) << 85u32) - 1u8;
        (0..3)
            .map(|i| {
                (
                    format!("{prefix}.limbs[{i}]"),
                    ((v >> (i as u32 * 85)) & &mask).to_string(),
                )
            })
            .collect()
    }

    impl xark_prover::NativeInput for PointL {
        /// Ed25519 compressed point (`y` little-endian + `x`-sign bit).
        type Native = [u8; 32];
        fn leaves(native: &[u8; 32], prefix: &str) -> Vec<(String, String)> {
            let (x, y) = decompress(native);
            let mut out = limbs85(&x, &format!("{prefix}.x"));
            out.extend(limbs85(&y, &format!("{prefix}.y")));
            out
        }
    }

    /// Decompress a compressed point to the compact uncompressed `[u8; 64]`
    /// (`x ‖ y` big-endian) form the macro-generated 3×86-bit `Point` takes.
    pub fn point_be(comp: &[u8; 32]) -> [u8; 64] {
        let (x, y) = decompress(comp);
        let mut out = [0u8; 64];
        out[..32].copy_from_slice(&be32(&x));
        out[32..].copy_from_slice(&be32(&y));
        out
    }

    /// The EdDSA challenge `k = SHA-512(R ‖ A ‖ M) mod L`, big-endian (for `Fq`).
    pub fn challenge(r: &[u8; 32], a: &[u8; 32], msg: &[u8]) -> [u8; 32] {
        let mut h = Sha512::new();
        h.update(r);
        h.update(a);
        h.update(msg);
        let k = BigUint::from_bytes_le(&h.finalize()) % order();
        be32(&k)
    }

    /// Reverse a little-endian signature scalar `S` to the big-endian form `Fq` takes.
    pub fn scalar_le_to_be(le: &[u8; 32]) -> [u8; 32] {
        let mut b = *le;
        b.reverse();
        b
    }

    // --- affine twisted-Edwards arithmetic (host, for `ed25519_smul` vectors) ---

    fn inv(a: &BigUint, p: &BigUint) -> BigUint {
        a.modpow(&(p - 2u32), p) // p prime → a⁻¹ = a^(p−2)
    }

    /// Complete affine addition on Ed25519 (`a = −1`), mod `p`.
    fn ed_add(pt1: &(BigUint, BigUint), pt2: &(BigUint, BigUint)) -> (BigUint, BigUint) {
        let p = p();
        let (x1, y1) = pt1;
        let (x2, y2) = pt2;
        let x1x2 = (x1 * x2) % &p;
        let y1y2 = (y1 * y2) % &p;
        let dt = (&d() * &x1x2 % &p * &y1y2) % &p; // d·x1x2·y1y2
        let xnum = (x1 * y2 + y1 * x2) % &p;
        let ynum = (&y1y2 + &x1x2) % &p;
        let xden = (1u32 + &dt) % &p;
        let yden = (&p + 1u32 - &dt) % &p; // 1 − dt
        ((xnum * inv(&xden, &p)) % &p, (ynum * inv(&yden, &p)) % &p)
    }

    /// `[k]·B` on the Ed25519 basepoint, returned compact `x ‖ y` big-endian.
    pub fn base_mul_be(k_be: &[u8; 32]) -> [u8; 64] {
        let base = (
            dec("15112221349535400772501151409588531511454012693041857206046113283949847762202"),
            dec("46316835694926478169428394003475163141307993866256225615783033603165251855960"),
        );
        let mut acc = (BigUint::from(0u32), BigUint::from(1u32)); // identity (0, 1)
        let mut addend = base;
        let mut k = BigUint::from_bytes_be(k_be);
        while k > BigUint::from(0u32) {
            if k.bit(0) {
                acc = ed_add(&acc, &addend);
            }
            addend = ed_add(&addend, &addend);
            k >>= 1;
        }
        let mut out = [0u8; 64];
        out[..32].copy_from_slice(&be32(&acc.0));
        out[32..].copy_from_slice(&be32(&acc.1));
        out
    }

    /// The Ed25519 basepoint `B` as compact `x ‖ y` big-endian.
    pub fn base_be() -> [u8; 64] {
        let one = {
            let mut b = [0u8; 32];
            b[31] = 1;
            b
        };
        base_mul_be(&one)
    }
}

#[cfg(not(xark))]
pub use host::{base_be, base_mul_be, challenge, point_be, scalar_le_to_be};
