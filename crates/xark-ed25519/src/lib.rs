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

use xark::{assert_eq, Field};

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

/// Verify the Ed25519 signature equation `[S]·B == R + [k]·A`.
///
/// `a_pub` is the public key `A`, `r_sig` the signature's `R` point, `s_bits` the
/// 256-bit decomposition of the signature scalar `S`, and `k_bits` the 256-bit
/// decomposition of the challenge `k = H(R‖A‖M)` (supplied as a witness — the
/// hash itself is not constrained here). Fails (unsatisfiable) if the equation
/// does not hold.
pub fn eddsa_verify(a_pub: Point, r_sig: Point, s_bits: [Field; 256], k_bits: [Field; 256]) {
    // pin A and R to the curve (range-checks limbs) before the group law
    enforce_on_curve(a_pub);
    enforce_on_curve(r_sig);

    // canonical scalar `S < L`, else S, S+L, S+2L, … all verify (EdDSA malleability)
    assert_scalar_below_order(s_bits);

    // Rewrite `[S]·B == R + [k]·A` as `[S]·B + [k]·(−A) == R`, so the two scalar
    // multiplications share one windowed Strauss–Shamir pass. Twisted-Edwards
    // negation is `(−x, y)`.
    let neg_a = Point::new(fp(0, 0, 0) - a_pub.x, a_pub.y);
    let t = double_scalar_mul(s_bits, base(), k_bits, neg_a);

    // cofactored verification: assert `[8]·t == [8]·R` (×8 clears any small-order
    // component of A/R — the RFC 8032 cofactored equation)
    let t8 = t.double().double().double();
    let r8 = r_sig.double().double().double();
    let mut i = 0usize;
    while i < 3usize {
        assert_eq(t8.x.limbs[i], r8.x.limbs[i]);
        assert_eq(t8.y.limbs[i], r8.y.limbs[i]);
        i += 1;
    }
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

/// SOUND lazy Ed25519 verification `[S]·B == R + [k]·A`, extended coords.
/// Point coords are raw 3×85 limbs; scalars are 256 caller-decomposed bits.
#[allow(clippy::too_many_arguments)]
pub fn eddsa_verify_lazy(
    ax: L3,
    ay: L3,
    rx: L3,
    ry: L3,
    s_bits: [Field; 256],
    k_bits: [Field; 256],
) {
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
