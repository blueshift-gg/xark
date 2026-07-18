//! `xark-secp256k1`: secp256k1 ECDSA gadget over the `xark` `Field` subset.
//!
//! secp256k1 is `y² = x³ + 7` (short Weierstrass with **a = 0**, j-invariant 0)
//! over the base field `p = 2^256 - 2^32 - 977`, group order `n`. 256-bit field
//! elements are 3 little-endian 86-bit limbs (86 is the multiply-optimal size
//! over BN254); the non-native field arithmetic lives in [`xark_bignum`] (shared
//! with secp256r1, parameterized by modulus). This crate supplies the curve
//! constants and the incomplete-affine group law — with `a = 0` the doubling
//! slope is just `3x²/2y` (no `a` term).
//!
//! The whole gadget (`Fp`/`Fq`, `Point`, `ec_add_incomplete`,
//! `ec_double_incomplete`, `double_scalar_mul_incomplete`, `ecdsa_verify`) is
//! emitted by the shared [`xark_curve::weierstrass!`] macro — this
//! file is just the curve's constants. secp256r1 differs only in its moduli,
//! `a = -3`, and these tables.
//!
//! Every arithmetic building block is individually solver-validated; see the
//! `xark` compiler snapshot tests. `ecdsa_verify` composes them (structural
//! capstone; not solved end-to-end due to size).

#![no_std]

xark_curve::weierstrass! {
    base = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
    scalar = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
    a = 0,
    b = [7, 0, 0],
    generators = [
        [17117865558768631194064792, 12501176021340589225372855, 9198697782662356105779718, 6441780312434748884571320, 57953919405111227542741658, 5457536640262350763842127],
        [57105948487393027623526117, 2088890992725950981549619, 14961784698075395646489684, 46925586441427271765976362, 19820246243853867596485833, 2031033786214458435714136],
        [57545291876987742944507641, 75066192660561802595210765, 18828234277447069677687620, 2583640362791394057184882, 38197615293098406611150035, 4273588397735691711217203],
        [39240586505594730384248083, 43607737248441145767116859, 17270833250143069575414244, 74945151656403808399104290, 9851937081784665158242046, 6190313694369289866667054],
    ],
    correction = [50013525532261609533771622, 33977132216705809345294891, 6434814454533600219945686, 34870826494395841319973943, 37401083326380650972982394, 14538710286819613138477839],
}

// ===========================================================================
// SOUND LAZY ECDSA verify (4×64 lazy-affine point arithmetic + eager 4×64
// scalar ops). Alongside the macro's eager 3×86 gadget. ~30% fewer constraints.
// ===========================================================================
use xark::{assert_eq as aeq, Field};
use xark_bignum::{
    assert_lt, assert_nonzero_limbs, ec_add_k1, ec_double_k1, finalize_k1, mod_inverse, mod_mul,
    modulus_limbs, modulus_minus_1, mul_lazy_k1, on_curve_k1, range_check_limbs, reduce_once,
    scalar_to_bits_256, weak_reduce_k1, M_K1,
};

type L4 = [Field; 4];
type Pt = [L4; 2];

const NN: L4 =
    modulus_limbs::<4, 64>("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");
const NN1: L4 =
    modulus_minus_1::<4, 64>("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");

const G0X: L4 = modulus_limbs::<4, 64>(
    "55066263022277343669578718895168534326250603453777594175500187360389116729240",
);
const G0Y: L4 = modulus_limbs::<4, 64>(
    "32670510020758816978083085130507043184471273380659243275938904335757337482424",
);
const G1X: L4 = modulus_limbs::<4, 64>(
    "89565891926547004231252920425935692360644145829622209833684329913297188986597",
);
const G1Y: L4 = modulus_limbs::<4, 64>(
    "12158399299693830322967808612713398636155367887041628176798871954788371653930",
);
const G2X: L4 = modulus_limbs::<4, 64>(
    "112711660439710606056748659173929673102114977341539408544630613555209775888121",
);
const G2Y: L4 = modulus_limbs::<4, 64>(
    "25583027980570883691656905877401976406448868254816295069919888960541586679410",
);
const G3X: L4 = modulus_limbs::<4, 64>(
    "103388573995635080359749164254216598308788835304023601477803095234286494993683",
);
const G3Y: L4 = modulus_limbs::<4, 64>(
    "37057141145242123013015316630864329550140216928701153669873286428255828810018",
);
const CX: L4 = modulus_limbs::<4, 64>(
    "38520798663562926792944031864649027925169018349022333225915301796724429459302",
);
const CY: L4 = modulus_limbs::<4, 64>(
    "87033237048797207701170633904307172638944778279500768066120558132238250062903",
);

fn gen0() -> Pt {
    [weak_reduce_k1(G0X), weak_reduce_k1(G0Y)]
}
fn muxc(s: Field, a: L4, b: L4) -> L4 {
    [
        b[0] + s * (a[0] - b[0]),
        b[1] + s * (a[1] - b[1]),
        b[2] + s * (a[2] - b[2]),
        b[3] + s * (a[3] - b[3]),
    ]
}
fn muxp(s: Field, a: Pt, b: Pt) -> Pt {
    [muxc(s, a[0], b[0]), muxc(s, a[1], b[1])]
}
fn select16_k1(t: [Pt; 16], b3: Field, b2: Field, b1: Field, b0: Field) -> Pt {
    let z: Pt = [[Field::from(0u8); 4]; 2];
    let mut l1 = [z; 8];
    let mut j = 0usize;
    while j < 8usize {
        l1[j] = muxp(b0, t[2 * j + 1], t[2 * j]);
        j += 1;
    }
    let mut l2 = [z; 4];
    let mut j = 0usize;
    while j < 4usize {
        l2[j] = muxp(b1, l1[2 * j + 1], l1[2 * j]);
        j += 1;
    }
    let mut l3 = [z; 2];
    let mut j = 0usize;
    while j < 2usize {
        l3[j] = muxp(b2, l2[2 * j + 1], l2[2 * j]);
        j += 1;
    }
    muxp(b3, l3[1], l3[0])
}

/// Strauss–Shamir `u1·G + u2·Q` with the offset-accumulator (incomplete-add safe),
/// all lazy 4×64. Returns the resulting affine point.
fn dsm_lazy_k1(u1b: [Field; 256], u2b: [Field; 256], qx: L4, qy: L4) -> Pt {
    on_curve_k1(qx, qy);
    let (q2x, q2y) = ec_double_k1(qx, qy);
    let (q3x, q3y) = ec_add_k1(q2x, q2y, qx, qy);
    let z: Pt = [[Field::from(0u8); 4]; 2];
    let mut table = [z; 16];
    table[0] = [weak_reduce_k1(G0X), weak_reduce_k1(G0Y)];
    let (a1, b1) = ec_add_k1(G0X, G0Y, qx, qy);
    table[1] = [a1, b1];
    let (a2, b2) = ec_add_k1(G0X, G0Y, q2x, q2y);
    table[2] = [a2, b2];
    let (a3, b3) = ec_add_k1(G0X, G0Y, q3x, q3y);
    table[3] = [a3, b3];
    table[4] = [weak_reduce_k1(G1X), weak_reduce_k1(G1Y)];
    let (a5, b5) = ec_add_k1(G1X, G1Y, qx, qy);
    table[5] = [a5, b5];
    let (a6, b6) = ec_add_k1(G1X, G1Y, q2x, q2y);
    table[6] = [a6, b6];
    let (a7, b7) = ec_add_k1(G1X, G1Y, q3x, q3y);
    table[7] = [a7, b7];
    table[8] = [weak_reduce_k1(G2X), weak_reduce_k1(G2Y)];
    let (a9, b9) = ec_add_k1(G2X, G2Y, qx, qy);
    table[9] = [a9, b9];
    let (a10, b10) = ec_add_k1(G2X, G2Y, q2x, q2y);
    table[10] = [a10, b10];
    let (a11, b11) = ec_add_k1(G2X, G2Y, q3x, q3y);
    table[11] = [a11, b11];
    table[12] = [weak_reduce_k1(G3X), weak_reduce_k1(G3Y)];
    let (a13, b13) = ec_add_k1(G3X, G3Y, qx, qy);
    table[13] = [a13, b13];
    let (a14, b14) = ec_add_k1(G3X, G3Y, q2x, q2y);
    table[14] = [a14, b14];
    let (a15, b15) = ec_add_k1(G3X, G3Y, q3x, q3y);
    table[15] = [a15, b15];
    let mut acc: Pt = gen0();
    let mut win = 0usize;
    while win < 128usize {
        let (dx, dy) = ec_double_k1(acc[0], acc[1]);
        let (ddx, ddy) = ec_double_k1(dx, dy);
        acc = [ddx, ddy];
        let top = 255 - win * 2;
        let sel = select16_k1(table, u1b[top], u1b[top - 1], u2b[top], u2b[top - 1]);
        let (nx, ny) = ec_add_k1(acc[0], acc[1], sel[0], sel[1]);
        acc = [nx, ny];
        win += 1;
    }
    let (fx, fy) = ec_add_k1(acc[0], acc[1], CX, CY);
    [fx, fy]
}

// ===========================================================================
// GLV-accelerated verify (endomorphism φ(x,y)=(βx,y)=λ·P halves the doublings).
// ===========================================================================
use xark_bignum::{complement, mod_neg, mod_sub};
const LAM: L4 =
    modulus_limbs::<4, 64>("0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72");
const BETA: L4 =
    modulus_limbs::<4, 64>("0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee");
const COMPN: L4 =
    complement::<4, 64>("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");
const OX: L4 = modulus_limbs::<4, 64>(
    "89565891926547004231252920425935692360644145829622209833684329913297188986597",
);
const OY: L4 = modulus_limbs::<4, 64>(
    "12158399299693830322967808612713398636155367887041628176798871954788371653930",
);
const CORRX: L4 = modulus_limbs::<4, 64>(
    "60853107477169765182989770797083903619426259615380584983853919641424871422399",
);
const CORRY: L4 = modulus_limbs::<4, 64>(
    "41161306400859365992137843649963616879210116114343429764926620426514952863053",
);
const PHIGX: L4 = modulus_limbs::<4, 64>(
    "85340279321737800624759429340272274763154997815782306132637707972559913914315",
);
const PHIGY: L4 = modulus_limbs::<4, 64>(
    "32670510020758816978083085130507043184471273380659243275938904335757337482424",
);

/// Verify GLV decomposition u ≡ (±m1) + λ·(±m2) mod n via carry-safe mod_sub.
fn glv_decomp(u: L4, m1lo: Field, m1hi: Field, s1: Field, m2lo: Field, m2hi: Field, s2: Field) {
    let z = Field::from(0u8);
    let m1 = [m1lo, m1hi, z, z];
    let m2 = [m2lo, m2hi, z, z];
    range_check_limbs::<4, 64>(m1);
    range_check_limbs::<4, 64>(m2);
    let sk1 = muxc(s1, mod_neg::<4, 64>(m1, NN), m1);
    let sk2 = muxc(s2, mod_neg::<4, 64>(m2, NN), m2);
    let lhs = mod_mul::<4, 64>(LAM, sk2, NN, NN1);
    let rhs = mod_sub::<4, 64>(u, sk1, COMPN);
    let mut i = 0usize;
    while i < 4usize {
        aeq(lhs[i], rhs[i]);
        i += 1;
    }
}

/// Sign-conditional point negation: s ? (x, p−y) : (x, y).
fn negp(s: Field, x: L4, y: L4) -> Pt {
    [x, muxc(s, mod_neg::<4, 64>(y, M_K1), y)]
}

/// SOUND GLV-accelerated secp256k1 ECDSA verify. Magnitudes are 2×64-bit (<2^128);
/// signs are bits. The 4 decomposed half-scalars drive a 4-dim Shamir (128 doublings).
#[allow(clippy::too_many_arguments)]
pub fn ecdsa_verify_glv(
    qx: L4,
    qy: L4,
    r: L4,
    s: L4,
    e: L4,
    m11: [Field; 2],
    s11: Field,
    m12: [Field; 2],
    s12: Field,
    m21: [Field; 2],
    s21: Field,
    m22: [Field; 2],
    s22: Field,
) {
    range_check_limbs::<4, 64>(r);
    range_check_limbs::<4, 64>(s);
    range_check_limbs::<4, 64>(e);
    assert_lt::<4, 64>(r, NN1);
    assert_lt::<4, 64>(s, NN1);
    assert_lt::<4, 64>(e, NN1);
    assert_nonzero_limbs(r);
    s11.assert_bool();
    s12.assert_bool();
    s21.assert_bool();
    s22.assert_bool();
    let s_inv = mod_inverse::<4, 64>(s, NN);
    let u1 = mod_mul::<4, 64>(e, s_inv, NN, NN1);
    let u2 = mod_mul::<4, 64>(r, s_inv, NN, NN1);
    glv_decomp(u1, m11[0], m11[1], s11, m12[0], m12[1], s12);
    glv_decomp(u2, m21[0], m21[1], s21, m22[0], m22[1], s22);
    on_curve_k1(qx, qy);
    let phiqx = mul_lazy_k1(BETA, qx);
    // signed bases: ±G, ±φG, ±Q, ±φQ
    let gs = negp(s11, G0X, G0Y);
    let pgs = negp(s12, PHIGX, PHIGY);
    let qs = negp(s21, qx, qy);
    let pqs = negp(s22, phiqx, qy);
    let z: Pt = [[Field::from(0u8); 4]; 2];
    let mut t = [z; 16];
    t[0] = [weak_reduce_k1(OX), weak_reduce_k1(OY)];
    let (x1, y1) = ec_add_k1(t[0][0], t[0][1], gs[0], gs[1]);
    t[1] = [x1, y1];
    let (x2, y2) = ec_add_k1(t[0][0], t[0][1], pgs[0], pgs[1]);
    t[2] = [x2, y2];
    let (x3, y3) = ec_add_k1(t[1][0], t[1][1], pgs[0], pgs[1]);
    t[3] = [x3, y3];
    let (x4, y4) = ec_add_k1(t[0][0], t[0][1], qs[0], qs[1]);
    t[4] = [x4, y4];
    let (x5, y5) = ec_add_k1(t[1][0], t[1][1], qs[0], qs[1]);
    t[5] = [x5, y5];
    let (x6, y6) = ec_add_k1(t[2][0], t[2][1], qs[0], qs[1]);
    t[6] = [x6, y6];
    let (x7, y7) = ec_add_k1(t[3][0], t[3][1], qs[0], qs[1]);
    t[7] = [x7, y7];
    let (x8, y8) = ec_add_k1(t[0][0], t[0][1], pqs[0], pqs[1]);
    t[8] = [x8, y8];
    let (x9, y9) = ec_add_k1(t[1][0], t[1][1], pqs[0], pqs[1]);
    t[9] = [x9, y9];
    let (x10, y10) = ec_add_k1(t[2][0], t[2][1], pqs[0], pqs[1]);
    t[10] = [x10, y10];
    let (x11, y11) = ec_add_k1(t[3][0], t[3][1], pqs[0], pqs[1]);
    t[11] = [x11, y11];
    let (x12, y12) = ec_add_k1(t[4][0], t[4][1], pqs[0], pqs[1]);
    t[12] = [x12, y12];
    let (x13, y13) = ec_add_k1(t[5][0], t[5][1], pqs[0], pqs[1]);
    t[13] = [x13, y13];
    let (x14, y14) = ec_add_k1(t[6][0], t[6][1], pqs[0], pqs[1]);
    t[14] = [x14, y14];
    let (x15, y15) = ec_add_k1(t[7][0], t[7][1], pqs[0], pqs[1]);
    t[15] = [x15, y15];
    let u1b1 = scalar_to_bits_256([m11[0], m11[1], Field::from(0u8), Field::from(0u8)]);
    let u1b2 = scalar_to_bits_256([m12[0], m12[1], Field::from(0u8), Field::from(0u8)]);
    let u2b1 = scalar_to_bits_256([m21[0], m21[1], Field::from(0u8), Field::from(0u8)]);
    let u2b2 = scalar_to_bits_256([m22[0], m22[1], Field::from(0u8), Field::from(0u8)]);
    let mut acc: Pt = [weak_reduce_k1(OX), weak_reduce_k1(OY)];
    let mut w = 0usize;
    while w < 128usize {
        let (dx, dy) = ec_double_k1(acc[0], acc[1]);
        acc = [dx, dy];
        let pos = 127 - w;
        let sel = select16_k1(t, u2b2[pos], u2b1[pos], u1b2[pos], u1b1[pos]);
        let (nx, ny) = ec_add_k1(acc[0], acc[1], sel[0], sel[1]);
        acc = [nx, ny];
        w += 1;
    }
    let (fx, _fy) = ec_add_k1(acc[0], acc[1], CORRX, CORRY);
    let rxn = reduce_once::<4, 64>(finalize_k1(fx), NN);
    let mut i = 0usize;
    while i < 4usize {
        aeq(rxn[i], r[i]);
        i += 1;
    }
}

/// SOUND lazy secp256k1 ECDSA verification. `qx`/`qy` are the public key (4×64
/// limbs); `r`/`s`/`e` are the signature and message scalars (4×64 limbs, < n).
pub fn ecdsa_verify_lazy(qx: L4, qy: L4, r: L4, s: L4, e: L4) {
    range_check_limbs::<4, 64>(r);
    range_check_limbs::<4, 64>(s);
    range_check_limbs::<4, 64>(e);
    assert_lt::<4, 64>(r, NN1);
    assert_lt::<4, 64>(s, NN1);
    assert_lt::<4, 64>(e, NN1);
    assert_nonzero_limbs(r);
    let s_inv = mod_inverse::<4, 64>(s, NN);
    let u1 = mod_mul::<4, 64>(e, s_inv, NN, NN1);
    let u2 = mod_mul::<4, 64>(r, s_inv, NN, NN1);
    let u1b = scalar_to_bits_256(u1);
    let u2b = scalar_to_bits_256(u2);
    let rr = dsm_lazy_k1(u1b, u2b, qx, qy);
    // r == rr.x mod n  (rr.x < p < 2n, one conditional subtract)
    let rxn = reduce_once::<4, 64>(finalize_k1(rr[0]), NN);
    let mut i = 0usize;
    while i < 4usize {
        aeq(rxn[i], r[i]);
        i += 1;
    }
}
