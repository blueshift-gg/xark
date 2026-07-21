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
//! The shipped verifier is the GLV-accelerated 4×64 lazy gadget below
//! ([`Point::verify`]); the non-native field / EC arithmetic lives in [`xark_bignum`]
//! (shared with secp256r1, parameterized by modulus). Inputs are the transparent
//! compound types [`Point`] / [`Signature`] / [`Scalar`] — the caller never touches
//! limbs. Every arithmetic building block is individually solver-validated (see the
//! `xark` compiler snapshot tests).

#![no_std]

/// The eager **3×86-bit** incomplete-affine curve gadget (`Point`, `Fq`,
/// `ec_add_incomplete`, `ec_double_incomplete`, …) emitted by the shared
/// [`xark_curve::weierstrass!`] macro. Kept in its own module because its `Point` /
/// `Scalar` use a different limb layout (3×86) than the shipped GLV verifier's
/// transparent [`Point`] / [`Scalar`] (2×128) below — so they'd collide at the crate
/// root. Used by the `ec_incomplete` example and the field-arithmetic snapshot tests;
/// the host `order` / `reduce_scalar` helpers it derives are re-exported at the root.
pub mod affine {
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
}
#[cfg(not(xark))]
pub use affine::{order, reduce_scalar};

// ===========================================================================
// SOUND LAZY ECDSA verify (4×64 lazy-affine point arithmetic + eager 4×64
// scalar ops). Alongside the macro's eager 3×86 gadget. ~30% fewer constraints.
// ===========================================================================
use xark::{require_eq as aeq, witness_begin, witness_end, Field, Transparent};
use xark_bignum::{
    assert_nonzero_limbs, ec_add_k1, ec_double_k1, finalize_k1, mod_inverse, mod_mul,
    modulus_limbs, modulus_minus_1, mul_lazy_k1, on_curve_k1, range_check_limbs, reduce_once,
    require_lt, scalar_to_bits_256, weak_reduce_k1, M_K1,
};

type L4 = [Field; 4];
type Pt = [L4; 2];

/// A secp256k1 256-bit value (a scalar `r`/`s`/`e`, or a point coordinate) in the
/// compact **2×128-bit half** public-input form — `{ limbs: [Field; 2] }` =
/// `[lo128, hi128]` in-circuit (2 public field elements vs 4 raw 64-bit limbs),
/// `[u8; 32]` big-endian on the host. Recomposed to the internal 4×64 limbs by the
/// gadget. `#[derive(Transparent)]` derives the host `NativeInput` (`[u8; 32]` →
/// `<name>.limbs[0..2]`) from this declaration.
#[derive(Clone, Copy, Transparent)]
#[transparent(bits = 128)]
pub struct Scalar {
    pub limbs: [Field; 2],
}

/// An affine secp256k1 public key as its two coordinates — compact uncompressed
/// `[u8; 64]` (`x ‖ y`, SEC1 minus the `0x04` tag) on the host, `{ x, y }`
/// (flattening to `<name>.x.limbs[i]` / `<name>.y.limbs[i]`) in-circuit. Verify a
/// signature against it with [`Point::verify`].
#[derive(Clone, Copy, Transparent)]
pub struct Point {
    pub x: Scalar,
    pub y: Scalar,
}

/// An ECDSA signature `(r, s)` — `[u8; 64]` (`r ‖ s`) on the host, `{ r, s }`
/// in-circuit. Pass it to [`Point::verify`] with the message digest.
#[derive(Clone, Copy, Transparent)]
pub struct Signature {
    pub r: Scalar,
    pub s: Scalar,
}

/// Everything to write a secp256k1-ECDSA circuit in one import:
/// `use xark_secp256k1::prelude::*;` re-exports the `xark` essentials (`circuit`,
/// `Public`, `Field`, `require_eq`, …) plus the transparent input types [`Point`],
/// [`Signature`], [`Scalar`]. Verify with `pubkey.verify(sig, digest)`.
pub mod prelude {
    pub use crate::{Point, Scalar, Signature};
    pub use xark::prelude::*;
}

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

// ===========================================================================
// GLV-accelerated verify (endomorphism φ(x,y)=(βx,y)=λ·P halves the doublings).
// ===========================================================================
use xark_bignum::{complement, is_ge, mod_add, mod_neg, mod_sub, mul_divmod, sub2};
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

// GLV lattice basis (short vectors of the endomorphism sublattice): the
// decomposition `u ↦ (k1, k2)` with `k1 + λ·k2 ≡ u (mod n)` uses
// `c_i = ⌊(b_i·u + n/2)/n⌉` then `k1 = u − c1·a1 − c2·a2`, `k2 = c1·b1 − c2·b2`
// (with `b2 = a1`). All magnitudes stay `< 2^128`.
const A1: L4 = modulus_limbs::<4, 64>("0x3086d221a7d46bcde86c90e49284eb15");
const B1: L4 = modulus_limbs::<4, 64>("0xe4437ed6010e88286f547fa90abfe4c3");
const A2: L4 = modulus_limbs::<4, 64>("0x114ca50f7a8e2f3f657c1108d9d44cfd8");
// (n+1)/2 — the round-half-up threshold and the sign-split boundary (`k > n/2`).
const NHALF1: L4 = modulus_limbs::<4, 64>(
    "57896044618658097711785492504343953926418782139537452191302581570759080747169",
);

/// Split a scalar `k ∈ [0, n)` into `(magnitude < 2^128, sign)`: the "short"
/// signed form, `k` if `k ≤ n/2` else `−(n−k)`.
fn signed_short(k: L4) -> (L4, Field) {
    let s = is_ge::<4, 64>(k, NHALF1); // k > n/2  ⇔  k ≥ (n+1)/2
    (muxc(s, mod_neg::<4, 64>(k, NN), k), s)
}

/// Derive one GLV half-decomposition of `u`: the two signed ~128-bit half-scalars
/// `(±m1, ±m2)` with `±m1 + λ·(±m2) ≡ u (mod n)`. Returns `(m1lo2, s1, m2lo2, s2)`
/// — the low two limbs of each magnitude and its sign bit. **Call inside a
/// `witness_only` region:** every op here emits witness-gen but no constraints, so
/// the whole reduction is free; the caller pins the result with `glv_decomp`.
fn glv_split(u: L4) -> ([Field; 2], Field, [Field; 2], Field) {
    let z = Field::from(0u8);
    // rounded quotients c_i = ⌊(b_i·u + n/2)/n⌉  (b2 = a1)
    let (q1, r1) = mul_divmod::<4, 64>(A1, u, NN, NN1);
    let (q2, r2) = mul_divmod::<4, 64>(B1, u, NN, NN1);
    let c1 = mod_add::<4, 64>(q1, [is_ge::<4, 64>(r1, NHALF1), z, z, z], NN);
    let c2 = mod_add::<4, 64>(q2, [is_ge::<4, 64>(r2, NHALF1), z, z, z], NN);
    // k1 = u − c1·a1 − c2·a2  (mod n)
    let k1 = sub2::<4, 64>(
        u,
        mod_mul::<4, 64>(c1, A1, NN, NN1),
        mod_mul::<4, 64>(c2, A2, NN, NN1),
        NN,
        NN1,
    );
    // k2 = c1·b1 − c2·b2  (mod n),  b2 = a1
    let k2 = mod_sub::<4, 64>(
        mod_mul::<4, 64>(c1, B1, NN, NN1),
        mod_mul::<4, 64>(c2, A1, NN, NN1),
        COMPN,
    );
    let (m1, s1) = signed_short(k1);
    let (m2, s2) = signed_short(k2);
    ([m1[0], m1[1]], s1, [m2[0], m2[1]], s2)
}

fn two64() -> Field {
    Field::from(1u128 << 64)
}

/// Recompose a 256-bit value from its two **128-bit halves** `[lo, hi]` (the compact
/// public-input form) into the 4×64-bit limbs the lazy arithmetic uses. Each half
/// is split by a `div_rem` hint into two range-checked 64-bit limbs and pinned to
/// the half — so the halves are implicitly constrained `< 2^128` and no separate
/// `range_check_limbs` is needed downstream.
fn unpack(packed: [Field; 2]) -> L4 {
    let two64 = two64();
    let lo = Field::hint_div_rem(packed[0], two64); // [hi64, lo64]
    let hi = Field::hint_div_rem(packed[1], two64);
    let limbs = [lo[1], lo[0], hi[1], hi[0]];
    range_check_limbs::<4, 64>(limbs);
    aeq(packed[0], limbs[0] + limbs[1] * two64);
    aeq(packed[1], limbs[2] + limbs[3] * two64);
    limbs
}

impl Point {
    /// Verify an ECDSA signature against this public key and message `digest`
    /// (`digest = int(hash(msg)) mod n`, supplied as a [`Scalar`]). Emits the whole
    /// constraint system; a wrong signature makes the circuit unsatisfiable. This is
    /// the transparent-type entry point — the caller never touches limbs:
    ///
    /// ```ignore
    /// #[circuit]
    /// fn secp256k1_ecdsa(pubkey: Public<Point>, sig: Public<Signature>, digest: Public<Scalar>) {
    ///     pubkey.verify(sig, digest);
    /// }
    /// ```
    pub fn verify(self, sig: Signature, digest: Scalar) {
        ecdsa_verify_packed(
            self.x.limbs,
            self.y.limbs,
            sig.r.limbs,
            sig.s.limbs,
            digest.limbs,
        );
    }
}

/// secp256k1 ECDSA verification core — the GLV-accelerated 4×64 lazy gadget
/// (128-window 4-dim Shamir via the λ-endomorphism), the fastest sound variant
/// (~1.64M constraints). Each of `qx`, `qy`, `r`, `s`, `e` is a 256-bit value as its
/// two **128-bit halves** `[lo, hi]`, recomposed to 4×64 internally. The endomorphism
/// decomposition is derived in-circuit at zero constraint cost (see [`glv_split`]) and
/// pinned by [`glv_decomp`]. Wrapped by [`Point::verify`] — callers use that.
fn ecdsa_verify_packed(
    qx: [Field; 2],
    qy: [Field; 2],
    r: [Field; 2],
    s: [Field; 2],
    e: [Field; 2],
) {
    let qx = unpack(qx);
    let qy = unpack(qy);
    let r = unpack(r);
    let s = unpack(s);
    let e = unpack(e);
    require_lt::<4, 64>(r, NN1);
    require_lt::<4, 64>(s, NN1);
    require_lt::<4, 64>(e, NN1);
    assert_nonzero_limbs(r);
    let s_inv = mod_inverse::<4, 64>(s, NN);
    let u1 = mod_mul::<4, 64>(e, s_inv, NN, NN1);
    let u2 = mod_mul::<4, 64>(r, s_inv, NN, NN1);
    // Derive the two GLV decompositions in-circuit at ZERO constraint cost, then
    // pin them exactly as before with `glv_decomp` — so the caller supplies only
    // the signature `(q, r, s, e)`, no hint inputs, and the constraint count is
    // unchanged. A wrong derivation can only fail `glv_decomp` (completeness),
    // never forge (soundness is the pin, not the derivation).
    witness_begin();
    let (m11, s11, m12, s12) = glv_split(u1);
    let (m21, s21, m22, s22) = glv_split(u2);
    witness_end();
    s11.require_bool();
    s12.require_bool();
    s21.require_bool();
    s22.require_bool();
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
