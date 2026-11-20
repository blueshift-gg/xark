//! `xark-secp256k1`: secp256k1 ECDSA gadget over the `xark` `Field` subset.
//!
//! secp256k1 is `y² = x³ + 7` (short Weierstrass with **a = 0**, j-invariant 0)
//! over the base field `p = 2^256 - 2^32 - 977`, group order `n`.
//!
//! The verifier ([`Point::verify`]) is fake GLV over 8 × 32-bit limbs whose field
//! relations are [`xark_bignum`] certificates (shared with secp256r1, parameterized
//! by modulus); scalars use 4 × 64-bit limbs. The eager 3×86-bit incomplete-affine
//! curve gadget lives in the [`affine`] submodule. Inputs are the transparent
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
// SOUND ECDSA verify (8×32 affine point arithmetic by `mul_cert_k1` certificates,
// fake GLV). Alongside the macro's eager 3×86 gadget.
// ===========================================================================
use xark::{Field, input, require_eq as aeq, witness_begin, witness_end};
use xark_bignum::{
    M_K1, assert_nonzero_limbs, b2_k1, ec_add_k1, ec_double_add_k1, modulus_limbs, modulus_minus_1,
    mul_cert_k1, on_curve_k1, one_hot8, range_check_limbs, require_lt,
};

type L4 = [Field; 4];
type L8 = [Field; 8];
type Pt = [L8; 2];

/// A secp256k1 256-bit value (a scalar `r`/`s`/`e`, or a point coordinate) in the
/// compact **2×128-bit half** public-input form — `{ limbs: [Field; 2] }` =
/// `[lo128, hi128]` in-circuit (2 public field elements vs 4 raw 64-bit limbs),
/// `[u8; 32]` big-endian on the host. Recomposed to internal limbs (4 × 64 for scalars,
/// 8 × 32 for coordinates) by the gadget. `#[input]` derives its host conversions (`[u8; 32]` →
/// `<name>.limbs[0..2]`) from this declaration.
#[input(number(bits = 128))]
pub struct Scalar {
    pub limbs: [Field; 2],
}

/// An affine secp256k1 public key as its two coordinates — compact uncompressed
/// `[u8; 64]` (`x ‖ y`, SEC1 minus the `0x04` tag) on the host, `{ x, y }`
/// (flattening to `<name>.x.limbs[i]` / `<name>.y.limbs[i]`) in-circuit. Verify a
/// signature against it with [`Point::verify`].
#[input(bytes)]
pub struct Point {
    pub x: Scalar,
    pub y: Scalar,
}

/// An ECDSA signature `(r, s)` — `[u8; 64]` (`r ‖ s`) on the host, `{ r, s }`
/// in-circuit. Pass it to [`Point::verify`] with the message digest.
#[input(bytes)]
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

#[xark::gadget]
#[doc(hidden)]
pub fn muxp(s: Field, a: Pt, b: Pt) -> Pt {
    let mut out = b;
    let mut i = 0usize;
    while i < 16 {
        out[i / 8][i % 8] = b[i / 8][i % 8] + s * (a[i / 8][i % 8] - b[i / 8][i % 8]);
        i += 1;
    }
    out
}
/// An 8 × 32-bit value as 4 × 64-bit limbs (linear).
fn x64(v: L8) -> L4 {
    let t = Field::from(1u64 << 32);
    [
        v[0] + t * v[1],
        v[2] + t * v[3],
        v[4] + t * v[5],
        v[6] + t * v[7],
    ]
}

// ===========================================================================
// Fake-GLV verify (Eagen–El Housni–Masson–Piellard, ePrint 2025/933): a hinted
// `R = u₁G + u₂Q`, and `C·G + A·Q + B·R = O` with `A`, `B` four 64-bit halves.
// ===========================================================================
// `OH` (the offset `O`), `HH` (the comb offset `H`), `OFF256N` (`−2^256·(O + H)`) and
// `COMB` (the fixed-base tables).
include!(concat!(env!("OUT_DIR"), "/comb.rs"));

/// `β` with `φ(x, y) = (βx, y) = λ·(x, y)`, and `λ`.
const BETA: L8 =
    modulus_limbs::<8, 32>("0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee");
const LAMBDA: L4 =
    modulus_limbs::<4, 64>("0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72");
const G: Pt = [
    modulus_limbs::<8, 32>("0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
    modulus_limbs::<8, 32>("0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
];
/// Digits per coefficient: each `kₘ ∈ [−2^64, 2^64)` is `cₘ − 2^64`, `cₘ < 2^65`.
const DIGITS: usize = 65;

fn two64() -> Field {
    Field::from(1u128 << 64)
}
fn pt(c: [u32; 16]) -> Pt {
    let mut out = [[Field::from(0u8); 8]; 2];
    let mut i = 0usize;
    while i < 16 {
        out[i / 8][i % 8] = Field::from(c[i] as u64);
        i += 1;
    }
    out
}

// ---- witness-region helpers: hints only, no rows -------------------------------
fn wmul(a: L8, b: L8) -> L8 {
    Field::hint_mulmod_divmod::<8>(a, b, M_K1, 32).1
}
fn wsub(a: L8, b: L8) -> L8 {
    Field::hint_sub2::<8>(a, b, [Field::from(0u8); 8], M_K1, 32).1
}
fn wmuln(a: L4, b: L4) -> L4 {
    Field::hint_mulmod_divmod::<4>(a, b, NN, 64).1
}
fn wsubn(a: L4, b: L4) -> L4 {
    Field::hint_sub2::<4>(a, b, [Field::from(0u8); 4], NN, 64).1
}
/// `P + Q` (`x_P ≠ x_Q`) on canonical coordinates.
fn wadd(p: Pt, q: Pt) -> Pt {
    let w = Field::hint_mod_inverse::<8>(wsub(q[0], p[0]), M_K1, 32);
    let l = wmul(wsub(q[1], p[1]), w);
    let x = Field::hint_sub2::<8>(wmul(l, l), p[0], q[0], M_K1, 32).1;
    [x, wsub(wmul(l, wsub(p[0], x)), p[1])]
}
/// `2P`, slope `3x²/2y`.
fn wdbl(p: Pt) -> Pt {
    let z = Field::from(0u8);
    let mut two_y = p[1];
    let mut three = [z; 8];
    three[0] = Field::from(3u8);
    let mut i = 0usize;
    while i < 8 {
        two_y[i] = p[1][i] + p[1][i];
        i += 1;
    }
    let w = Field::hint_mod_inverse::<8>(two_y, M_K1, 32);
    let l = wmul(wmul(three, wmul(p[0], p[0])), w);
    let x = Field::hint_sub2::<8>(wmul(l, l), p[0], p[0], M_K1, 32).1;
    [x, wsub(wmul(l, wsub(p[0], x)), p[1])]
}
/// `u·P` plus `2^256·off` by double-and-add from `off` (no step meets the identity).
fn wmul1(u: L4, p: Pt, off: Pt) -> Pt {
    let mut acc = off;
    let mut i = 256usize;
    while i > 0 {
        i -= 1;
        acc = wdbl(acc);
        let b = Field::hint_bit(u[i / 64], i % 64);
        acc = muxp(b, wadd(acc, p), acc);
    }
    acc
}
/// `u₁G + u₂Q`: one ladder per base, from the offsets `O` and `H` (so `Q = ±G` and
/// `u₁G = ±u₂Q` meet no exceptional add), less `2^256·(O + H)`.
fn wmul2(u1: L4, u2: L4, q: Pt) -> Pt {
    let s = wadd(wmul1(u1, G, pt(OH)), wmul1(u2, q, pt(HH)));
    wadd(s, pt(OFF256N))
}
/// Signed 64-bit columns (`|cᵢ| < 2^199`) as ten 64-bit limbs of their (non-negative) sum.
fn wnorm(cols: [Field; 10]) -> [Field; 10] {
    let mut out = [Field::from(0u8); 10];
    let mut carry = Field::from(0u8);
    let mut m = 0usize;
    while m < 10 {
        let qr = Field::hint_div_rem(cols[m] + carry + two_pow(200), two64());
        out[m] = qr[1];
        carry = qr[0] - two_pow(136);
        m += 1;
    }
    out
}
fn pad10(v: L4) -> [Field; 10] {
    let mut out = [Field::from(0u8); 10];
    let mut i = 0usize;
    while i < 4 {
        out[i] = v[i];
        i += 1;
    }
    out
}

// ---- the scalar relation ---------------------------------------------------------
fn two_pow(e: usize) -> Field {
    let mut p = Field::from(1u8);
    let mut i = 0usize;
    while i < e {
        p = p + p;
        i += 1;
    }
    p
}
/// Columns of `(k₁ + λk₂)·v` in base `2^64` (`λ = LAMBDA`'s limbs).
fn lam_cols(k1: Field, k2: Field, v: L4) -> [Field; 7] {
    let mut out = [Field::from(0u8); 7];
    let mut m = 0usize;
    while m < 7 {
        let mut l = Field::from(0u8);
        let mut j = 0usize;
        while j < 4 {
            if m >= j && m - j < 4 {
                l += LAMBDA[j] * v[m - j];
            }
            j += 1;
        }
        out[m] = k2 * l;
        if m < 4 {
            out[m] += k1 * v[m];
        }
        m += 1;
    }
    out
}
/// Columns of `a·b` in base `2^64`.
fn mul_cols(a: L4, b: L4) -> [Field; 7] {
    let mut out = [Field::from(0u8); 7];
    let mut i = 0usize;
    while i < 4 {
        let mut j = 0usize;
        while j < 4 {
            out[i + j] += a[i] * b[j];
            j += 1;
        }
        i += 1;
    }
    out
}
fn add7(a: [Field; 7], b: [Field; 7]) -> [Field; 7] {
    let mut out = a;
    let mut m = 0usize;
    while m < 7 {
        out[m] += b[m];
        m += 1;
    }
    out
}
/// The columns of `z + 2^322·n − q·n` (`2^322 = 4·2^{64·5}`).
fn rel_cols(z: [Field; 7], q: [Field; 6]) -> [Field; 10] {
    let mut out = [Field::from(0u8); 10];
    let mut m = 0usize;
    while m < 9 {
        let mut c = if m < 7 { z[m] } else { Field::from(0u8) };
        if m >= 5 {
            c += Field::from(4u8) * NN[m - 5];
        }
        let mut j = 0usize;
        while j < 4 {
            if m >= j && m - j < 6 {
                c -= NN[j] * q[m - j];
            }
            j += 1;
        }
        out[m] = c;
        m += 1;
    }
    out
}
/// `q` with `z = (q − 2^322)·n`, from the columns of `z` (witness region).
fn wquot(z: [Field; 7]) -> [Field; 6] {
    let x = wnorm(rel_cols(z, [Field::from(0u8); 6]));
    let mut one = [Field::from(0u8); 10];
    one[0] = Field::from(1u8);
    let q = Field::hint_mulmod_divmod::<10>(x, one, pad10(NN), 64).0;
    [q[0], q[1], q[2], q[3], q[4], q[5]]
}
/// The biased carries `c_m + 2^133` of `Σ cols[m]·2^{64m} = 0` (witness region).
fn wcarries(cols: [Field; 10]) -> [Field; 8] {
    let mut out = [Field::from(0u8); 8];
    let mut carry = Field::from(0u8);
    let mut m = 0usize;
    while m < 8 {
        out[m] = Field::hint_div_rem(cols[m] + carry + two_pow(197), two64())[0];
        carry = out[m] - two_pow(133);
        m += 1;
    }
    out
}
/// Assert `Σ cols[m]·2^{64m} = 0` over the integers: the carries `c_m = h_m − 2^133`,
/// `h_m < 2^134` (`to_bits`), satisfy `cols[m] + c_{m−1} = 2^64·c_m`, and the last column
/// closes the chain.
fn zero_chain(cols: [Field; 10], h: [Field; 8]) {
    let mut carry = Field::from(0u8);
    let mut m = 0usize;
    while m < 9 {
        let v = cols[m] + carry;
        if m < 8 {
            let _ = h[m].to_bits::<134>();
            carry = h[m] - two_pow(133);
            aeq(v, two64() * carry);
        } else {
            aeq(v, Field::from(0u8));
        }
        m += 1;
    }
}

/// The fake-GLV scalar checks of `ecdsa_verify_packed` (ePrint 2025/933). Inputs: `r`,
/// `s`, `e`, `x_R` (4 × 64-bit limbs, below `2^64` by the caller's range checks), the
/// hinted `cₘ` (`kₘ = cₘ − 2^64`), the hinted `C`, quotients `q₁`, `q₂`, biased carries
/// `h₁`, `h₂` of the two chains and `[t, u]` (all from the caller's witness region). Rows:
/// `cₘ < 2^65` and `C`'s, `qᵢ`'s limbs `< 2^64` (`to_bits`, whose bits it returns: the
/// digits of each `cₘ` and `C`'s 256 bits); `(k₂, k₃) ≠ 0` (`(k₂² + k₃²)·w = 1`); the
/// integer identities `A·s + B·r = (q₁ − 2^322)·n` and `C·s + B·e = (q₂ − 2^322)·n` for
/// `A = k₀ + λk₁`, `B = k₂ + λk₃` (columns in base `2^64`, carries `< 2^134` biased by
/// `2^133`); and `x_R = r + t·n`, `t, u ∈ {0, 1}`. Proven in `formal/Formal/FakeGlvK1.lean`: every
/// satisfying assignment has `A·s + B·r ≡ C·s + B·e ≡ 0`, `B ≢ 0 (mod n)` and
/// `x_R ≡ r (mod n)`, and returns those bits.
#[xark::gadget]
#[allow(clippy::too_many_arguments)]
pub fn fake_glv_check_k1(
    r: [Field; 4],
    s: [Field; 4],
    e: [Field; 4],
    xr: [Field; 4],
    c: [Field; 4],
    g: [Field; 4],
    q1: [Field; 6],
    q2: [Field; 6],
    h1: [Field; 8],
    h2: [Field; 8],
    tu: [Field; 2],
) -> ([[Field; DIGITS]; 4], [Field; 256]) {
    let z = Field::from(0u8);
    let d = [
        c[0].to_bits::<DIGITS>(),
        c[1].to_bits::<DIGITS>(),
        c[2].to_bits::<DIGITS>(),
        c[3].to_bits::<DIGITS>(),
    ];
    let mut gb = [z; 256];
    let mut i = 0usize;
    while i < 4 {
        let b = g[i].to_bits::<64>();
        let mut j = 0usize;
        while j < 64 {
            gb[64 * i + j] = b[j];
            j += 1;
        }
        i += 1;
    }
    let mut i = 0usize;
    while i < 6 {
        let _ = q1[i].to_bits::<64>();
        let _ = q2[i].to_bits::<64>();
        i += 1;
    }
    let k = [
        c[0] - two64(),
        c[1] - two64(),
        c[2] - two64(),
        c[3] - two64(),
    ];
    let _ = (k[2] * k[2] + k[3] * k[3]).inv();
    let bz = lam_cols(k[2], k[3], r);
    zero_chain(rel_cols(add7(lam_cols(k[0], k[1], s), bz), q1), h1);
    zero_chain(
        rel_cols(add7(mul_cols(g, s), lam_cols(k[2], k[3], e)), q2),
        h2,
    );
    // x_R = r + t·n over 128-bit halves (`u` the low half's carry).
    // `t·(1 − t) = 0` rather than `require_bool`: its product folds to the constant
    // whether `t` is the caller's hint or a harness input, so both emit one row.
    let (t, u) = (tu[0], tu[1]);
    aeq(t * (Field::from(1u8) - t), z);
    aeq(u * (Field::from(1u8) - u), z);
    let (rl, rh, xl, xh, nl, nh) = halves(r, xr);
    aeq(rl + t * nl, xl + u * two_pow(128));
    aeq(xh, rh + t * nh + u);
    (d, gb)
}

/// The 128-bit halves of `r`, `x_R` and `n`.
fn halves(r: L4, xr: L4) -> (Field, Field, Field, Field, Field, Field) {
    let h = |v: L4| (v[0] + two64() * v[1], v[2] + two64() * v[3]);
    let ((rl, rh), (xl, xh), (nl, nh)) = (h(r), h(xr), h(NN));
    (rl, rh, xl, xh, nl, nh)
}

fn xor(a: Field, b: Field) -> Field {
    a + b - Field::from(2u8) * a * b
}

/// `t[e₂ + 2e₃ + 4e₄]` by a mux tree over the three index bits.
fn select8(t: [Pt; 8], e2: Field, e3: Field, e4: Field) -> Pt {
    let a = [
        muxp(e2, t[1], t[0]),
        muxp(e2, t[3], t[2]),
        muxp(e2, t[5], t[4]),
        muxp(e2, t[7], t[6]),
    ];
    muxp(e4, muxp(e3, a[3], a[2]), muxp(e3, a[1], a[0]))
}

/// Recompose a 256-bit value from its two **128-bit halves** `[lo, hi]` (the compact
/// public-input form) into the 4×64-bit limbs the scalar relations use. Each half
/// is split by a `div_rem` hint into two range-checked 64-bit limbs and pinned to
/// the half — so the halves are implicitly constrained `< 2^128` and no separate
/// `range_check_limbs` is needed downstream.
#[xark::gadget]
#[doc(hidden)]
pub fn unpack(packed: [Field; 2]) -> L4 {
    let two64 = two64();
    let lo = Field::hint_div_rem(packed[0], two64); // [hi64, lo64]
    let hi = Field::hint_div_rem(packed[1], two64);
    let limbs = [lo[1], lo[0], hi[1], hi[0]];
    range_check_limbs::<4, 64>(limbs);
    aeq(packed[0], limbs[0] + limbs[1] * two64);
    aeq(packed[1], limbs[2] + limbs[3] * two64);
    limbs
}

/// The same as 8 × 32-bit limbs (the point coordinates' layout).
#[xark::gadget]
#[doc(hidden)]
pub fn unpack8(packed: [Field; 2]) -> L8 {
    let two32 = Field::from(1u64 << 32);
    let mut out = [Field::from(0u8); 8];
    // The split is scratch; the range checks and the two sums below pin every limb.
    witness_begin();
    let mut k = 0usize;
    while k < 2 {
        let mut v = packed[k];
        let mut j = 0usize;
        while j < 3 {
            let qr = Field::hint_div_rem(v, two32);
            out[4 * k + j] = qr[1];
            v = qr[0];
            j += 1;
        }
        out[4 * k + 3] = v;
        k += 1;
    }
    witness_end();
    range_check_limbs::<8, 32>(out);
    let mut k = 0usize;
    while k < 2 {
        let o = 4 * k;
        let sum = out[o] + two32 * (out[o + 1] + two32 * (out[o + 2] + two32 * out[o + 3]));
        aeq(packed[k], sum);
        k += 1;
    }
    out
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

/// `(x, βx mod p)`'s certified second coordinate: a hinted canonical product,
/// range-checked and certified.
fn phi_x(x: L8) -> L8 {
    witness_begin();
    let px = wmul(BETA, x);
    witness_end();
    range_check_limbs::<8, 32>(px);
    mul_cert_k1(BETA, x, px);
    px
}

/// secp256k1 ECDSA verification core, by fake GLV (Eagen–El Housni–Masson–Piellard,
/// ePrint 2025/933; zkGolf b3730d4f): the prover hints `R = u₁G + u₂Q` (`u₁ = e/s`,
/// `u₂ = r/s`), checked canonical and on the curve with `x_R ≡ r (mod n)`, and a short
/// `(A, B) = (k₀ + λk₁, k₂ + λk₃)` with `A ≡ −B·u₂` and `C ≡ −B·u₁` (`kₘ ∈ [−2^64, 2^64)`,
/// the lattice hint [`Field::hint_fake_glv`]); [`fake_glv_check_k1`] pins them, and the
/// circuit proves `C·G + A·Q + B·R = O`, so `B·R = B·(u₁G + u₂Q)` with `B ≢ 0`. Group side:
/// 65 fused steps [`ec_double_add_k1`] from the offset `O` over the 8-entry table
/// `Q ± φQ ± R ± φR` reach `M = 2^65·O + Σₘ (2kₘ + 1)·Pₘ`; a fixed-base comb (32 windows
/// of a byte of `C`, [`one_hot8`] over constant tables, 31 adds; Lim–Lee, CRYPTO 1994)
/// gives `C' = 2C·G − 2^65·O`; and `M + C' = Q + φQ + R + φR` (the table's first entry),
/// i.e. `2(C·G + A·Q + B·R) = O`. Each of `qx`, `qy`, `r`, `s`, `e` is a 256-bit value as
/// its two 128-bit halves `[lo, hi]`. Wrapped by [`Point::verify`].
///
/// Exceptional cases: a step, comb add or the last add refuses `x_A ≡ x_S` and
/// `A + S = −A`, which needs the discrete log of `O` or of the comb's `H` to reach. The
/// table adds `(Q ± φQ) ± (R ± φR)` refuse exactly the signatures with `R = μ·Q`,
/// `μ ∈ {±1, ±(1+λ)/(1−λ), ±(1−λ)/(1+λ)} mod n`, i.e. the nonce `k ≡ μ·q` for the key
/// `q`: there `Q ± φQ = ±(R ± φR)`. No public key is refused.
fn ecdsa_verify_packed(
    qx: [Field; 2],
    qy: [Field; 2],
    r: [Field; 2],
    s: [Field; 2],
    e: [Field; 2],
) {
    let z = Field::from(0u8);
    let qx = unpack8(qx);
    let qy = unpack8(qy);
    let r = unpack(r);
    let s = unpack(s);
    let e = unpack(e);
    require_lt::<4, 64>(r, NN1);
    require_lt::<4, 64>(s, NN1);
    require_lt::<4, 64>(e, NN1);
    assert_nonzero_limbs(r);
    assert_nonzero_limbs(s);
    on_curve_k1(qx, qy);
    // The whole fake-GLV witness costs no rows; `fake_glv_check_k1` and the curve
    // checks below pin it.
    witness_begin();
    let si = Field::hint_mod_inverse::<4>(s, NN, 64);
    let u1 = wmuln(e, si);
    let u2 = wmuln(r, si);
    let rp = wmul2(u1, u2, [qx, qy]);
    let k = Field::hint_fake_glv::<4>(wsubn([z; 4], u2), NN, LAMBDA, 64);
    let c = [
        k[0] + two64(),
        k[1] + two64(),
        k[2] + two64(),
        k[3] + two64(),
    ];
    // C = −B·u₁ mod n, from B + 2^64·n ≥ 0.
    let mut bc = [z; 10];
    let mut m = 0usize;
    while m < 5 {
        if m < 4 {
            bc[m] = LAMBDA[m] * k[3];
        }
        if m == 0 {
            bc[m] += k[2];
        } else {
            bc[m] += NN[m - 1];
        }
        m += 1;
    }
    let g = Field::hint_mulmod_divmod::<10>(wnorm(bc), pad10(wsubn([z; 4], u1)), pad10(NN), 64).1;
    let g = [g[0], g[1], g[2], g[3]];
    let bz = lam_cols(k[2], k[3], r);
    let z1 = add7(lam_cols(k[0], k[1], s), bz);
    let z2 = add7(mul_cols(g, s), lam_cols(k[2], k[3], e));
    let q1 = wquot(z1);
    let q2 = wquot(z2);
    let h1 = wcarries(rel_cols(z1, q1));
    let h2 = wcarries(rel_cols(z2, q2));
    let (rl, rh, _, xh, nl, _) = halves(r, x64(rp[0]));
    let t = Field::hint_div_rem(xh - rh, two_pow(127))[0];
    let u = Field::hint_div_rem(rl + t * nl, two_pow(128))[0];
    witness_end();
    // R: limbs, canonical, on the curve (gnark GHSA-7fx8: a hinted point is checked).
    range_check_limbs::<8, 32>(rp[0]);
    range_check_limbs::<8, 32>(rp[1]);
    on_curve_k1(rp[0], rp[1]);
    let (d, gb) = fake_glv_check_k1(r, s, e, x64(rp[0]), c, g, q1, q2, h1, h2, [t, u]);

    // Table over P = (Q, φQ, R, φR): entry e₂ + 2e₃ + 4e₄ is A_{e₂} + σ(e₃)·B_{e₃⊕e₄},
    // A_e = Q + σ(e)φQ, B_e = R + σ(e)φR, σ(b) = 1 − 2b; an entry with e₃ = 1 is
    // −(B_{¬e₄} − A_{e₂}). Every `−y` is kept as `2p − y` limb-wise (limbs < 2^33, no rows).
    let b2 = b2_k1();
    let neg = |y: L8| -> L8 {
        let mut out = y;
        let mut l = 0usize;
        while l < 8 {
            out[l] = b2[l] - y[l];
            l += 1;
        }
        out
    };
    let phiqx = phi_x(qx);
    let phirx = phi_x(rp[0]);
    let a = [
        ec_add_k1(qx, qy, phiqx, qy),
        ec_add_k1(qx, qy, phiqx, neg(qy)),
    ];
    let b = [
        ec_add_k1(rp[0], rp[1], phirx, rp[1]),
        ec_add_k1(rp[0], rp[1], phirx, neg(rp[1])),
    ];
    let na = [neg(a[0].1), neg(a[1].1)];
    let zp: Pt = [[z; 8]; 2];
    let mut t = [zp; 8];
    let mut i = 0usize;
    while i < 8 {
        let (e2, e3, e4) = (i & 1, (i >> 1) & 1, i >> 2);
        if e3 == 0 {
            let (x, y) = ec_add_k1(a[e2].0, a[e2].1, b[e4].0, b[e4].1);
            t[i] = [x, y];
        } else {
            let (x, y) = ec_add_k1(b[1 - e4].0, b[1 - e4].1, a[e2].0, na[e2]);
            t[i] = [x, neg(y)];
        }
        i += 1;
    }
    // Digit i adds d₀·t[d₀d₁, d₀d₂, d₀d₃] = Σ dₘPₘ; d₀ = −1 gives `y ↦ 2p − y`.
    let mut acc: Pt = pt(OH);
    let mut w = 0usize;
    while w < DIGITS {
        let i = DIGITS - 1 - w;
        let sel = select8(
            t,
            xor(d[0][i], d[1][i]),
            xor(d[0][i], d[2][i]),
            xor(d[0][i], d[3][i]),
        );
        let mut sy = [z; 8];
        let mut l = 0usize;
        while l < 8 {
            let y = sel[1][l];
            sy[l] = b2[l] - y + d[0][i] * (y + y - b2[l]);
            l += 1;
        }
        let (x, y) = ec_double_add_k1(acc[0], acc[1], sel[0], sy);
        acc = [x, y];
        w += 1;
    }
    // C' = Σⱼ COMB[j][byte j of C] = 2C·G − 2^65·O.
    let mut cacc: Pt = zp;
    let mut j = 0usize;
    while j < 32 {
        let mut bits = [z; 8];
        let mut l = 0usize;
        while l < 8 {
            bits[l] = gb[8 * j + l];
            l += 1;
        }
        let hot = one_hot8(bits);
        let mut sel: Pt = zp;
        let mut v = 0usize;
        while v < 256 {
            let c = pt(COMB[j][v]);
            let mut l = 0usize;
            while l < 16 {
                sel[l / 8][l % 8] += hot[v] * c[l / 8][l % 8];
                l += 1;
            }
            v += 1;
        }
        cacc = if j == 0 {
            sel
        } else {
            let (x, y) = ec_add_k1(cacc[0], cacc[1], sel[0], sel[1]);
            [x, y]
        };
        j += 1;
    }
    // M + C' = t[0] = Q + φQ + R + φR, compared mod p.
    let (fx, fy) = ec_add_k1(acc[0], acc[1], cacc[0], cacc[1]);
    let mut one = [z; 8];
    one[0] = Field::from(1u8);
    mul_cert_k1(fx, one, t[0][0]);
    mul_cert_k1(fy, one, t[0][1]);
}
