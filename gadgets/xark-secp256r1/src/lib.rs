//! `xark-secp256r1`: NIST P-256 / secp256r1 ECDSA gadget over the `xark`
//! `Field` subset.
//!
//! P-256 is `y² = x³ − 3x + b` (short Weierstrass with **a = −3**) over the base
//! field `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, group order `n`. The shipped verifier
//! ([`Point::verify`]) is fake GLV over 8 × 32-bit limbs whose field relations are
//! [`xark_bignum::mul_cert_r1`] certificates; P-256 has no endomorphism, so the scalar
//! split is the 2-dimensional one (`A`, `B` below `2^128`).
//!
//! # Inputs
//! The public inputs are the transparent [`Point`] / [`Signature`] / [`Scalar`]
//! types, each a 256-bit value in the compact **2×128-bit half** form (2 public
//! field elements per value) — matching secp256k1. The verifier recomposes them into
//! 4 × 64-bit limbs for scalars and 8 × 32-bit limbs for point coordinates. The eager
//! 3×86-bit affine curve gadget
//! (`Point`/`Fq`/`Fp`, emitted by [`xark_curve::weierstrass!`]) lives in the [`affine`]
//! submodule.

#![no_std]

/// The 3×86-bit incomplete-affine P-256 curve gadget (`Point`, `Fq`, `Fp`,
/// `double_scalar_mul_incomplete`, …), emitted by the shared
/// [`xark_curve::weierstrass!`] macro (`a = -3` selects the `3x² − 3` doubling
/// numerator). Kept in its own module because its `Point` / `Scalar` names would
/// otherwise collide with the compact 2×128 public-input types below; used by the
/// `ec_incomplete_r1` and `on_curve_r1` examples.
pub mod affine {
    xark_curve::weierstrass! {
        base = "0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF",
        scalar = "0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551",
        a = -3,
        b = [23805269282153275520606283, 64478498050055519801623345, 6858709101169761702330043],
        generators = [
            [52227620040540588600771222, 33347259622618539004134583, 8091721874918813684698062, 59685082318776612195095029, 54599710628478995760242092, 6036146923926000695307902],
            [60574784517941929169033592, 38742641973200156549941727, 9440742814978962916680995, 50180633949907515547874257, 52108912657982010475124979, 564125721045731681407961],
            [55202213340089332766604652, 75352241312048865668270014, 7162618025266537839759230, 19003939109578686433415218, 32907397120494406415210721, 10215774641556159746766000],
            [26100211762158113520814162, 69619406642068213128195553, 17100660033962586070975197, 17982870448577553720334534, 69510469396798200300113868, 16996192830591725418421758],
        ],
        correction = [73008335506530070440987265, 52113507725237922464657843, 1975229404901465064722683, 4808832657966113361640839, 48622947606618793931251433, 9925785685835320508030124],
    }
}
#[cfg(not(xark))]
pub use affine::{order, reduce_scalar};

use xark::{Field, input, require_eq as aeq, witness_begin, witness_end};
use xark_bignum::{
    M_R1, assert_nonzero_limbs, b2_r1, ec_add_r1, ec_double_add_r1, modulus_limbs, modulus_minus_1,
    mul_cert_r1, on_curve_r1, one_hot8, range_check_limbs, require_lt,
};

type L4 = [Field; 4];
type L8 = [Field; 8];
type Pt = [L8; 2];

/// A P-256 256-bit value (a scalar `r`/`s`/`e`, or a point coordinate) in the
/// compact **2×128-bit half** public-input form — `{ limbs: [Field; 2] }` =
/// `[lo128, hi128]` in-circuit (2 public field elements vs 4 raw 64-bit limbs),
/// `[u8; 32]` big-endian on the host. Recomposed to internal limbs (4 × 64 for scalars,
/// 8 × 32 for coordinates) by the gadget. `#[input]` derives its host conversions (`[u8; 32]`
/// → `<name>.limbs[0..2]`) from this declaration.
#[input(number(bits = 128))]
pub struct Scalar {
    pub limbs: [Field; 2],
}

/// An affine P-256 public key as its two coordinates — compact uncompressed
/// `[u8; 64]` (`x ‖ y`, SEC1 minus the `0x04` tag) on the host, `{ x, y }`
/// (flattening to `<name>.x.limbs[i]` / `<name>.y.limbs[i]`) in-circuit. Verify a
/// signature against it with [`Point::verify`].
#[input(bytes)]
pub struct Point {
    pub x: Scalar,
    pub y: Scalar,
}

/// A P-256 ECDSA signature `(r, s)` — `[u8; 64]` (`r ‖ s`) on the host, `{ r, s }`
/// in-circuit. Pass it to [`Point::verify`] with the message digest.
#[input(bytes)]
pub struct Signature {
    pub r: Scalar,
    pub s: Scalar,
}

/// Everything to write a secp256r1-ECDSA circuit in one import:
/// `use xark_secp256r1::prelude::*;` re-exports the `xark` essentials (`circuit`,
/// `Public`, `Field`, `require_eq`, …) plus the transparent input types [`Point`],
/// [`Signature`], [`Scalar`]. Verify with `pubkey.verify(sig, digest)`.
pub mod prelude {
    pub use crate::{Point, Scalar, Signature};
    pub use xark::prelude::*;
}

const NN: L4 =
    modulus_limbs::<4, 64>("0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551");
const NN1: L4 =
    modulus_minus_1::<4, 64>("0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551");
/// `2^64`, the lattice hint's `λ`: P-256 has no endomorphism, so `A = k₀ + 2^64·k₁`.
const LAMBDA: L4 = modulus_limbs::<4, 64>("0x10000000000000000");
/// `2^129` as 4 × 64-bit limbs.
const P129: L4 = modulus_limbs::<4, 64>("0x200000000000000000000000000000000");
const G: Pt = [
    modulus_limbs::<8, 32>("0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296"),
    modulus_limbs::<8, 32>("0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5"),
];
/// Digits per coefficient: `A`, `B ∈ [−2^129, 2^129)` are `a − 2^129`, `b − 2^129`,
/// `a, b < 2^130`.
const DIGITS: usize = 130;

// `OH` (the offset `O`), `HH` (the comb offset `H`), `OFF256N` (`−2^256·(O + H)`) and
// `COMB` (the fixed-base tables).
include!(concat!(env!("OUT_DIR"), "/comb.rs"));

fn two_pow(e: usize) -> Field {
    let mut p = Field::from(1u8);
    let mut i = 0usize;
    while i < e {
        p = p + p;
        i += 1;
    }
    p
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
fn xor(a: Field, b: Field) -> Field {
    a + b - Field::from(2u8) * a * b
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

// ---- witness-region helpers: hints only, no rows -------------------------------
fn wmul(a: L8, b: L8) -> L8 {
    Field::hint_mulmod_divmod::<8>(a, b, M_R1, 32).1
}
fn wsub(a: L8, b: L8) -> L8 {
    Field::hint_sub2::<8>(a, b, [Field::from(0u8); 8], M_R1, 32).1
}
fn wmuln(a: L4, b: L4) -> L4 {
    Field::hint_mulmod_divmod::<4>(a, b, NN, 64).1
}
fn wsubn(a: L4, b: L4) -> L4 {
    Field::hint_sub2::<4>(a, b, [Field::from(0u8); 4], NN, 64).1
}
/// `P + Q` (`x_P ≠ x_Q`) on canonical coordinates.
fn wadd(p: Pt, q: Pt) -> Pt {
    let w = Field::hint_mod_inverse::<8>(wsub(q[0], p[0]), M_R1, 32);
    let l = wmul(wsub(q[1], p[1]), w);
    let x = Field::hint_sub2::<8>(wmul(l, l), p[0], q[0], M_R1, 32).1;
    [x, wsub(wmul(l, wsub(p[0], x)), p[1])]
}
/// `2P`, slope `(3x² − 3)/2y`.
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
    let w = Field::hint_mod_inverse::<8>(two_y, M_R1, 32);
    let num = wsub(wmul(three, wmul(p[0], p[0])), three);
    let l = wmul(num, w);
    let x = Field::hint_sub2::<8>(wmul(l, l), p[0], p[0], M_R1, 32).1;
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
/// `u₁G + u₂Q`: one ladder per base, from the offsets `O` and `H`, less `2^256·(O + H)`.
fn wmul2(u1: L4, u2: L4, q: Pt) -> Pt {
    let s = wadd(wmul1(u1, G, pt(OH)), wmul1(u2, q, pt(HH)));
    wadd(s, pt(OFF256N))
}
/// Signed columns (`|cᵢ| < 2^199`) as ten 64-bit limbs of their (non-negative) sum.
fn wnorm<const K: usize>(cols: [Field; K]) -> [Field; 10] {
    let mut out = [Field::from(0u8); 10];
    let mut carry = Field::from(0u8);
    let mut m = 0usize;
    while m < 10 {
        let c = if m < K { cols[m] } else { Field::from(0u8) };
        let qr = Field::hint_div_rem(c + carry + two_pow(200), two_pow(64));
        out[m] = qr[1];
        carry = qr[0] - two_pow(136);
        m += 1;
    }
    out
}
/// The quotient (ten 64-bit limbs) of the columns' sum by `n` (exact for honest inputs).
fn wquot<const K: usize>(cols: [Field; K]) -> [Field; 10] {
    let z = Field::from(0u8);
    let mut one = [z; 10];
    one[0] = Field::from(1u8);
    let nn = [NN[0], NN[1], NN[2], NN[3], z, z, z, z, z, z];
    Field::hint_mulmod_divmod::<10>(wnorm(cols), one, nn, 64).0
}
/// The biased carries `c_m + 2^134` of `Σ cols[m]·2^{64m} = 0`.
fn wcarries<const K: usize, const H: usize>(cols: [Field; K]) -> [Field; H] {
    let mut out = [Field::from(0u8); H];
    let mut carry = Field::from(0u8);
    let mut m = 0usize;
    while m < H {
        out[m] = Field::hint_div_rem(cols[m] + carry + two_pow(198), two_pow(64))[0];
        carry = out[m] - two_pow(134);
        m += 1;
    }
    out
}

// ---- the scalar relations ------------------------------------------------------
/// Columns of `a·s + b·r − 2^129·(s + r) + 2^131·n − q₁·n` in base `2^64`, i.e. of
/// `A·s + B·r − (q₁ − 2^131)·n`.
fn rel1(a: Field, b: Field, r: L4, s: L4, q1: Field) -> [Field; 4] {
    let mut out = [Field::from(0u8); 4];
    let mut m = 0usize;
    while m < 4 {
        out[m] =
            a * s[m] + b * r[m] - two_pow(129) * (s[m] + r[m]) + two_pow(131) * NN[m] - q1 * NN[m];
        m += 1;
    }
    out
}
/// Columns of `C·s + b·e − 2^129·e + 2^131·n − q₂·n`, i.e. of `C·s + B·e − (q₂ − 2^131)·n`.
fn rel2(g: L4, b: Field, s: L4, e: L4, q2: [Field; 5]) -> [Field; 8] {
    let mut out = [Field::from(0u8); 8];
    let mut m = 0usize;
    while m < 8 {
        let mut c = Field::from(0u8);
        let mut i = 0usize;
        while i < 4 {
            if m >= i && m - i < 4 {
                c += g[i] * s[m - i];
            }
            if m >= i && m - i < 5 {
                c -= NN[i] * q2[m - i];
            }
            i += 1;
        }
        if m < 4 {
            c += b * e[m] - two_pow(129) * e[m] + two_pow(131) * NN[m];
        }
        out[m] = c;
        m += 1;
    }
    out
}
/// Assert `Σ cols[m]·2^{64m} = 0` over the integers: the carries `c_m = h_m − 2^134`,
/// `h_m < 2^135` (`to_bits`), satisfy `cols[m] + c_{m−1} = 2^64·c_m`, and the last column
/// closes the chain.
fn zero_chain<const K: usize, const H: usize>(cols: [Field; K], h: [Field; H]) {
    const { assert!(K == H + 1) };
    let mut carry = Field::from(0u8);
    let mut m = 0usize;
    while m < K {
        let v = cols[m] + carry;
        if m < H {
            let _ = h[m].to_bits::<135>();
            carry = h[m] - two_pow(134);
            aeq(v, two_pow(64) * carry);
        } else {
            aeq(v, Field::from(0u8));
        }
        m += 1;
    }
}

/// The fake-GLV scalar checks of [`ecdsa_verify`] (ePrint 2025/933), with no endomorphism.
/// Inputs: `r`, `s`, `e`, `x_R` (4 × 64-bit limbs, below `2^64` by the caller's range
/// checks), the hinted `[a, b]` (`A = a − 2^129`, `B = b − 2^129`), `C`, the quotients `q₁`,
/// `q₂`, the biased carries `h₁`, `h₂` and `[t, u]` (all from the caller's witness region).
/// Rows: `a, b < 2^130`, `C`'s and `q₂`'s limbs `< 2^64`, `q₁ < 2^132` (`to_bits`, whose bits
/// it returns: the digits of `a`, `b` and `C`'s 256 bits); `B ≠ 0` (`(b − 2^129)·w = 1`);
/// the integer identities `A·s + B·r = (q₁ − 2^131)·n` and `C·s + B·e = (q₂ − 2^131)·n`
/// (columns in base `2^64`, carries `< 2^135` biased by `2^134`); and `x_R = r + t·n`,
/// `t, u ∈ {0, 1}`. Proven in `formal/Formal/FakeGlvR1.lean`: every satisfying assignment
/// has `A·s + B·r ≡ C·s + B·e ≡ 0`, `B ≢ 0 (mod n)` (`0 < |B| ≤ 2^129 < n`) and
/// `x_R ≡ r (mod n)`, and returns those bits.
#[xark::gadget]
#[allow(clippy::too_many_arguments)]
pub fn fake_glv_check_r1(
    r: [Field; 4],
    s: [Field; 4],
    e: [Field; 4],
    xr: [Field; 4],
    ab: [Field; 2],
    g: [Field; 4],
    q1: Field,
    q2: [Field; 5],
    h1: [Field; 3],
    h2: [Field; 7],
    tu: [Field; 2],
) -> ([[Field; DIGITS]; 2], [Field; 256]) {
    let z = Field::from(0u8);
    let d = [ab[0].to_bits::<DIGITS>(), ab[1].to_bits::<DIGITS>()];
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
    let _ = q1.to_bits::<132>();
    let mut i = 0usize;
    while i < 5 {
        let _ = q2[i].to_bits::<64>();
        i += 1;
    }
    let _ = (ab[1] - two_pow(129)).inv();
    zero_chain(rel1(ab[0], ab[1], r, s, q1), h1);
    zero_chain(rel2(g, ab[1], s, e, q2), h2);
    // x_R = r + t·n over 128-bit halves (`u` the low half's carry).
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
    let t = two_pow(64);
    let h = |v: L4| (v[0] + t * v[1], v[2] + t * v[3]);
    let ((rl, rh), (xl, xh), (nl, nh)) = (h(r), h(xr), h(NN));
    (rl, rh, xl, xh, nl, nh)
}

/// A 256-bit value from its two **128-bit halves** `[lo, hi]` (the compact public-input
/// form) as 4 × 64-bit limbs: each half split by a `div_rem` hint into two range-checked
/// limbs pinned to it, so the halves are constrained `< 2^128`.
#[xark::gadget]
#[doc(hidden)]
pub fn unpack4(packed: [Field; 2]) -> L4 {
    let two64 = two_pow(64);
    let lo = Field::hint_div_rem(packed[0], two64);
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
    /// (`digest = int(hash(msg)) mod n`, a [`Scalar`]). The transparent-type entry
    /// point — the caller never touches limbs:
    ///
    /// ```ignore
    /// #[circuit]
    /// fn secp256r1_ecdsa(pubkey: Public<Point>, sig: Public<Signature>, digest: Public<Scalar>) {
    ///     pubkey.verify(sig, digest);
    /// }
    /// ```
    pub fn verify(self, sig: Signature, digest: Scalar) {
        ecdsa_verify(self, sig.r, sig.s, digest);
    }
}

/// P-256 ECDSA verification core, by fake GLV (Eagen–El Housni–Masson–Piellard, ePrint
/// 2025/933) without an endomorphism: the prover hints `R = u₁G + u₂Q` (`u₁ = e/s`,
/// `u₂ = r/s`), checked canonical and on the curve with `x_R ≡ r (mod n)`, and a short
/// `(A, B)` (`|A|, |B| ≤ 2^129`) with `A ≡ −B·u₂` and `C ≡ −B·u₁` (the lattice hint
/// [`Field::hint_fake_glv`] at `λ = 2^64`); [`fake_glv_check_r1`] pins them, and the circuit
/// proves `C·G + A·Q + B·R = O`, so `B·R = B·(u₁G + u₂Q)` with `B ≢ 0`. Group side: 130
/// fused steps [`ec_double_add_r1`] from the offset `O` over the table `±(Q ± R)` reach
/// `M = 2^130·O + (2A + 1)·Q + (2B + 1)·R`; a fixed-base comb (32 windows of a byte of `C`,
/// [`one_hot8`] over constant tables, 31 adds; Lim–Lee, CRYPTO 1994) gives
/// `C' = 2C·G − 2^130·O`; and `M + C' = Q + R` (the table's first entry), i.e.
/// `2(C·G + A·Q + B·R) = O`. Wrapped by [`Point::verify`].
///
/// Exceptional cases: a step, comb add or the last add refuses `x_A ≡ x_S` and
/// `A + S = −A`, which needs the discrete log of `O` or of the comb's `H` to reach. The
/// table adds `Q ± R` refuse exactly the signatures with `R = ±Q`, i.e. the nonce `k ≡ ±q`
/// for the key `q`. No public key is refused.
pub fn ecdsa_verify(q: Point, r: Scalar, s: Scalar, e: Scalar) {
    let z = Field::from(0u8);
    let two64 = two_pow(64);
    let qx = unpack8(q.x.limbs);
    let qy = unpack8(q.y.limbs);
    let r = unpack4(r.limbs);
    let s = unpack4(s.limbs);
    let e = unpack4(e.limbs);
    require_lt::<4, 64>(r, NN1);
    require_lt::<4, 64>(s, NN1);
    require_lt::<4, 64>(e, NN1);
    assert_nonzero_limbs(r);
    assert_nonzero_limbs(s);
    on_curve_r1(qx, qy);
    // The whole fake-GLV witness costs no rows; `fake_glv_check_r1` and the curve checks
    // below pin it.
    witness_begin();
    let si = Field::hint_mod_inverse::<4>(s, NN, 64);
    let u1 = wmuln(e, si);
    let u2 = wmuln(r, si);
    let rp = wmul2(u1, u2, [qx, qy]);
    let k = Field::hint_fake_glv::<4>(wsubn([z; 4], u2), NN, LAMBDA, 64);
    let a = k[0] + two64 * k[1] + two_pow(129);
    let b = k[2] + two64 * k[3] + two_pow(129);
    // C = −B·u₁ = (2^129 − b)·u₁ mod n.
    let bd = Field::hint_div_rem(b, two64);
    let g = wmuln(wsubn(P129, [bd[1], bd[0], z, z]), u1);
    let q1 = wquot(rel1(a, b, r, s, z));
    let q1 = q1[0] + two64 * (q1[1] + two64 * q1[2]);
    let q2 = wquot(rel2(g, b, s, e, [z; 5]));
    let q2 = [q2[0], q2[1], q2[2], q2[3], q2[4]];
    let h1 = wcarries::<4, 3>(rel1(a, b, r, s, q1));
    let h2 = wcarries::<8, 7>(rel2(g, b, s, e, q2));
    let (rl, rh, _, xh, nl, _) = halves(r, x64(rp[0]));
    let t = Field::hint_div_rem(xh - rh, two_pow(127))[0];
    let u = Field::hint_div_rem(rl + t * nl, two_pow(128))[0];
    witness_end();
    // R: limbs, canonical, on the curve (gnark GHSA-7fx8: a hinted point is checked).
    range_check_limbs::<8, 32>(rp[0]);
    range_check_limbs::<8, 32>(rp[1]);
    on_curve_r1(rp[0], rp[1]);
    let (d, gb) = fake_glv_check_r1(r, s, e, x64(rp[0]), [a, b], g, q1, q2, h1, h2, [t, u]);

    // Table: t[0] = Q + R, t[1] = Q − R (`−R`'s y kept as `2p − y`, limbs < 2^34).
    let b2 = b2_r1();
    let mut nry = [z; 8];
    let mut l = 0usize;
    while l < 8 {
        nry[l] = b2[l] - rp[1][l];
        l += 1;
    }
    let (t0x, t0y) = ec_add_r1(qx, qy, rp[0], rp[1]);
    let (t1x, t1y) = ec_add_r1(qx, qy, rp[0], nry);
    let t = [[t0x, t0y], [t1x, t1y]];
    // Digit i adds σ(aᵢ)·t[aᵢ ⊕ bᵢ] = σ(aᵢ)·Q + σ(bᵢ)·R; aᵢ = 0 gives `y ↦ 2p − y`.
    let mut acc: Pt = pt(OH);
    let mut w = 0usize;
    while w < DIGITS {
        let i = DIGITS - 1 - w;
        let sel = muxp(xor(d[0][i], d[1][i]), t[1], t[0]);
        let mut sy = [z; 8];
        let mut l = 0usize;
        while l < 8 {
            let y = sel[1][l];
            sy[l] = b2[l] - y + d[0][i] * (y + y - b2[l]);
            l += 1;
        }
        let (x, y) = ec_double_add_r1(acc[0], acc[1], sel[0], sy);
        acc = [x, y];
        w += 1;
    }
    // C' = Σⱼ COMB[j][byte j of C] = 2C·G − 2^130·O.
    let zp: Pt = [[z; 8]; 2];
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
            let (x, y) = ec_add_r1(cacc[0], cacc[1], sel[0], sel[1]);
            [x, y]
        };
        j += 1;
    }
    // M + C' = t[0] = Q + R, compared mod p.
    let (fx, fy) = ec_add_r1(acc[0], acc[1], cacc[0], cacc[1]);
    let mut one = [z; 8];
    one[0] = Field::from(1u8);
    mul_cert_r1(fx, one, t[0][0]);
    mul_cert_r1(fy, one, t[0][1]);
}
