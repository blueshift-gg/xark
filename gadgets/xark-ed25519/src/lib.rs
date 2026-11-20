//! `xark-ed25519`: an Ed25519 (twisted-Edwards, `a = −1`) scalar-multiplication
//! and EdDSA signature-verification gadget, over the `xark` `Field` subset.
//!
//! Ed25519 lives over the base field `p = 2^255 − 19` with the curve equation
//! `−x² + y² = 1 + d·x²·y²` and group order `L`. Its ~255-bit coordinates are
//! foreign to the native BN254 proving field, so they use non-native limb arithmetic
//! from [`xark_bignum`].
//!
//! The verifier ([`PointL::verify`]) checks the cofactored EdDSA equation
//! `[8]·([S]·B − [k]·A − R) = O`, with `A` and `R` canonical and on the curve and
//! `S < L`, by division certificates and fake GLV over 8 × 32-bit limbs. The SHA-512
//! challenge `k = H(R‖A‖M)` is out of scope: `k` is an input.
//!
//! The [`xark_curve::edwards!`] macro also emits a complete twisted-Edwards group law
//! and scalar multiplication over 3 × 86-bit limbs (`Point`, [`mul_base`]); its
//! addition has no exceptional cases.

#![no_std]
// Gadget code keeps the `x = x + y` style it was written in (the old compiler
// rejected `+=` on `Field`; the wasm frontend accepts both).
#![allow(clippy::assign_op_pattern)]

use xark::{Field, input, require_eq};

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
/// the scalar field's `3 × 86`-bit limbs and require canonical. `bits` must be
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
// EdDSA verification by division certificates and fake GLV (8 × 32-bit limbs).
// ===========================================================================
mod cert;
mod curve;
#[doc(hidden)]
pub use cert::{Fe, mul_cert_25519};
#[doc(hidden)]
pub use curve::{ed_add_check, ed_double_check, ed_f_check, ed_on_curve_check, ed_torsion_check};

use curve::{Pt, TPt, add, double, neg, on_curve, torsion, with_f};
use xark::{witness_begin, witness_end};
use xark_bignum::{modulus_limbs, one_hot8, require_lt};

type L3 = [Field; 3];
type L4 = [Field; 4];

// A base-field element in the public input's 3×85-bit limb layout (distinct from the
// affine gadget's `Fp` at 3×86). Only the input-flatten wrapper, so the
// `ed25519_verify` example can take aggregate `Point` coordinates: storage only, no
// `fp!` operators; the verifier re-limbs it to 8 × 32 bits.
xark_bignum::fp!(storage pub FpL, 3, 85);
/// An Ed25519 affine point with 3×85-bit coordinates — the verifier's public
/// input type (`x`/`y` each flatten to `<name>.x.limbs[0..2]` / `<name>.y.limbs`).
#[derive(Clone, Copy, Debug)]
pub struct PointL {
    pub x: FpL,
    pub y: FpL,
}

/// A circuit input given as the compressed point (32 bytes, `0x…` in a client),
/// decompressed into `x`, `y`.
impl xark::Input for PointL {
    const TYPE: xark::input::Type = {
        use xark::input::{Bytes, Encoding, Layout, Member, Type};
        Type::Named(
            &Type::named(
                "PointL",
                Layout::fields(&[
                    Member::new("x", <FpL as xark::Input>::TYPE),
                    Member::new("y", <FpL as xark::Input>::TYPE),
                ]),
            )
            .encoded(Encoding::Bytes(Bytes::Ed25519)),
        )
    };
    fn read(r: &mut xark::input::Reader<'_>) -> Self {
        PointL {
            x: r.read(),
            y: r.read(),
        }
    }
    fn write(&self, w: &mut xark::input::Writer<'_>) {
        w.write(&self.x);
        w.write(&self.y);
    }
}

/// The group order `L` (4 × 64-bit limbs).
const LL: L4 = modulus_limbs::<4, 64>(
    "7237005577332262213973186563042994240857116359379907606001950938285454250989",
);
/// `L⁻¹ mod r` (BN254's scalar field): the witness region's exact quotients.
const LINV: Field = Field::constant(
    "13190247080771224628580549526763007273965312965423810974879048037356625225145",
);
/// `2¹²⁹ mod L`.
const TWO129: L4 = modulus_limbs::<4, 64>("680564733841876926926749214863536422912");
/// Windows of two digit bits per coefficient: `cₘ = kₘ + 2¹²⁹ < 2¹³⁰`.
const WINDOWS: usize = 65;

// `COMB`: the fixed-base comb tables (`build.rs`).
include!(concat!(env!("OUT_DIR"), "/comb.rs"));

fn f0() -> Field {
    Field::from(0u8)
}
fn pow2(e: u32) -> Field {
    cert::pow2(e)
}

/// `Σᵢ 2ⁱ·bits[o + i]` for `i < n`.
fn recompose(bits: &[Field], o: usize, n: usize) -> Field {
    let mut acc = f0();
    let mut i = n;
    while i > 0 {
        i -= 1;
        acc = acc + acc + bits[o + i];
    }
    acc
}

/// A coordinate's 3 × 85-bit public limbs as 8 × 32-bit limbs, by the bits of each
/// limb (`to_bits::<85>`, which also bounds the limbs below `2⁸⁵`).
fn limbs32(x: L3) -> Fe {
    let mut bits = [f0(); 256];
    let mut l = 0;
    while l < 3 {
        let b = x[l].to_bits::<85>();
        let mut i = 0;
        while i < 85 {
            bits[85 * l + i] = b[i];
            i += 1;
        }
        l += 1;
    }
    let mut out = [f0(); 8];
    let mut j = 0;
    while j < 8 {
        out[j] = recompose(&bits, 32 * j, 32);
        j += 1;
    }
    out
}

/// A public point: limbs below `2⁸⁵`, canonical coordinates (`< p`, so each point has
/// one accepted encoding) and on the curve.
fn point_in(x: L3, y: L3) -> Pt {
    let p = [limbs32(x), limbs32(y)];
    require_lt::<3, 85>(x, xark_bignum::P1_25519_L);
    require_lt::<3, 85>(y, xark_bignum::P1_25519_L);
    on_curve(p[0], p[1]);
    p
}

/// 256 bits as 4 × 64-bit limbs.
fn limbs64(bits: [Field; 256]) -> L4 {
    [
        recompose(&bits, 0, 64),
        recompose(&bits, 64, 64),
        recompose(&bits, 128, 64),
        recompose(&bits, 192, 64),
    ]
}

// ---- the scalar relation -----------------------------------------------------------
/// The base-`2⁶⁴` columns of `a + k·b − q·L` (`a` up to four limbs, `b` and `q` three,
/// signed): six columns.
fn rel_cols(a: L4, k: L4, b: L3, q: L3) -> [Field; 6] {
    let mut out = [f0(); 6];
    let mut m = 0;
    while m < 4 {
        out[m] = a[m];
        m += 1;
    }
    let mut i = 0;
    while i < 4 {
        let mut j = 0;
        while j < 3 {
            out[i + j] = out[i + j] + k[i] * b[j] - q[j] * LL[i];
            j += 1;
        }
        i += 1;
    }
    out
}

/// The biased carries `c_m + 2⁶⁷` of `Σ cols[m]·2^(64m) = 0` (witness region).
fn wcarries(cols: [Field; 6]) -> [Field; 5] {
    let mut out = [f0(); 5];
    let mut carry = f0();
    let mut m = 0;
    while m < 5 {
        out[m] = Field::hint_div_rem(cols[m] + carry + pow2(131), pow2(64))[0];
        carry = out[m] - pow2(67);
        m += 1;
    }
    out
}

/// Assert `Σ cols[m]·2^(64m) = 0` over the integers: the carries `c_m = h_m − 2⁶⁷`,
/// `h_m < 2⁶⁸`, satisfy `cols[m] + c_{m−1} = 2⁶⁴·c_m`, and the last column closes.
fn zero_chain(cols: [Field; 6], h: [Field; 5]) {
    let mut carry = f0();
    let mut m = 0;
    while m < 6 {
        let v = cols[m] + carry;
        if m < 5 {
            let _ = h[m].to_bits::<68>();
            carry = h[m] - pow2(67);
            require_eq(v, pow2(64) * carry);
        } else {
            require_eq(v, f0());
        }
        m += 1;
    }
}

/// A coefficient's limbs `[c₀, c₁, c₂ − 2]` (`c − 2¹²⁹`) from its 130 bits.
fn signed3(bits: &[Field; 130]) -> L3 {
    [
        recompose(bits, 0, 64),
        recompose(bits, 64, 64),
        recompose(bits, 128, 2) - Field::from(2u8),
    ]
}

/// The fake-GLV scalar checks of `eddsa_verify` (ePrint 2025/933, two-dimensional:
/// Ed25519 has no cheap endomorphism). Inputs: `k` and `S` (4 × 64-bit limbs, below
/// `2⁶⁴` by the caller's bits), the hinted `c_A = A + 2¹²⁹`, `c_B = B + 2¹²⁹`, `W`, the
/// quotients `q₁ + 2¹³³`, `q₂ + 2¹³³` (limbs) and the biased carries of the two chains.
/// Rows: `c_A`, `c_B < 2¹³⁰` (`to_bits`, whose bits it returns as the loop's digits), `W`'s
/// limbs `< 2⁶⁴` (its 256 bits, the comb's), the quotient limbs `< 2⁶⁴, 2⁶⁴, 2⁶`,
/// `B ≠ 0` (`B·w = 1`), and the integer identities `A + k·B = q₁·L`,
/// `W + S·B = q₂·L` (columns in base `2⁶⁴`, carries `< 2⁶⁸` biased by `2⁶⁷`). Proven in
/// `formal/Formal/FakeGlv25519.lean`: every satisfying assignment has
/// `A + k·B ≡ W + S·B ≡ 0 (mod L)` with `0 < |B| < 2¹²⁹`, and returns those bits.
#[xark::gadget]
#[allow(clippy::too_many_arguments)]
pub fn fake_glv_check_25519(
    k: L4,
    s: L4,
    ca: Field,
    cb: Field,
    w: L4,
    q1: L3,
    q2: L3,
    h1: [Field; 5],
    h2: [Field; 5],
) -> ([Field; 130], [Field; 130], [Field; 256]) {
    let da = ca.to_bits::<130>();
    let db = cb.to_bits::<130>();
    let mut wb = [f0(); 256];
    let mut i = 0;
    while i < 4 {
        let b = w[i].to_bits::<64>();
        let mut j = 0;
        while j < 64 {
            wb[64 * i + j] = b[j];
            j += 1;
        }
        i += 1;
    }
    let qs = [q1, q2];
    let mut i = 0;
    while i < 2 {
        let _ = qs[i][0].to_bits::<64>();
        let _ = qs[i][1].to_bits::<64>();
        let _ = qs[i][2].to_bits::<6>();
        i += 1;
    }
    let _ = (cb - pow2(129)).inv();
    let a = signed3(&da);
    let b = signed3(&db);
    let off = |q: L3| [q[0], q[1], q[2] - Field::from(32u8)];
    zero_chain(rel_cols([a[0], a[1], a[2], f0()], k, b, off(q1)), h1);
    zero_chain(rel_cols(w, s, b, off(q2)), h2);
    (da, db, wb)
}

// ---- the group side ------------------------------------------------------------------
fn xor(a: Field, b: Field) -> Field {
    a + b - Field::from(2u8) * a * b
}

#[xark::gadget]
#[doc(hidden)]
pub fn mux(s: Field, a: TPt, b: TPt) -> TPt {
    let mut out = b;
    let mut c = 0;
    while c < 3 {
        let mut l = 0;
        while l < 8 {
            out[c][l] = b[c][l] + s * (a[c][l] - b[c][l]);
            l += 1;
        }
        c += 1;
    }
    out
}

/// `t[i₀ + 2i₁ + 4i₂]` by a mux tree over the three index bits.
fn select8(t: [TPt; 8], i0: Field, i1: Field, i2: Field) -> TPt {
    let a = [
        mux(i0, t[1], t[0]),
        mux(i0, t[3], t[2]),
        mux(i0, t[5], t[4]),
        mux(i0, t[7], t[6]),
    ];
    mux(i2, mux(i1, a[3], a[2]), mux(i1, a[1], a[0]))
}

/// `P` if `s = 1`, `−P` if `s = 0` (`x`, `f` ↦ `4p − x`, `4p − f`).
fn signed(s: Field, p: TPt) -> TPt {
    let n = neg(p);
    let mut out = p;
    let mut c = 0;
    while c < 3 {
        let mut l = 0;
        while l < 8 {
            out[c][l] = n[c][l] + s * (p[c][l] - n[c][l]);
            l += 1;
        }
        c += 1;
    }
    out
}

/// `C'' = [2W·4⁻⁶⁵]·G` by the comb: window `j` adds `COMB[j][byte j of W]`
/// (`one_hot8` over the constant table; Lim–Lee, CRYPTO 1994), 31 additions.
fn comb(wb: [Field; 256]) -> Pt {
    let mut acc: Pt = [[f0(); 8]; 2];
    let mut j = 0;
    while j < 32 {
        let mut bits = [f0(); 8];
        let mut l = 0;
        while l < 8 {
            bits[l] = wb[8 * j + l];
            l += 1;
        }
        let hot = one_hot8(bits);
        let mut sel: TPt = [[f0(); 8]; 3];
        let mut v = 0;
        while v < 256 {
            let c = &COMB[j][v];
            let mut l = 0;
            while l < 24 {
                sel[l / 8][l % 8] = sel[l / 8][l % 8] + hot[v] * Field::from(c[l]);
                l += 1;
            }
            v += 1;
        }
        acc = if j == 0 {
            [sel[0], sel[1]]
        } else {
            add(acc, sel)
        };
        j += 1;
    }
    acc
}

/// The building blocks of `eddsa_verify`, wrapped for the block-level soundness
/// test (`signature_blocks_are_sound` in `crates/lang/tests/snapshot.rs`). Not API.
#[doc(hidden)]
pub mod blocks {
    use super::{Field, L3};
    pub fn point_in(x: L3, y: L3) {
        let _ = super::point_in(x, y);
    }
    pub fn scalar_below_order(bits: [Field; 256]) {
        super::assert_scalar_below_order(bits)
    }
}

/// An Ed25519 signature `(R, S)` — a curve point `R` (compressed `[u8; 32]` on the
/// host) and a scalar `S`. Its `#[input]` with `#[input(bytes)]` takes
/// `R`'s (decompressing) bytes then `S`'s, so on the host it comes from a `[u8; 64]`:
/// compressed `R ‖ big-endian S`. Pass it to [`PointL::verify`].
#[input(bytes)]
pub struct Signature {
    pub r: PointL,
    pub s: Scalar,
}

/// Everything to write an Ed25519 circuit in one import:
/// `use xark_ed25519::prelude::*;` re-exports the `xark` essentials (`circuit`,
/// `Public`, `Field`, `require_eq`, …) plus the transparent input types [`PointL`],
/// [`Signature`], [`Scalar`]. Verify with `pubkey.verify(sig, digest)`.
pub mod prelude {
    pub use crate::{PointL, Scalar, Signature};
    pub use xark::prelude::*;
}

impl PointL {
    /// Verify an Ed25519 signature against this public key `A` and the challenge
    /// `digest = k = H(R ‖ A ‖ M) mod L` (a [`Scalar`]). Checks the cofactored EdDSA
    /// equation `[8]·([S]·B − [k]·A − R) = O`. The transparent-type entry point — no limbs:
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

/// Ed25519 signature verification core: the cofactored EdDSA equation
/// `[8]·([S]·B − [k]·A − R) = O`, with `A`, `R` canonical and on the curve and `S < L`.
/// Wrapped by [`PointL::verify`], the public entry: it takes the transparent
/// [`Signature`] and decomposes the scalars to pinned bits — `s_bits`/`k_bits` here are
/// assumed boolean.
///
/// By fake GLV (Eagen–El Housni–Masson–Piellard, ePrint 2025/933): the prover hints a
/// short `(A, B)` with `A + k·B ≡ 0 (mod L)`, `0 < |B| < 2¹²⁸` (the lattice hint with
/// `λ = 2⁶⁴`, so `A = a₀ + 2⁶⁴a₁`) and `W ≡ −B·S`; [`fake_glv_check_25519`] pins them.
/// Then `B·([S]B − [k]A − R) = −[W]G + [A]·A − [B]·R` (here `G` is the base point), and
/// since `B ≢ 0 (mod L)` and `[8]·(…)` lies in the order-`L` subgroup, the circuit checks
/// `[8]·X = O` for `−2X = [2W]G + M − (P_A + P_B)`, `P_A = −A`, `P_B = R`, where
/// `M = Σ_w 4^w·(d_A,w·P_A + d_B,w·P_B) + 4⁶⁵·C''` is 65 steps (two doublings and an
/// add) over the odd digits `d = 2·(2b₁ + b₀) − 3 ∈ {±1, ±3}` of `c_A`, `c_B` (so the
/// digit sums are `2A + 1`, `2B + 1`), each reading an 8-entry table `{1,3}·P_A ±
/// {1,3}·P_B` (negated for a negative `d_A`), seeded with the comb's
/// `C'' = [2W·4⁻⁶⁵]G`. Twisted-Edwards addition is complete, so no input is refused:
/// every valid signature verifies.
fn eddsa_verify(ax: L3, ay: L3, rx: L3, ry: L3, s_bits: [Field; 256], k_bits: [Field; 256]) {
    // canonical scalar S < L (else S, S+L, … all verify — EdDSA malleability)
    assert_scalar_below_order(s_bits);
    let a = point_in(ax, ay);
    let r = point_in(rx, ry);
    let k = limbs64(k_bits);
    let s = limbs64(s_bits);
    let z4 = [f0(); 4];
    // The whole fake-GLV witness costs no rows; `fake_glv_check_25519` pins it.
    witness_begin();
    let one = [Field::from(1u8), f0(), f0(), f0()];
    let kr = Field::hint_mulmod_divmod::<4>(k, one, LL, 64).1;
    let u = Field::hint_sub2::<4>(z4, kr, z4, LL, 64).1;
    let v = Field::hint_fake_glv::<4>(u, LL, [f0(), Field::from(1u8), f0(), f0()], 64);
    let ca = v[0] + pow2(64) * v[1] + pow2(129);
    let cb = v[2] + pow2(64) * v[3] + pow2(129);
    // W = −B·S mod L, from c_B's limbs.
    let lo = Field::hint_div_rem(cb, pow2(64));
    let hi = Field::hint_div_rem(lo[0], pow2(64));
    let bm = Field::hint_sub2::<4>([lo[1], hi[1], hi[0], f0()], TWO129, z4, LL, 64).1;
    let bs = Field::hint_mulmod_divmod::<4>(bm, s, LL, 64).1;
    let w = Field::hint_sub2::<4>(z4, bs, z4, LL, 64).1;
    // Exact quotients in Fr (|q| < 2¹³³ ≪ r), shifted by 2¹³³, as 64-bit limbs.
    let fe = |x: L4| x[0] + pow2(64) * x[1] + pow2(128) * x[2] + pow2(192) * x[3];
    let bf = cb - pow2(129);
    let split = |q: Field| {
        let a = Field::hint_div_rem(q, pow2(64));
        let b = Field::hint_div_rem(a[0], pow2(64));
        [a[1], b[1], b[0]]
    };
    let q1 = split((ca - pow2(129) + fe(k) * bf) * LINV + pow2(133));
    let q2 = split((fe(w) + fe(s) * bf) * LINV + pow2(133));
    let limbs = |c: Field| {
        let q = split(c);
        [q[0], q[1], q[2] - Field::from(2u8)]
    };
    let off = |q: L3| [q[0], q[1], q[2] - Field::from(32u8)];
    let al = limbs(ca);
    let h1 = wcarries(rel_cols([al[0], al[1], al[2], f0()], k, limbs(cb), off(q1)));
    let h2 = wcarries(rel_cols(w, s, limbs(cb), off(q2)));
    witness_end();
    let (da, db, wb) = fake_glv_check_25519(k, s, ca, cb, w, q1, q2, h1, h2);

    // The table over P_A = −A, P_B = R: entry i₀ + 2β' is (1 + 2i₀)·P_A + (2β' − 3)·P_B.
    let pa = neg(with_f(a));
    let pb = with_f(r);
    let p3a = add(double([pa[0], pa[1]]), pa);
    let p3b = with_f(add(double(r), pb));
    let ma = [[pa[0], pa[1]], p3a];
    let mb = [neg(p3b), neg(pb), pb, p3b];
    let mut t: [TPt; 8] = [[[f0(); 8]; 3]; 8];
    let mut i = 0;
    while i < 8 {
        t[i] = with_f(add(ma[i & 1], mb[i >> 1]));
        i += 1;
    }
    // Window w adds d_A·P_A + d_B·P_B = σ·t[i₀ + 2β'], σ the sign of d_A.
    let mut acc = comb(wb);
    let mut w = WINDOWS;
    while w > 0 {
        w -= 1;
        acc = double(double(acc));
        let (a0, a1) = (da[2 * w], da[2 * w + 1]);
        let one = Field::from(1u8);
        let sel = select8(
            t,
            one - xor(a0, a1),
            one - xor(db[2 * w], a1),
            one - xor(db[2 * w + 1], a1),
        );
        acc = add(acc, signed(a1, sel));
    }
    // −2X = M − (P_A + P_B), P_A + P_B = t[4]; X must have order dividing 8.
    torsion(add(acc, neg(t[4])));
}

/// Host-side conversions + EdDSA helpers, behind the `host` feature. Ed25519
/// points are natively **compressed** (32-byte little-endian `y` + `x`-sign bit);
/// these recover the affine `(x, y)` per RFC 8032 §5.1.3 so the circuit's
/// transparent types take the exact bytes `ed25519-dalek` emits. Signatures use
/// **little-endian** scalars, so `S`/`k` are byte-reversed to the big-endian form
/// the macro-generated `Fq`'s host conversions expect.
#[cfg(not(xark))]
mod host {
    extern crate std;
    use super::PointL;
    use num_bigint::BigUint;
    use sha2::{Digest, Sha512};

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
        // Decoded as RFC 8032 §5.1.3 does: `y ≥ p`, a `y` with no `x`, and `x = 0` with
        // the sign bit set are refused, so every point has one encoding.
        let y = BigUint::from_bytes_le(&yb);
        assert!(y < p, "not an Ed25519 point: y ≥ p");
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
        assert!(
            (&v * (&x * &x % &p)) % &p == u,
            "not an Ed25519 point: no x for this y"
        );
        assert!(
            !(x.bits() == 0 && sign == 1),
            "not an Ed25519 point: x = 0 with the sign bit set"
        );
        if (x.bit(0) as u8) != sign {
            x = (&p - &x) % &p;
        }
        (x, y)
    }

    impl xark::host::FromBeBytes for PointL {
        const BYTES: usize = 32;
        /// From the compressed point (`y` little-endian with the `x`-sign bit),
        /// decompressed to affine `(x, y)`. Panics if it isn't a curve point.
        fn from_be_bytes(bytes: &[u8]) -> PointL {
            let (x, y) = decompress(bytes.try_into().expect("a compressed point is 32 bytes"));
            let limbs = |v: &BigUint| super::FpL::new(xark::host::limb_fields::<3>(&be32(v), 85));
            PointL {
                x: limbs(&x),
                y: limbs(&y),
            }
        }
    }

    /// From an Ed25519 public key or `R`: the 32-byte compressed point.
    impl From<[u8; 32]> for PointL {
        fn from(bytes: [u8; 32]) -> PointL {
            <PointL as xark::host::FromBeBytes>::from_be_bytes(&bytes)
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

    // --- affine twisted-Edwards arithmetic (host, for the ed25519 vectors) ---

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
