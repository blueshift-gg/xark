//! Affine twisted-Edwards (`a = −1`) arithmetic on Ed25519 by division certificates
//! ([`mul_cert_25519`]). The addition law is complete (`d` is not a square mod `p`,
//! Bernstein–Birkner–Joye–Lange–Peters, AFRICACRYPT 2008, Thm 3.3; proven in
//! `formal/Formal/Ed25519Curve.lean`), so no step needs a guard, an offset or a flag.
//!
//! Each operation's honest values are hints in a witness region (`ed_double`,
//! `ed_add`, …), pinned by an exported `#[gadget]` (`ed_double_check`, …) that
//! range-checks them below `2³²` limb-wise and certifies them. Every check assumes its
//! input limbs below `2³⁵` (`8 × 32`-bit limbs: a canonical value, or `4p − v` for a
//! negated one) and, where it divides, that its points are on the curve.

use crate::cert::{Fe, mul_cert_25519};
use xark::Field;
use xark_bignum::modulus_limbs;

const P_DEC: &str = "57896044618658097711785492504343953926634992332820282019728792003956564819949";
/// `p = 2²⁵⁵ − 19`.
pub(crate) const P8: Fe = modulus_limbs::<8, 32>(P_DEC);
/// `d = −121665/121666 mod p`, the curve constant.
const D8: Fe = modulus_limbs::<8, 32>(
    "37095705934669439343138083508754565189542113879843219016388785533085940283555",
);
/// `d⁻¹ mod p`: the certificate `x·y − d⁻¹·f ≡ 0` reads `f ≡ d·x·y`.
const DINV8: Fe = modulus_limbs::<8, 32>(
    "29203323570479832313932222820853031755424015489030106335172286495629888845891",
);

/// An affine point `(x, y)`.
pub type Pt = [Fe; 2];
/// A point with `f = d·x·y`, the form an addition's second operand takes.
pub type TPt = [Fe; 3];

fn zero() -> Fe {
    [Field::from(0u8); 8]
}

/// `4p` limb-wise: each limb is at least `4·(2³¹ − 1) > 2³²`, so `4p + u − v` has
/// non-negative limbs below `2³⁵` for `u, v` below `2³²`, and is `≡ u − v`.
pub(crate) fn b4() -> Fe {
    let mut out = zero();
    let mut i = 0;
    while i < 8 {
        out[i] = Field::from(4u8) * P8[i];
        i += 1;
    }
    out
}

/// `c + Σ±` limb-wise: `lin(c, &[(1, u), (−1, v)])` is `c + u − v`.
fn lin(c: Fe, terms: &[(i8, Fe)]) -> Fe {
    let mut out = c;
    let mut i = 0;
    while i < 8 {
        let mut t = 0;
        while t < terms.len() {
            let (s, v) = terms[t];
            out[i] = if s > 0 { out[i] + v[i] } else { out[i] - v[i] };
            t += 1;
        }
        i += 1;
    }
    out
}

fn small(v: u8) -> Fe {
    let mut out = zero();
    out[0] = Field::from(v);
    out
}

/// `−P`: `(4p − x, y, 4p − f)` (limbs below `2³⁵`, no rows).
pub fn neg(p: TPt) -> TPt {
    [lin(b4(), &[(-1, p[0])]), p[1], lin(b4(), &[(-1, p[2])])]
}

/// Range-check each limb below `2³²` (`to_bits::<32>`, `formal/Formal/ToBits32.lean`).
fn range32(v: Fe) {
    let mut i = 0;
    while i < 8 {
        let _ = v[i].to_bits::<32>();
        i += 1;
    }
}

/// `a·b ≡ t`.
fn cert1(a: Fe, b: Fe, t: Fe) {
    let z = zero();
    mul_cert_25519(a, b, z, z, z, z, t);
}

// ---- witness-region helpers: hints only, no rows --------------------------------
fn wmul(a: Fe, b: Fe) -> Fe {
    Field::hint_mulmod_divmod::<8>(a, b, P8, 32).1
}
fn wsub(a: Fe, b: Fe) -> Fe {
    Field::hint_sub2::<8>(a, b, zero(), P8, 32).1
}
fn winv(a: Fe) -> Fe {
    Field::hint_mod_inverse::<8>(a, P8, 32)
}

/// The rows of `on_curve`: `s`, `u` below `2³²` and `x·x ≡ s`, `y·y ≡ u`,
/// `s·u − d⁻¹·(u − s − 1) ≡ 0`, so `−x² + y² = 1 + d·x²·y² (mod p)`. Proven in
/// `formal/Formal/EdCheck.lean` on `x`, `y` limbs below `2³⁵`.
#[xark::gadget]
pub fn ed_on_curve_check(x: Fe, y: Fe, s: Fe, u: Fe) {
    range32(s);
    range32(u);
    cert1(x, x, s);
    cert1(y, y, u);
    let z = zero();
    let rhs = lin(b4(), &[(1, u), (-1, s), (-1, small(1))]);
    mul_cert_25519(s, u, DINV8, rhs, z, z, z);
}

/// Assert `(x, y)` is on Ed25519.
pub fn on_curve(x: Fe, y: Fe) {
    xark::witness_begin();
    let s = wmul(x, x);
    let u = wmul(y, y);
    xark::witness_end();
    ed_on_curve_check(x, y, s, u);
}

/// The rows of `with_f`: `f` below `2³²` and `x·y − d⁻¹·f ≡ 0`, so `f ≡ d·x·y`.
#[xark::gadget]
pub fn ed_f_check(x: Fe, y: Fe, f: Fe) {
    range32(f);
    let z = zero();
    mul_cert_25519(x, y, DINV8, f, z, z, z);
}

/// `(x, y, d·x·y)`.
pub fn with_f(p: Pt) -> TPt {
    xark::witness_begin();
    let f = wmul(D8, wmul(p[0], p[1]));
    xark::witness_end();
    ed_f_check(p[0], p[1], f);
    [p[0], p[1], f]
}

/// The rows of `double`: `s`, `u`, `x₂`, `y₂` below `2³²` and `x·x ≡ s`, `y·y ≡ u`,
/// `x₂·(u − s) − 2x·y ≡ 0`, `y₂·(2 − u + s) ≡ u + s` (differences biased by `4p`).
/// On the curve, `u − s = 1 + d·s·u` and `2 − u + s = 1 − d·s·u` are nonzero, so
/// `(x₂, y₂) = 2·(x, y)`. Proven in `formal/Formal/EdCheck.lean`.
#[xark::gadget]
pub fn ed_double_check(x: Fe, y: Fe, s: Fe, u: Fe, x2: Fe, y2: Fe) {
    range32(s);
    range32(u);
    range32(x2);
    range32(y2);
    let z = zero();
    cert1(x, x, s);
    cert1(y, y, u);
    let two_x = lin(x, &[(1, x)]);
    mul_cert_25519(x2, lin(b4(), &[(1, u), (-1, s)]), two_x, y, z, z, z);
    cert1(
        y2,
        lin(b4(), &[(1, small(2)), (-1, u), (1, s)]),
        lin(u, &[(1, s)]),
    );
}

/// `2·P` on canonical-or-negated coordinates.
pub fn double(p: Pt) -> Pt {
    let (x, y) = (p[0], p[1]);
    xark::witness_begin();
    let s = wmul(x, x);
    let u = wmul(y, y);
    let x2 = wmul(wmul(small(2), wmul(x, y)), winv(wsub(u, s)));
    let y2 = wmul(lin(u, &[(1, s)]), winv(wsub(lin(small(2), &[(1, s)]), u)));
    xark::witness_end();
    ed_double_check(x, y, s, u, x2, y2);
    [x2, y2]
}

/// The rows of `add`: `t`, `e`, `x₃`, `y₃` below `2³²` and `x₁·y₁ ≡ t`, `t·f₂ ≡ e`,
/// `x₃·(1 + e) − x₁·y₂ − y₁·x₂ ≡ 0`, `y₃·(1 − e) − y₁·y₂ − x₁·x₂ ≡ 0`. With
/// `f₂ = d·x₂·y₂` and both points on the curve, `1 ± e ≠ 0` and `(x₃, y₃) = P₁ + P₂`.
/// Proven in `formal/Formal/EdCheck.lean`.
#[xark::gadget]
#[allow(clippy::too_many_arguments)]
pub fn ed_add_check(x1: Fe, y1: Fe, x2: Fe, y2: Fe, f2: Fe, t: Fe, e: Fe, x3: Fe, y3: Fe) {
    range32(t);
    range32(e);
    range32(x3);
    range32(y3);
    let z = zero();
    cert1(x1, y1, t);
    cert1(t, f2, e);
    mul_cert_25519(x3, lin(small(1), &[(1, e)]), x1, y2, y1, x2, z);
    mul_cert_25519(y3, lin(b4(), &[(1, small(1)), (-1, e)]), y1, y2, x1, x2, z);
}

/// `P₁ + Q` for `Q = (x₂, y₂, d·x₂·y₂)`.
pub fn add(p: Pt, q: TPt) -> Pt {
    let (x1, y1) = (p[0], p[1]);
    let (x2, y2, f2) = (q[0], q[1], q[2]);
    xark::witness_begin();
    let t = wmul(x1, y1);
    let e = wmul(t, f2);
    let num_x = lin(wmul(x1, y2), &[(1, wmul(y1, x2))]);
    let num_y = lin(wmul(y1, y2), &[(1, wmul(x1, x2))]);
    let x3 = wmul(num_x, winv(lin(small(1), &[(1, e)])));
    let y3 = wmul(num_y, winv(wsub(small(1), e)));
    xark::witness_end();
    ed_add_check(x1, y1, x2, y2, f2, t, e, x3, y3);
    [x3, y3]
}

/// The rows of `torsion`: `s`, `u`, `m` below `2³²` and `x·x ≡ s`, `y·y ≡ u`,
/// `x·y ≡ m`, `m·(s + u) ≡ 0`, so `x·y·(x² + y²) ≡ 0`: on the curve, exactly the
/// points of order dividing 8 (`formal/Formal/Ed25519Curve.lean`).
#[xark::gadget]
pub fn ed_torsion_check(x: Fe, y: Fe, s: Fe, u: Fe, m: Fe) {
    range32(s);
    range32(u);
    range32(m);
    let z = zero();
    cert1(x, x, s);
    cert1(y, y, u);
    cert1(x, y, m);
    cert1(m, lin(s, &[(1, u)]), z);
}

/// Assert `8·P = O`.
pub fn torsion(p: Pt) {
    xark::witness_begin();
    let s = wmul(p[0], p[0]);
    let u = wmul(p[1], p[1]);
    let m = wmul(p[0], p[1]);
    xark::witness_end();
    ed_torsion_check(p[0], p[1], s, u, m);
}
