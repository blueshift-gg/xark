//! `xark-grumpkin`: native-field **Grumpkin** elliptic-curve gadgets in the
//! `xark` `Field` subset — embedded-curve point addition and
//! multi-scalar multiplication as native-field gadgets.
//!
//! ## Why Grumpkin is native (the key insight)
//!
//! Grumpkin and BN254 form a 2-cycle: Grumpkin's **base field** is exactly
//! BN254's **scalar field**
//! `r = 21888242871839275222246405745257275088548364400416034343698204186575808495617`,
//! which is precisely `xark`'s native `Field`. So a Grumpkin point's
//! coordinates are ordinary `Field` values and **all elliptic-curve arithmetic
//! is native `Field` `+ - *`** (plus `Field::hint_inverse` for the affine slope
//! division) — no non-native limbs, no `mod_mul`. Grumpkin short-Weierstrass
//! form: `y² = x³ - 17`  (`a = 0`, `b = -17`).
//!
//! ## Gadgets
//!
//! * [`ec_add`] / [`ec_double`] — incomplete affine addition / doubling
//!   (both operands are witness points).
//! * [`scalar_mul`] / [`wide_scalar_mul`] — **variable-base** scalar
//!   multiplication `m · P` where `P` is a *witness* point (no precomputed
//!   multiples): one fused double-and-add step per bit.
//! * [`multi_scalar_mul`] — `s₀·P₀ + s₁·P₁`, one fused step per bit pair from a
//!   shared table `±(P₀ + P₁)`, `±(P₀ − P₁)`.
//!
//! ## Offset accumulator with signed digits
//!
//! Incomplete affine addition cannot represent the point at infinity. To keep
//! every intermediate off `∞` the accumulator starts at a fixed offset `O`, and
//! each step adds a signed digit `±P` (no point mux):
//!
//! ```text
//!   acc = (O + P) + O                    // top digit +1
//!   for i in N-1 .. 1  (MSB first):
//!       acc = (acc ± P) + acc            // + for bitᵢ = 1, − for 0 (dbl_add)
//!   result = acc + (bit₀ ? corr : corr − P)
//! ```
//!
//! After the loop `acc = 2^N·O + (m − bit₀ + 1)·P`, so the last add of the
//! compile-time constant `corr = −(2^N·O)` (or `corr − P`) yields `m·P`.
//! `formal/Formal/GrumpkinMul.lean` certifies `corr` (and `corr254`) in the
//! kernel by a chain of tangent slopes from `O`.
//!
//! ## Soundness / completeness
//!
//! Each add's first slope is pinned by a guard `denom · inv == 1`, unsatisfiable
//! at `x1 == x2`, so a malicious prover can never forge a result at an edge. The
//! fused step's second slope `λ2` has no guard of its own: its row
//! `(λ1 + λ2)·(x_A − x_R) = 2·y_A` cannot hold at `x_A = x_R` because Grumpkin has
//! no point with `y = 0` (`formal/Formal/DoubleAdd.lean`). An honest prover fails
//! when the result is the identity (`m·P = 0`, e.g. `m = 0`, or a wide scalar equal
//! to the group order), on `multi_scalar_mul`'s `P₀ = ±P₁` (no table), and otherwise
//! only on inputs that land on an incomplete-addition edge, which needs `O`'s
//! discrete log.
//!
//! ## Scalar range / bit-length
//!
//! `N_BITS = 128`: scalars are decomposed into 128 pinned little-endian bits.
//! Because `2^128 < r`, the decomposition is *injective* (analyzer-clean, no
//! non-canonical-decomposition malleability). Raising `N_BITS` toward 252
//! (full-field scalars) is a one-line change plus regenerating the single
//! `corr` constant (`corr` depends on `N_BITS`).

#![no_std]
// Gadget code keeps the `x = x + y` style it was written in (the old compiler
// rejected `+=` on `Field`; the wasm frontend accepts both).
#![allow(clippy::assign_op_pattern)]

use xark::{Field, gadget, input, require_eq, select, witness_begin, witness_end};

pub mod schnorr;

/// Scalar bit-length (see module docs). Kept in sync with the `128usize` loop
/// literals below (loop bounds must be integer literals in the subset).
pub const N_BITS: usize = 128;

/// Number of `(scalar, point)` pairs summed by [`multi_scalar_mul`].
pub const K: usize = 2;

// ===========================================================================
// Curve constants. `O` is a fixed on-curve non-identity Grumpkin point (x = 5);
// `corr = -(2^N_BITS · O)`, certified by `formal/Formal/GrumpkinMul.lean`.
// ===========================================================================

/// Offset-accumulator seed `O` (fixed non-identity point, `x = 5`).
fn offset() -> [Field; 2] {
    [
        Field::from(5u8),
        Field::from("26447525821777463057023244913909144251512587297343525263882"),
    ]
}

/// Offset correction `corr = -(2^N_BITS · O)`, added at the end of each
/// scalar-mul to remove the accumulated offset. Compile-time constant because
/// `O` and `N_BITS` are.
fn corr() -> [Field; 2] {
    [
        Field::from(
            "15091588220200540439587434062098309947749547413125795808386331904279218024383",
        ),
        Field::from("9700730252355689723080387012214398702149611734773390356605491655538683087420"),
    ]
}

// ===========================================================================
// Native Grumpkin affine EC ops (a = 0). Incomplete: assume non-identity,
// non-colliding inputs (guaranteed by the offset accumulator + nonzero scalars).
// ===========================================================================

/// Incomplete affine point addition `P + Q` (`P ≠ ±Q`, neither `∞`).
/// `λ = (y2 - y1)/(x2 - x1)`, `x3 = λ² - x1 - x2`, `y3 = λ(x1 - x3) - y1`.
///
/// General embedded-curve point addition: both operands are witness points.
pub fn ec_add(p: [Field; 2], q: [Field; 2]) -> [Field; 2] {
    let one = Field::from(1u8);
    let dx = q[0] - p[0];
    let inv = Field::hint_inverse(dx); // witness-gen: inv = 1/dx
    require_eq(dx * inv, one); // pins dx ≠ 0 (edge ⇒ unsatisfiable)
    let lam = (q[1] - p[1]) * inv;
    let x3 = lam * lam - p[0] - q[0];
    let y3 = lam * (p[0] - x3) - p[1];
    [x3, y3]
}

/// Incomplete affine point doubling `2·P` (`P ≠ ∞`, `y ≠ 0`, `a = 0`).
/// `λ = 3x²/(2y)`, `x3 = λ² - 2x`, `y3 = λ(x - x3) - y`.
pub fn ec_double(p: [Field; 2]) -> [Field; 2] {
    let one = Field::from(1u8);
    let two = Field::from(2u8);
    let three = Field::from(3u8);
    let x = p[0];
    let y = p[1];
    let two_y = two * y;
    let inv = Field::hint_inverse(two_y); // witness-gen: inv = 1/(2y)
    require_eq(two_y * inv, one); // pins 2y ≠ 0 (edge ⇒ unsatisfiable)
    let lam = three * x * x * inv;
    let x3 = lam * lam - two * x;
    let y3 = lam * (x - x3) - y;
    [x3, y3]
}

/// Fused incomplete double-and-add `(A + S) + A` (Orchard's `DoubleAndAdd`; halo2 book
/// `var-base-scalar-mul.md` L79-140 @ 3442dd3; arkworks `double_and_add_unchecked`):
/// `R = A + S` is never materialised, only `x_R` through `λ1`. Six rows:
///
/// ```text
///   (x_A − x_S)·w = 1                    guard: A ≠ ±S (a 0/0 slope would leave λ1 free)
///   (y_A − y_S)·w = λ1                   λ1 = slope(A, S)
///   λ1·λ1 = λ1²                          x_R = λ1² − x_A − x_S
///   (λ1 + λ2)·(x_A − x_R) = 2·y_A        λ2 = slope(R, A); unsatisfiable at x_A = x_R
///                                        because y_A ≠ 0 (Grumpkin has no 2-torsion)
///   λ2·λ2 = λ2²                          x' = λ2² − x_R − x_A
///   λ2·(x_A − x') = y' + y_A             y' (a hinted variable)
/// ```
///
/// Proven over the exported rows in `formal/Formal/DoubleAdd.lean` (any short
/// Weierstrass curve with `a₁ = a₂ = a₃ = 0`, so ticket 04 can reuse it).
fn dbl_add(a: [Field; 2], s: [Field; 2]) -> [Field; 2] {
    let dx = a[0] - s[0];
    let w = Field::hint_inverse(dx);
    require_eq(dx * w, Field::from(1u8));
    let l1 = (a[1] - s[1]) * w;
    let xr = l1 * l1 - a[0] - s[0];
    witness_begin();
    let l2 = (a[1] + a[1]) * Field::hint_inverse(a[0] - xr) - l1;
    witness_end();
    require_eq((l1 + l2) * (a[0] - xr), a[1] + a[1]);
    let x = l2 * l2 - xr - a[0];
    [x, mul_add(l2, a[0] - x, -a[1])]
}

/// `a·b + c` as one fresh variable, pinned by the row `a·b = it − c`. The rows that
/// read it then see one variable instead of `c`'s terms (in a chain of steps, the
/// alternating sum of every earlier step's products). `1/(1/v)` is two hints and no
/// row.
fn mul_add(a: Field, b: Field, c: Field) -> Field {
    witness_begin();
    let inv = Field::hint_inverse_or_zero(a * b + c);
    witness_end();
    let it = Field::hint_inverse_or_zero(inv);
    require_eq(a * b, it - c);
    it
}

/// `−p`.
fn neg(p: [Field; 2]) -> [Field; 2] {
    [p[0], -p[1]]
}

// ===========================================================================
// Scalar decomposition + variable-base scalar multiplication.
// ===========================================================================

/// Decompose `x` into `N_BITS` little-endian bits, boolean-constrained and
/// pinned to `x` by recomposition (`Σ bits[i]·2^i == x`). Because
/// `2^N_BITS < r`, this uniquely determines the bits (injective), so a cheating
/// prover cannot supply a non-canonical decomposition.
pub fn decompose(x: Field) -> [Field; N_BITS] {
    let mut bits = [Field::from(0u8); N_BITS];
    let mut i = 0usize;
    while i < 128usize {
        bits[i] = Field::hint_bit(x, i); // witness-gen: bits[i] = bit(x, i)
        i += 1;
    }
    let mut i = 0usize;
    while i < 128usize {
        bits[i].require_bool();
        i += 1;
    }
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 128usize {
        acc = acc + bits[i] * pow;
        pow = pow + pow; // double: stays a compile-time constant (no gate)
        i += 1;
    }
    require_eq(acc, x);
    bits
}

/// Assert the affine point `p = (x, y)` lies on the Grumpkin curve `y² = x³ − 17`.
pub fn enforce_on_curve(p: [Field; 2]) {
    let x = p[0];
    let y = p[1];
    require_eq(y * y, x * x * x - Field::from(17u8));
}

/// `s·p` from the little-endian bits of `s` (`bit(i)`, `i < n`): the fused step over
/// the signed digits `+1, ±1 (bit n−1), …, ±1 (bit 1)` from the offset `O` gives
/// `acc = 2ⁿ·O + (s − bit(0) + 1)·p`; the last add of `q = corr` (bit 0 set) or
/// `corr − p` removes both, with `corr = −2ⁿ·O`. A signed digit `±p` is
/// `(x_p, (2·bit − 1)·y_p)`, one row and no point mux. The caller pins each `bit(i)`
/// boolean: a non-boolean bit lets the prover choose the output.
fn signed_mul(
    bit: impl Fn(usize) -> Field,
    n: usize,
    p: [Field; 2],
    corr: [Field; 2],
) -> [Field; 2] {
    let one = Field::from(1u8);
    let mut acc = dbl_add(offset(), p);
    let mut i = n - 1;
    while i > 0 {
        let b = bit(i);
        acc = dbl_add(acc, [p[0], (b + b - one) * p[1]]);
        i -= 1;
    }
    ec_add(acc, select(bit(0), corr, ec_add(corr, neg(p))))
}

/// **Variable-base** scalar multiplication `m · p`. `bits` is the little-endian
/// decomposition of `m`; each bit is pinned boolean here (one row per bit, even
/// when the caller already proved it a bit). `p` is a *witness* Grumpkin point,
/// pinned to the curve here. Returns the affine point `m · p`; rejects `m = 0` (no
/// affine result) and the inputs that make an incomplete add exceptional (`p = ±O`,
/// `p = ±corr`, or an accumulator colliding with `±p`), which an honest prover
/// hits only by choosing `p` from `O`'s discrete log. Eight rows per bit.
#[gadget]
pub fn scalar_mul(bits: [Field; N_BITS], p: [Field; 2]) -> [Field; 2] {
    enforce_on_curve(p);
    let mut i = 0usize;
    while i < 128usize {
        bits[i].require_bool();
        i += 1;
    }
    signed_mul(|i| bits[i], N_BITS, p, corr())
}

/// **Multi-scalar multiplication** `s₀·P₀ + s₁·P₁` over a shared table (halo2 book
/// `var-base-scalar-mul.md` L79-140 @ 3442dd3): `U = P₀ + P₁` and `V = P₀ − P₁`,
/// so one fused step per bit adds `±U` (bits equal) or `±V` (bits differ) for both
/// scalars at once. Each scalar is decomposed here (`< 2^N_BITS`) and each point
/// pinned to the curve. Rejects `P₀ = ±P₁` (no table), and as [`scalar_mul`] an
/// all-zero result or an exceptional incomplete add. Ten rows per bit pair.
#[gadget]
pub fn multi_scalar_mul(scalars: [Field; K], points: [[Field; 2]; K]) -> [Field; 2] {
    let one = Field::from(1u8);
    let [p0, p1] = points;
    enforce_on_curve(p0);
    enforce_on_curve(p1);
    let b0 = decompose(scalars[0]);
    let b1 = decompose(scalars[1]);
    // `U` and `V` share the guard `x₀ ≠ x₁` and its inverse.
    let dx = p1[0] - p0[0];
    let w = Field::hint_inverse(dx);
    require_eq(dx * w, one);
    let lu = (p1[1] - p0[1]) * w;
    // `x_U` and each step's addend `x` are fresh variables (`mul_add`), so every
    // step's rows have the same shape.
    let xu = mul_add(lu, lu, -p0[0] - p1[0]);
    let u = [xu, lu * (p0[0] - xu) - p0[1]];
    let lv = (-p1[1] - p0[1]) * w;
    let xv = lv * lv - p0[0] - p1[0];
    let v = [xv, lv * (p0[0] - xv) - p0[1]];
    let mut acc = dbl_add(offset(), u);
    let mut i = N_BITS - 1;
    while i > 0 {
        let (k0, k1) = (b0[i], b1[i]);
        let both = k0 * k1;
        let sel = one - k0 - k1 + both + both;
        let tx = mul_add(sel, u[0] - v[0], v[0]);
        let ty = v[1] + sel * (u[1] - v[1]);
        acc = dbl_add(acc, [tx, (k0 + k0 - one) * ty]);
        i -= 1;
    }
    // acc = 2^N·O + (s₀ − a + 1)·P₀ + (s₁ − b + 1)·P₁ for the low bits a, b.
    let (a, b) = (b0[0], b1[0]);
    let c = corr();
    let q = select(
        b,
        select(a, c, ec_add(c, neg(p0))),
        select(a, ec_add(c, neg(p1)), ec_add(c, neg(u))),
    );
    ec_add(acc, q)
}

/// A Grumpkin affine point as two native `Field` coordinates. Grumpkin's base
/// field is exactly BN254's scalar field (the circuit `Field`), so a point needs
/// no non-native limbs — `x`/`y` are ordinary field elements. Flattens to the
/// leaves `<name>.x` / `<name>.y`.
#[input]
pub struct Affine {
    pub x: Field,
    pub y: Field,
}

/// Host side: an [`Affine`] value from its two coordinates, `(x, y)` of anything
/// that converts to a `Field` (an `ark_bn254::Fr` — Grumpkin's base field — an
/// integer, a decimal / `0x`-hex string).
#[cfg(not(xark))]
mod host {
    use super::Affine;
    use xark::Field;

    impl<X: Into<Field>, Y: Into<Field>> From<(X, Y)> for Affine {
        fn from((x, y): (X, Y)) -> Affine {
            Affine {
                x: x.into(),
                y: y.into(),
            }
        }
    }
}
// ===========================================================================
// Structured inputs: a folding instance and a full-width scalar.
// ===========================================================================

/// A committed relaxed-R1CS (Nova) instance: commitments to the witness `W` and
/// the error `E`, the slack `u` and the public `x`. Flattens (and so hashes, via
/// `to_fields`) as `[cw.x, cw.y, ce.x, ce.y, u, x]`.
#[input]
pub struct Instance {
    pub cw: Affine,
    pub ce: Affine,
    pub u: Field,
    pub x: Field,
}

/// A full-width Grumpkin scalar (`< 2^254`, so it can exceed the circuit field)
/// as two 127-bit limbs, `lo + hi·2^127`, both below the field, so the split is
/// injective. On the host it comes from the whole number (a decimal / `0x`-hex
/// string, its 32 big-endian bytes, an integer); see [`wide_scalar_mul`].
#[input(number(bits = 127))]
pub struct WideScalar {
    /// `[lo, hi]`.
    pub limbs: [Field; 2],
}

/// `corr₂₅₄ = −(2^254·O)`, removing the offset accumulated over 254 doublings.
/// Computed off-circuit with `ark-grumpkin` and validated: the same routine
/// reproduces [`corr`] (the 128-bit `corr₁₂₈`) exactly.
fn corr254() -> [Field; 2] {
    [
        Field::from(
            "16553197835714973834031774601520451931051624293930580121206769559624452310037",
        ),
        Field::from(
            "19649441642928946798700829372424834756358685055060237751050452085768514233992",
        ),
    ]
}

/// **Full-width variable-base scalar mul** `s·P`: [`scalar_mul`]'s signed-digit
/// fused double-and-add over all 254 bits of a [`WideScalar`] (MSB first). Pins `p`
/// to the curve first (the group law only holds there) and decomposes the limbs
/// itself. Rejects `s·P = 0` (`s = 0`, or `s` the group order) as [`scalar_mul`]
/// rejects `m = 0`.
#[gadget]
pub fn wide_scalar_mul(s: WideScalar, p: Affine) -> Affine {
    let p = [p.x, p.y];
    enforce_on_curve(p);
    let lo = s.limbs[0].to_bits::<127>();
    let hi = s.limbs[1].to_bits::<127>();
    let bit = |i: usize| if i < 127 { lo[i] } else { hi[i - 127] };
    let r = signed_mul(bit, 254, p, corr254());
    Affine { x: r[0], y: r[1] }
}

/// Bring the gadget's public API into scope alongside the xark circuit
/// essentials (`Field`, `Public`/`Private`, `require_eq`, `#[circuit]`), so a
/// circuit crate needs a single `use xark_grumpkin::prelude::*;`.
pub mod prelude {
    pub use crate::*;
    pub use xark::prelude::*;
}
