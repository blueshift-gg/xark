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
//! * [`scalar_mul`] — **variable-base** scalar multiplication `m · P` where `P`
//!   is a *witness* point (unlike the Pedersen fixed-base version, we cannot
//!   precompute multiples of `P`, so we double the accumulator and
//!   conditionally add the variable `P`).
//! * [`multi_scalar_mul`] — multi-scalar multiplication `Σᵢ scalarᵢ · Pᵢ`.
//!
//! ## Offset accumulator (staying off infinity)
//!
//! Incomplete affine addition cannot represent the point at infinity. To keep
//! every intermediate off `∞` we run an **offset double-and-add**:
//!
//! ```text
//!   acc = O                              // O: fixed non-identity offset point
//!   for i in 0..N  (MSB first):
//!       acc = 2·acc
//!       acc = bitᵢ ? acc + P : acc       // arithmetic point-mux, never a branch
//!   result = acc - 2^N·O                 // remove the accumulated offset
//! ```
//!
//! After the loop `acc = 2^N·O + m·P`, so adding the compile-time constant
//! correction `corr = -(2^N·O)` yields `m·P`. `O` is a constant, hence `corr`
//! is a compile-time constant too. (`O` and `corr` are shared with
//! `xark-pedersen`; both are computed/verified by the scratchpad Python
//! reference used in `tests/vec.rs`.)
//!
//! ## Soundness / completeness
//!
//! Every division uses `Field::hint_inverse`, PINNED by `denom · inv == 1`. At
//! an exceptional case (`x1 == x2` in an add, or `y == 0` in a double) the
//! denominator is `0`, so `0 · inv == 1` is **unsatisfiable** — a malicious
//! prover can never forge a result at an edge (soundness holds). An honest
//! prover only fails on the negligible fraction of inputs that land exactly on
//! an incomplete-addition edge (the standard completeness gap): each scalar must
//! be nonzero, and the scalar bits / witness point must avoid the (negligible)
//! collision set of the offset accumulator.
//!
//! ## Scalar range / bit-length
//!
//! `N_BITS = 128`: scalars are decomposed into 128 pinned little-endian bits.
//! Because `2^128 < r`, the decomposition is *injective* (analyzer-clean, no
//! non-canonical-decomposition malleability). Raising `N_BITS` toward 252
//! (full-field scalars) is a one-line change plus regenerating the single
//! `corr` constant (`corr` depends on `N_BITS`).

#![no_std]
// Circuit-lowered gadget code: the xark compiler rejects compound assignment on
// `Field` (`+=`/`-=`/`*=`), so `x = x + y` is required — not a clippy oversight.
#![allow(clippy::assign_op_pattern)]

use xark::{assert_eq, Field};

/// Scalar bit-length (see module docs). Kept in sync with the `128usize` loop
/// literals below (loop bounds must be integer literals in the subset).
pub const N_BITS: usize = 128;

/// Number of `(scalar, point)` pairs summed by [`multi_scalar_mul`].
pub const K: usize = 2;

// ===========================================================================
// Curve constants. `O` is a fixed on-curve non-identity Grumpkin point (x = 5);
// `corr = -(2^N_BITS · O)`. Both verified by scratchpad `gref.py`.
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
    assert_eq(dx * inv, one); // pins dx ≠ 0 (edge ⇒ unsatisfiable)
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
    assert_eq(two_y * inv, one); // pins 2y ≠ 0 (edge ⇒ unsatisfiable)
    let lam = three * x * x * inv;
    let x3 = lam * lam - two * x;
    let y3 = lam * (x - x3) - y;
    [x3, y3]
}

/// Boolean-gated select between two affine points: `bit ? if_true : if_false`.
/// Pure arithmetic mux `sel·(a - b) + b` — never a data-dependent branch.
fn point_select(bit: Field, if_true: [Field; 2], if_false: [Field; 2]) -> [Field; 2] {
    bit.assert_bool();
    [
        if_false[0] + bit * (if_true[0] - if_false[0]),
        if_false[1] + bit * (if_true[1] - if_false[1]),
    ]
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
        bits[i].assert_bool();
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
    assert_eq(acc, x);
    bits
}

/// Assert the affine point `p = (x, y)` lies on the Grumpkin curve `y² = x³ − 17`.
pub fn enforce_on_curve(p: [Field; 2]) {
    let x = p[0];
    let y = p[1];
    assert_eq(y * y, x * x * x - Field::from(17u8));
}

/// **Variable-base** scalar multiplication `m · p` via the offset
/// (double-and-add) accumulator. `bits` is the little-endian decomposition of
/// `m`; processed MSB-first. `p` is a *witness* Grumpkin point. Returns the
/// affine point `m · p`. Requires `m ≠ 0`.
pub fn scalar_mul(bits: [Field; N_BITS], p: [Field; 2]) -> [Field; 2] {
    // pin the witness point to the curve (group law is only valid on-curve)
    enforce_on_curve(p);
    let mut acc = offset();
    let mut i = 0usize;
    while i < 128usize {
        acc = ec_double(acc);
        let bit = bits[127 - i]; // MSB first
        let cand = ec_add(acc, p);
        acc = point_select(bit, cand, acc);
        i += 1;
    }
    // acc = 2^N·O + m·p ; remove the offset by adding corr = -(2^N·O).
    ec_add(acc, corr())
}

/// **Multi-scalar multiplication**: `Σᵢ scalarᵢ · pointᵢ` over `K` witness
/// `(scalar, point)` pairs. Each `scalarᵢ` must be a nonzero `< 2^N_BITS`
/// scalar and each `pointᵢ` a non-identity on-curve Grumpkin point.
pub fn multi_scalar_mul(scalars: [Field; K], points: [[Field; 2]; K]) -> [Field; 2] {
    let mut acc = scalar_mul(decompose(scalars[0]), points[0]);
    let mut i = 1usize;
    while i < 2usize {
        let term = scalar_mul(decompose(scalars[i]), points[i]);
        acc = ec_add(acc, term);
        i += 1;
    }
    acc
}

/// A Grumpkin affine point as two native `Field` coordinates. Grumpkin's base
/// field is exactly BN254's scalar field (the circuit `Field`), so a point needs
/// no non-native limbs — `x`/`y` are ordinary field elements. Flattens to the
/// leaves `<name>.x` / `<name>.y`.
#[derive(Clone, Copy)]
pub struct Affine {
    pub x: Field,
    pub y: Field,
}

/// Host-side `NativeInput` for [`Affine`], behind the `host` feature: the two
/// coordinates are full field elements, taken as decimal (or `0x`-hex) strings.
#[cfg(not(xark))]
mod host {
    extern crate std;
    use super::Affine;
    use std::string::String;
    use std::vec::Vec;

    impl xark_prover::NativeInput for Affine {
        type Native = [String; 2];
        fn leaves(native: &[String; 2], prefix: &str) -> Vec<(String, String)> {
            use std::format;
            let mut out = Vec::new();
            out.push((format!("{prefix}.x"), native[0].clone()));
            out.push((format!("{prefix}.y"), native[1].clone()));
            out
        }
    }
}
