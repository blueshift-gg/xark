//! Grumpkin embedded-curve operations.
//!
//! Implements `BlackBoxFuncCall::EmbeddedCurveAdd` and
//! `BlackBoxFuncCall::MultiScalarMul`. The embedded curve over BN254 Fr is
//! **Grumpkin**: `y^2 = x^3 - 17` over `ark_bn254::Fr`. Its scalar field equals
//! BN254's base field `Fq`. No foreign-field arithmetic is needed because the
//! Grumpkin base field IS the proving system field.
//!
//! # Representation
//!
//! Each curve point is an affine triple `(x, y, is_infinity)`. Following Noir's
//! convention (see `noir_stdlib/src/embedded_curve_ops.nr`), the
//! point-at-infinity is encoded as `(0, 0, 1)`. Note Noir's stdlib stores only
//! `(x, y)` and derives `is_infinite = (x == 0 && y == 0)`; the ACIR opcode
//! carries the boolean explicitly.
//!
//! # In-circuit point addition
//!
//! Given the Noir contract — points are guaranteed on-curve, `is_infinite` is
//! boolean — we use a **prover-aided affine addition**:
//!
//! 1. The prover supplies the output `(x3, y3, is_inf3)` and the slope
//!    `lambda` such that:
//! * Generic case (different x): `lambda = (y2 - y1) / (x2 - x1)`.
//! * Doubling case (same point): `lambda = 3 x1^2 / (2 y1)`.
//! * Inverse case (`y1 = -y2, x1 = x2`): result is infinity, `lambda = 0`.
//! 2. We allocate selector booleans
//!    `lhs_inf, rhs_inf, is_double, is_inverse` and prove they are consistent
//!    with the input flags / coordinates.
//! 3. We enforce the affine slope equation for `lambda` in the appropriate
//!    case and the standard `x3 = lambda^2 - x1 - x2`,
//!    `y3 = lambda * (x1 - x3) - y1` formulas, *gated* by selectors so that
//!    the right output is produced in every edge case.
//!
//! Specifically, define the "generic" output
//! ```text
//! xg = lambda^2 - x1 - x2
//! yg = lambda * (x1 - xg) - y1
//! ```
//! and select:
//! * if `lhs_inf == 1`: output = `(x2, y2, rhs_inf)`,
//! * else if `rhs_inf == 1`: output = `(x1, y1, lhs_inf)`,
//! * else if `is_inverse == 1`: output = `(0, 0, 1)`,
//! * else: output = `(xg, yg, 0)` (this covers doubling and generic add).
//!
//! Conservatively this costs ~12 R1CS constraints per add.
//!
//! # In-circuit MSM
//!
//! Each `(point, scalar_lo, scalar_hi)` triple is processed with **bit-by-bit
//! double-and-add**: the 256-bit scalar `s = lo + 2^128 * hi` is decomposed
//! into 256 boolean witnesses LSB-first; we run an accumulator `acc` initially
//! at infinity, doubling the running point and conditionally adding it to
//! `acc` per bit. Constraint cost ≈ `256 * (3 * EC_ADD) = ~9k` per pair.
//!
//! All MSMs sum the partial products via the same `ec_add_in_circuit` gadget.

#![allow(clippy::needless_range_loop)]

use ark_bn254::{Fq, Fr};
use ark_ec::short_weierstrass::{self as sw, SWCurveConfig};
use ark_ec::{AffineRepr, CurveConfig, CurveGroup, PrimeGroup};
use ark_ff::{AdditiveGroup, Field, One, PrimeField, Zero};
use ark_relations::gr1cs::{LinearCombination, SynthesisError, Variable};
use num_bigint::BigUint;

use crate::gadgets::boolean::enforce_boolean;
use crate::r1cs_builder::R1csBuilder;

// ---------------------------------------------------------------------------
// Grumpkin curve config (in-crate).
// ---------------------------------------------------------------------------

/// Local Grumpkin Short Weierstrass config. Matches the upstream
/// `ark_grumpkin::GrumpkinConfig`: base field `ark_bn254::Fr` (the proving
/// field), scalar field `ark_bn254::Fq`, `y^2 = x^3 - 17`, cofactor 1,
/// generator `(1, sqrt(-16))`. We define it in-crate to avoid a Cargo
/// dependency on `ark-grumpkin` (which is pinned to ark-ec 0.6 while the rest
/// of the workspace lives on 0.5).
#[derive(Copy, Clone, Default, PartialEq, Eq)]
pub struct GrumpkinConfig;

impl CurveConfig for GrumpkinConfig {
    type BaseField = Fr;
    type ScalarField = Fq;

    const COFACTOR: &'static [u64] = &[1];
    const COFACTOR_INV: Fq = Fq::ONE;
}

impl SWCurveConfig for GrumpkinConfig {
    const COEFF_A: Fr = Fr::ZERO;
    /// `COEFF_B = -17` over `ark_bn254::Fr`.
    const COEFF_B: Fr = ark_ff::MontFp!("-17");
    const GENERATOR: GrumpkinAffine = GrumpkinAffine::new_unchecked(Fr::ONE, GENERATOR_Y);

    // arkworks 0.6 added this associated type; `()` selects the default
    // (0,0)-is-infinity zero-flag representation the built-in configs use.
    type ZeroFlag = ();

    #[inline(always)]
    fn mul_by_a(_: Fr) -> Fr {
        Fr::ZERO
    }
}

/// Pre-evaluated generator-y constant. We cannot construct `Fr` via `MontFp!`
/// from a 60-digit decimal literal at const-eval time without macro support
/// for it; instead we hand-compute the limbs by hardcoding the decimal.
const GENERATOR_Y: Fr =
    ark_ff::MontFp!("17631683881184975370165255887551781615748388533673675138860");

pub type GrumpkinAffine = sw::Affine<GrumpkinConfig>;
pub type GrumpkinProjective = sw::Projective<GrumpkinConfig>;

// ---------------------------------------------------------------------------
// Native reference ops.
// ---------------------------------------------------------------------------

/// Native (out-of-circuit) Grumpkin point addition using Arkworks SW arithmetic.
pub fn ec_add_native(p1: GrumpkinAffine, p2: GrumpkinAffine) -> GrumpkinAffine {
    (p1 + p2).into_affine()
}

/// Native Grumpkin doubling.
pub fn ec_double_native(p: GrumpkinAffine) -> GrumpkinAffine {
    (p + p).into_affine()
}

/// Native multi-scalar multiplication: `sum_i scalars[i] * points[i]`.
/// Scalars are given as `BigUint` (256-bit), matching the
/// `lo + 2^128 * hi` decomposition Noir ships across the
/// `MultiScalarMul` opcode boundary.
pub fn msm_native(points: &[GrumpkinAffine], scalars: &[BigUint]) -> GrumpkinAffine {
    assert_eq!(points.len(), scalars.len());
    let mut acc = GrumpkinProjective::zero();
    for (p, s) in points.iter().zip(scalars.iter()) {
        let limbs = s.to_u64_digits();
        let term = p.into_group().mul_bigint(limbs);
        acc += term;
    }
    acc.into_affine()
}

// ---------------------------------------------------------------------------
// In-circuit point + helpers.
// ---------------------------------------------------------------------------

/// A point in the constraint system, carrying both its R1CS handles and
/// (optionally) its proving-time values.
#[derive(Clone, Debug)]
pub struct CurvePoint {
    pub x: Variable,
    pub y: Variable,
    pub is_infinity: Variable,
    pub x_val: Option<Fr>,
    pub y_val: Option<Fr>,
    pub is_inf_val: Option<bool>,
}

impl CurvePoint {
    fn to_affine(&self) -> Option<GrumpkinAffine> {
        let (x, y, i) = (self.x_val?, self.y_val?, self.is_inf_val?);
        if i {
            Some(GrumpkinAffine::zero())
        } else {
            Some(GrumpkinAffine::new_unchecked(x, y))
        }
    }
}

/// Build a `CurvePoint` from existing variables. Enforces `is_infinity` is
/// boolean *and* that `(x, y)` lies on Grumpkin (`y² = x³ − 17`) when
/// `is_infinity == 0`. The on-curve check protects against a malicious
/// prover supplying off-curve `(x, y)` to `EmbeddedCurveAdd` or
/// `MultiScalarMul` and exploiting the looser arithmetic the generic
/// add/double formulas allow.
///
/// Cost: 1 boolean (is_infinity) + 3 mul auxes (y², x², x³) + 1 gated
/// equality constraint = 5 constraints per point. Negligible relative to
/// any non-trivial scalar mul that uses the point.
pub fn curve_point_from_vars(
    builder: &mut R1csBuilder<'_>,
    x: Variable,
    y: Variable,
    is_infinity: Variable,
    x_val: Option<Fr>,
    y_val: Option<Fr>,
    is_inf_val: Option<bool>,
) -> Result<CurvePoint, SynthesisError> {
    enforce_boolean(builder, is_infinity)?;
    enforce_on_curve_grumpkin(builder, x, y, x_val, y_val, is_infinity, is_inf_val)?;
    Ok(CurvePoint {
        x,
        y,
        is_infinity,
        x_val,
        y_val,
        is_inf_val,
    })
}

/// Enforce `(1 − is_infinity) · (y² − x³ + 17) = 0` over the proving-system
/// field. When `is_infinity = 1`, the constraint is satisfied trivially
/// (no curve membership required for the identity); when
/// `is_infinity = 0`, this forces `y² = x³ − 17`, i.e. `(x, y) ∈ Grumpkin`.
fn enforce_on_curve_grumpkin(
    builder: &mut R1csBuilder<'_>,
    x: Variable,
    y: Variable,
    x_val: Option<Fr>,
    y_val: Option<Fr>,
    is_infinity: Variable,
    is_inf_val: Option<bool>,
) -> Result<(), SynthesisError> {
    // y² aux.
    let y_sq_val = y_val.map(|v| v * v);
    let y_sq = builder.alloc_with_value(y_sq_val)?;
    builder.enforce(var_lc(y), var_lc(y), var_lc(y_sq))?;

    // x² aux.
    let x_sq_val = x_val.map(|v| v * v);
    let x_sq = builder.alloc_with_value(x_sq_val)?;
    builder.enforce(var_lc(x), var_lc(x), var_lc(x_sq))?;

    // x³ aux.
    let x_cu_val = match (x_sq_val, x_val) {
        (Some(s), Some(v)) => Some(s * v),
        _ => None,
    };
    let x_cu = builder.alloc_with_value(x_cu_val)?;
    builder.enforce(var_lc(x_sq), var_lc(x), var_lc(x_cu))?;

    // (1 − is_infinity) · (y² − x³ + 17) = 0.
    //
    // A = 1 − is_infinity
    // B = y_sq − x_cu + 17·Variable::One
    // C = 0
    let a = LinearCombination(vec![(Fr::one(), Variable::One), (-Fr::one(), is_infinity)]);
    let b = LinearCombination(vec![
        (Fr::one(), y_sq),
        (-Fr::one(), x_cu),
        (Fr::from(17u64), Variable::One),
    ]);
    let _ = (is_inf_val, y_sq_val, x_sq_val, x_cu_val);
    builder.enforce(a, b, LinearCombination(vec![]))
}

/// Pin a value-carrying linear combination to a fresh witness via
/// `0 * 0 = lc - var`.
fn pin_lc(
    builder: &mut R1csBuilder<'_>,
    lc: LinearCombination<Fr>,
    value: Option<Fr>,
) -> Result<Variable, SynthesisError> {
    let var = builder.alloc_with_value(value)?;
    let mut diff = lc;
    diff.0.push((-Fr::one(), var));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), diff)?;
    Ok(var)
}

/// Allocate a boolean witness with the given proving-time value.
fn alloc_bool(
    builder: &mut R1csBuilder<'_>,
    value: Option<bool>,
) -> Result<Variable, SynthesisError> {
    let fr_val = value.map(|b| if b { Fr::one() } else { Fr::zero() });
    let var = builder.alloc_with_value(fr_val)?;
    enforce_boolean(builder, var)?;
    Ok(var)
}

/// Convenience: `Variable::One` as a 1-coefficient LC.
#[inline]
fn one_lc() -> LinearCombination<Fr> {
    LinearCombination(vec![(Fr::one(), Variable::One)])
}

/// LC for a single variable.
#[inline]
fn var_lc(v: Variable) -> LinearCombination<Fr> {
    LinearCombination(vec![(Fr::one(), v)])
}

/// `a - b` as a fresh LC, given each side as an LC.
fn sub_lc(a: &LinearCombination<Fr>, b: &LinearCombination<Fr>) -> LinearCombination<Fr> {
    let mut out = a.clone();
    for (c, v) in b.0.iter() {
        out.0.push((-*c, *v));
    }
    out
}

// ---------------------------------------------------------------------------
// Native helper: affine addition with full case handling. Used by the gadget
// to populate witness values; we cross-check against Arkworks in tests.
// ---------------------------------------------------------------------------

fn affine_add_full(p1: GrumpkinAffine, p2: GrumpkinAffine) -> GrumpkinAffine {
    (p1 + p2).into_affine()
}

// ---------------------------------------------------------------------------
// In-circuit complete affine addition.
// ---------------------------------------------------------------------------

/// Add `p1 + p2` in-circuit. Handles all edge cases (infinity, doubling,
/// `p + (-p)`). Per-add cost is ~16 R1CS constraints.
///
/// Strategy: the prover supplies the output `(x3, y3, is_inf3)` and the
/// slope `lambda`. We additionally allocate selector booleans
/// `same_x, same_y, is_double, is_inverse` and enforce:
///
/// * `same_x` ↔ `x1 == x2` via a hinted inverse witness `inv_dx` such that
///   `(x2 - x1) * inv_dx = 1 - same_x` and `same_x * (x2 - x1) = 0`.
/// * Likewise `same_y` ↔ `y1 == y2`.
/// * `is_double = same_x * same_y * (1 - lhs_inf) * (1 - rhs_inf)`
///   (computed via several muls).
/// * `is_inverse = same_x * (1 - same_y) * (1 - lhs_inf) * (1 - rhs_inf)`.
/// * Slope equation:
///   `(x2 - x1) * lambda = (y2 - y1) + is_double * extra_double_correction`
///   where `extra_double_correction = 2*y1*lambda - 3*x1^2` is also computed
///   from witnesses — but we side-step that complexity by writing two gated
///   equations:
/// - `(1 - is_double) * (1 - is_inverse) * ((x2 - x1) * lambda - (y2 - y1)) = 0`
/// - `is_double * (2 * y1 * lambda - 3 * x1 * x1) = 0`
/// * Generic output:
///   `xg = lambda^2 - x1 - x2`, `yg = lambda * (x1 - xg) - y1`.
/// * Final output selection:
/// ```text
/// x3 = lhs_inf * x2 + (1 - lhs_inf) * (rhs_inf * x1 + (1 - rhs_inf) * (1 - is_inverse) * xg)
/// y3 = lhs_inf * y2 + (1 - lhs_inf) * (rhs_inf * y1 + (1 - rhs_inf) * (1 - is_inverse) * yg)
/// is_inf3 = lhs_inf * rhs_inf
/// + (1 - lhs_inf) * (1 - rhs_inf) * is_inverse +...
/// ```
/// For readability we flatten this in code using pin_lc.
pub fn ec_add_in_circuit(
    builder: &mut R1csBuilder<'_>,
    p1: &CurvePoint,
    p2: &CurvePoint,
) -> Result<CurvePoint, SynthesisError> {
    // --- native reference output (used to populate witness values) ---
    let native_out: Option<GrumpkinAffine> = match (p1.to_affine(), p2.to_affine()) {
        (Some(a), Some(b)) => Some(affine_add_full(a, b)),
        _ => None,
    };

    // --- compute lambda value from cases ---
    let lambda_val: Option<Fr> = match (
        p1.x_val,
        p1.y_val,
        p1.is_inf_val,
        p2.x_val,
        p2.y_val,
        p2.is_inf_val,
    ) {
        (Some(x1), Some(y1), Some(i1), Some(x2), Some(y2), Some(i2)) => {
            if i1 || i2 {
                Some(Fr::zero())
            } else if x1 == x2 {
                if y1 == y2 {
                    // doubling: 3 x1^2 / 2 y1
                    let num = Fr::from(3u64) * x1 * x1;
                    let den = (y1 + y1).inverse().unwrap_or(Fr::zero());
                    Some(num * den)
                } else {
                    // inverse: result is infinity, lambda unused; pick 0
                    Some(Fr::zero())
                }
            } else {
                Some((y2 - y1) * (x2 - x1).inverse().expect("x2 != x1"))
            }
        }
        _ => None,
    };

    // --- compute selectors from values ---
    let same_x_val: Option<bool> = match (p1.x_val, p2.x_val) {
        (Some(a), Some(b)) => Some(a == b),
        _ => None,
    };
    let same_y_val: Option<bool> = match (p1.y_val, p2.y_val) {
        (Some(a), Some(b)) => Some(a == b),
        _ => None,
    };
    let lhs_inf_val = p1.is_inf_val;
    let rhs_inf_val = p2.is_inf_val;
    let is_double_val: Option<bool> = match (same_x_val, same_y_val, lhs_inf_val, rhs_inf_val) {
        (Some(sx), Some(sy), Some(li), Some(ri)) => Some(sx && sy && !li && !ri),
        _ => None,
    };
    let is_inverse_val: Option<bool> = match (same_x_val, same_y_val, lhs_inf_val, rhs_inf_val) {
        (Some(sx), Some(sy), Some(li), Some(ri)) => Some(sx && !sy && !li && !ri),
        _ => None,
    };

    // --- allocate witnesses ---
    let lambda = builder.alloc_with_value(lambda_val)?;
    let same_x = alloc_bool(builder, same_x_val)?;
    let same_y = alloc_bool(builder, same_y_val)?;

    // --- enforce same_x correctness via hinted inverse: ---
    // same_x * (x2 - x1) = 0
    // (x2 - x1) * inv_dx = 1 - same_x (when same_x = 0, this pins inv_dx
    // to be the true inverse; when same_x = 1, dx must be 0 by previous).
    let dx_lc = sub_lc(&var_lc(p2.x), &var_lc(p1.x));
    builder.enforce(var_lc(same_x), dx_lc.clone(), builder.zero_lc())?;
    let inv_dx_val: Option<Fr> = match (p1.x_val, p2.x_val) {
        (Some(a), Some(b)) => {
            if a == b {
                Some(Fr::zero())
            } else {
                Some((b - a).inverse().expect("dx nonzero when same_x = false"))
            }
        }
        _ => None,
    };
    let inv_dx = builder.alloc_with_value(inv_dx_val)?;
    // (x2 - x1) * inv_dx = 1 - same_x
    let one_minus_same_x = sub_lc(&one_lc(), &var_lc(same_x));
    builder.enforce(dx_lc.clone(), var_lc(inv_dx), one_minus_same_x.clone())?;

    // --- enforce same_y correctness similarly: ---
    let dy_lc = sub_lc(&var_lc(p2.y), &var_lc(p1.y));
    builder.enforce(var_lc(same_y), dy_lc.clone(), builder.zero_lc())?;
    let inv_dy_val: Option<Fr> = match (p1.y_val, p2.y_val) {
        (Some(a), Some(b)) => {
            if a == b {
                Some(Fr::zero())
            } else {
                Some((b - a).inverse().expect("dy nonzero when same_y = false"))
            }
        }
        _ => None,
    };
    let inv_dy = builder.alloc_with_value(inv_dy_val)?;
    let one_minus_same_y = sub_lc(&one_lc(), &var_lc(same_y));
    builder.enforce(dy_lc.clone(), var_lc(inv_dy), one_minus_same_y.clone())?;

    // --- compute is_double, is_inverse as 4-way products ---
    // not_lhs = 1 - lhs_inf, not_rhs = 1 - rhs_inf
    let not_lhs_lc = sub_lc(&one_lc(), &var_lc(p1.is_infinity));
    let not_rhs_lc = sub_lc(&one_lc(), &var_lc(p2.is_infinity));

    // t1 = same_x * same_y
    let t1_val = match (same_x_val, same_y_val) {
        (Some(a), Some(b)) => Some(if a && b { Fr::one() } else { Fr::zero() }),
        _ => None,
    };
    let t1 = builder.alloc_with_value(t1_val)?;
    builder.enforce(var_lc(same_x), var_lc(same_y), var_lc(t1))?;

    // t2 = t1 * not_lhs
    let t2_val = match (t1_val, lhs_inf_val) {
        (Some(a), Some(b)) => Some(if !b && a == Fr::one() {
            Fr::one()
        } else {
            Fr::zero()
        }),
        _ => None,
    };
    let t2 = builder.alloc_with_value(t2_val)?;
    builder.enforce(var_lc(t1), not_lhs_lc.clone(), var_lc(t2))?;

    // is_double = t2 * not_rhs
    let is_double =
        builder.alloc_with_value(is_double_val.map(|b| if b { Fr::one() } else { Fr::zero() }))?;
    builder.enforce(var_lc(t2), not_rhs_lc.clone(), var_lc(is_double))?;

    // s1 = same_x * (1 - same_y)
    let s1_val = match (same_x_val, same_y_val) {
        (Some(a), Some(b)) => Some(if a && !b { Fr::one() } else { Fr::zero() }),
        _ => None,
    };
    let s1 = builder.alloc_with_value(s1_val)?;
    builder.enforce(var_lc(same_x), one_minus_same_y.clone(), var_lc(s1))?;

    // s2 = s1 * not_lhs
    let s2_val = match (s1_val, lhs_inf_val) {
        (Some(v), Some(li)) => Some(if !li { v } else { Fr::zero() }),
        _ => None,
    };
    let s2 = builder.alloc_with_value(s2_val)?;
    builder.enforce(var_lc(s1), not_lhs_lc.clone(), var_lc(s2))?;

    // is_inverse = s2 * not_rhs
    let is_inverse =
        builder.alloc_with_value(is_inverse_val.map(|b| if b { Fr::one() } else { Fr::zero() }))?;
    builder.enforce(var_lc(s2), not_rhs_lc.clone(), var_lc(is_inverse))?;

    // --- slope equations ---
    // Generic case (when neither inf, not doubling, not inverse):
    // (x2 - x1) * lambda = y2 - y1
    // Doubling case (when is_double = 1):
    // 2 * y1 * lambda = 3 * x1^2
    //
    // We gate each by selectors. To avoid emitting them at all when at-infinity
    // or in inverse case (where lambda is unused), we gate further by
    // `not_lhs * not_rhs`.
    //
    // not_both_special = (1 - is_double) * (1 - is_inverse)
    // generic_active = not_lhs * not_rhs * not_both_special
    let not_double_lc = sub_lc(&one_lc(), &var_lc(is_double));
    let not_inverse_lc = sub_lc(&one_lc(), &var_lc(is_inverse));

    let nis_val = match (is_double_val, is_inverse_val) {
        (Some(d), Some(i)) => Some(if !d && !i { Fr::one() } else { Fr::zero() }),
        _ => None,
    };
    let not_in_special = builder.alloc_with_value(nis_val)?;
    builder.enforce(
        not_double_lc.clone(),
        not_inverse_lc.clone(),
        var_lc(not_in_special),
    )?;

    // both_finite = not_lhs * not_rhs
    let both_finite_val = match (lhs_inf_val, rhs_inf_val) {
        (Some(a), Some(b)) => Some(if !a && !b { Fr::one() } else { Fr::zero() }),
        _ => None,
    };
    let both_finite = builder.alloc_with_value(both_finite_val)?;
    builder.enforce(not_lhs_lc.clone(), not_rhs_lc.clone(), var_lc(both_finite))?;

    // generic_active = both_finite * not_in_special
    let generic_active_val = match (both_finite_val, nis_val) {
        (Some(a), Some(b)) => Some(if a == Fr::one() && b == Fr::one() {
            Fr::one()
        } else {
            Fr::zero()
        }),
        _ => None,
    };
    let generic_active = builder.alloc_with_value(generic_active_val)?;
    builder.enforce(
        var_lc(both_finite),
        var_lc(not_in_special),
        var_lc(generic_active),
    )?;

    // Constraint: generic_active * ((x2 - x1) * lambda - (y2 - y1)) = 0
    // We split into: t_dxl = (x2 - x1) * lambda, then enforce
    // generic_active * (t_dxl - (y2 - y1)) = 0.
    let t_dxl_val: Option<Fr> = match (p1.x_val, p2.x_val, lambda_val) {
        (Some(a), Some(b), Some(l)) => Some((b - a) * l),
        _ => None,
    };
    let t_dxl = builder.alloc_with_value(t_dxl_val)?;
    builder.enforce(dx_lc.clone(), var_lc(lambda), var_lc(t_dxl))?;
    let dxl_minus_dy = sub_lc(&var_lc(t_dxl), &dy_lc);
    builder.enforce(var_lc(generic_active), dxl_minus_dy, builder.zero_lc())?;

    // Doubling constraint: is_double * (2 y1 lambda - 3 x1^2) = 0
    // Compute aux: yl = y1 * lambda, xx = x1 * x1
    let yl_val = match (p1.y_val, lambda_val) {
        (Some(y), Some(l)) => Some(y * l),
        _ => None,
    };
    let yl = builder.alloc_with_value(yl_val)?;
    builder.enforce(var_lc(p1.y), var_lc(lambda), var_lc(yl))?;
    let xx_val = p1.x_val.map(|x| x * x);
    let xx = builder.alloc_with_value(xx_val)?;
    builder.enforce(var_lc(p1.x), var_lc(p1.x), var_lc(xx))?;

    // 2 * yl - 3 * xx
    let mut doubling_diff = LinearCombination::<Fr>::default();
    doubling_diff.0.push((Fr::from(2u64), yl));
    doubling_diff.0.push((-Fr::from(3u64), xx));
    builder.enforce(var_lc(is_double), doubling_diff, builder.zero_lc())?;

    // --- generic output (xg, yg) ---
    // xg = lambda^2 - x1 - x2
    // yg = lambda * (x1 - xg) - y1
    let lambda_sq_val = lambda_val.map(|l| l * l);
    let lambda_sq = builder.alloc_with_value(lambda_sq_val)?;
    builder.enforce(var_lc(lambda), var_lc(lambda), var_lc(lambda_sq))?;

    let xg_val: Option<Fr> = match (lambda_sq_val, p1.x_val, p2.x_val) {
        (Some(ls), Some(a), Some(b)) => Some(ls - a - b),
        _ => None,
    };
    // xg = lambda_sq - x1 - x2 (pure linear, pin it)
    let mut xg_lc = var_lc(lambda_sq);
    for (c, v) in var_lc(p1.x).0 {
        xg_lc.0.push((-c, v));
    }
    for (c, v) in var_lc(p2.x).0 {
        xg_lc.0.push((-c, v));
    }
    let xg = pin_lc(builder, xg_lc, xg_val)?;

    // yg = lambda * (x1 - xg) - y1
    // t_x1_minus_xg LC: x1 - xg
    let x1_minus_xg = sub_lc(&var_lc(p1.x), &var_lc(xg));
    let lambda_times_x1_minus_xg_val: Option<Fr> = match (lambda_val, p1.x_val, xg_val) {
        (Some(l), Some(x1), Some(x3)) => Some(l * (x1 - x3)),
        _ => None,
    };
    let lambda_times = builder.alloc_with_value(lambda_times_x1_minus_xg_val)?;
    builder.enforce(var_lc(lambda), x1_minus_xg, var_lc(lambda_times))?;

    let yg_val: Option<Fr> = match (lambda_times_x1_minus_xg_val, p1.y_val) {
        (Some(t), Some(y1)) => Some(t - y1),
        _ => None,
    };
    let mut yg_lc = var_lc(lambda_times);
    for (c, v) in var_lc(p1.y).0 {
        yg_lc.0.push((-c, v));
    }
    let yg = pin_lc(builder, yg_lc, yg_val)?;

    // --- output selection ---
    // We compute the final output coordinates as:
    // x3 = lhs_inf * x2 + not_lhs * (rhs_inf * x1 + not_rhs * (not_inverse * xg))
    // y3 = lhs_inf * y2 + not_lhs * (rhs_inf * y1 + not_rhs * (not_inverse * yg))
    // is_inf3 = lhs_inf * is_inf_lhs_case + not_lhs * (rhs_inf * is_inf_rhs_case + not_rhs * is_inverse)
    // where:
    // is_inf_lhs_case = rhs_inf (if both at infinity, output is also infinity; if p1 inf, output = p2)
    // is_inf_rhs_case = lhs_inf (already 0 here, but for symmetry)
    //
    // Concretely:
    // - If lhs_inf: out = (x2, y2, rhs_inf)
    // - Elif rhs_inf: out = (x1, y1, lhs_inf) = (x1, y1, 0)
    // - Elif is_inverse: out = (0, 0, 1)
    // - Else (incl is_double or generic): out = (xg, yg, 0)
    //
    // We compute the witness values from `native_out`.
    let (x3_val, y3_val, is_inf3_val) = match native_out {
        Some(p) => {
            if p.is_zero() {
                (Some(Fr::zero()), Some(Fr::zero()), Some(true))
            } else {
                let (xv, yv) = p.xy().expect("affine point not at infinity");
                (Some(xv), Some(yv), Some(false))
            }
        }
        None => (None, None, None),
    };

    // Pin selection helpers.
    // alpha = not_lhs * not_rhs * not_inverse (when 1, output is (xg, yg, 0))
    // We already have `generic_active = not_lhs * not_rhs * not_in_special`.
    // We want a slightly different selector since `not_in_special` excludes
    // `is_double` too, but in the doubling case xg/yg ARE the correct
    // doubling output. So define:
    // take_generic = both_finite * not_inverse -- selects the (xg, yg, 0)
    // branch when not at infinity and not in the p + (-p) case.
    let take_generic_val = match (both_finite_val, is_inverse_val) {
        (Some(bf), Some(inv)) => {
            if bf == Fr::one() && !inv {
                Some(Fr::one())
            } else {
                Some(Fr::zero())
            }
        }
        _ => None,
    };
    let take_generic = builder.alloc_with_value(take_generic_val)?;
    builder.enforce(
        var_lc(both_finite),
        not_inverse_lc.clone(),
        var_lc(take_generic),
    )?;

    // take_inverse = both_finite * is_inverse (output: (0, 0, 1))
    let take_inverse_val = match (both_finite_val, is_inverse_val) {
        (Some(bf), Some(inv)) => Some(if bf == Fr::one() && inv {
            Fr::one()
        } else {
            Fr::zero()
        }),
        _ => None,
    };
    let take_inverse = builder.alloc_with_value(take_inverse_val)?;
    builder.enforce(
        var_lc(both_finite),
        var_lc(is_inverse),
        var_lc(take_inverse),
    )?;

    // For the lhs_inf branch the result equals p2; for the rhs_inf branch
    // (when !lhs_inf) the result equals p1. We compute these as products,
    // then sum.
    // take_p2 = lhs_inf (result = (x2, y2, rhs_inf) — i3 = rhs_inf when only lhs is inf)
    // take_p1 = not_lhs * rhs_inf
    let take_p2 = p1.is_infinity;
    let take_p1_val = match (lhs_inf_val, rhs_inf_val) {
        (Some(li), Some(ri)) => Some(if !li && ri { Fr::one() } else { Fr::zero() }),
        _ => None,
    };
    let take_p1 = builder.alloc_with_value(take_p1_val)?;
    builder.enforce(not_lhs_lc.clone(), var_lc(p2.is_infinity), var_lc(take_p1))?;

    // For final coords: x3 = take_p2*x2 + take_p1*x1 + take_generic*xg + take_inverse*0
    // Use multiplication helpers for each product.
    let prod_p2_x_val = match (p1.is_inf_val, p2.x_val) {
        (Some(b), Some(x)) => Some(if b { x } else { Fr::zero() }),
        _ => None,
    };
    let prod_p2_x = builder.alloc_with_value(prod_p2_x_val)?;
    builder.enforce(var_lc(take_p2), var_lc(p2.x), var_lc(prod_p2_x))?;

    let prod_p1_x_val = match (take_p1_val, p1.x_val) {
        (Some(s), Some(x)) => Some(if s == Fr::one() { x } else { Fr::zero() }),
        _ => None,
    };
    let prod_p1_x = builder.alloc_with_value(prod_p1_x_val)?;
    builder.enforce(var_lc(take_p1), var_lc(p1.x), var_lc(prod_p1_x))?;

    let prod_gen_x_val = match (take_generic_val, xg_val) {
        (Some(s), Some(x)) => Some(if s == Fr::one() { x } else { Fr::zero() }),
        _ => None,
    };
    let prod_gen_x = builder.alloc_with_value(prod_gen_x_val)?;
    builder.enforce(var_lc(take_generic), var_lc(xg), var_lc(prod_gen_x))?;

    // x3 = prod_p2_x + prod_p1_x + prod_gen_x
    let x3 = builder.alloc_with_value(x3_val)?;
    let mut x3_lc = var_lc(prod_p2_x);
    for (c, v) in var_lc(prod_p1_x).0 {
        x3_lc.0.push((c, v));
    }
    for (c, v) in var_lc(prod_gen_x).0 {
        x3_lc.0.push((c, v));
    }
    x3_lc.0.push((-Fr::one(), x3));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), x3_lc)?;

    // y3 similarly
    let prod_p2_y_val = match (p1.is_inf_val, p2.y_val) {
        (Some(b), Some(y)) => Some(if b { y } else { Fr::zero() }),
        _ => None,
    };
    let prod_p2_y = builder.alloc_with_value(prod_p2_y_val)?;
    builder.enforce(var_lc(take_p2), var_lc(p2.y), var_lc(prod_p2_y))?;

    let prod_p1_y_val = match (take_p1_val, p1.y_val) {
        (Some(s), Some(y)) => Some(if s == Fr::one() { y } else { Fr::zero() }),
        _ => None,
    };
    let prod_p1_y = builder.alloc_with_value(prod_p1_y_val)?;
    builder.enforce(var_lc(take_p1), var_lc(p1.y), var_lc(prod_p1_y))?;

    let prod_gen_y_val = match (take_generic_val, yg_val) {
        (Some(s), Some(y)) => Some(if s == Fr::one() { y } else { Fr::zero() }),
        _ => None,
    };
    let prod_gen_y = builder.alloc_with_value(prod_gen_y_val)?;
    builder.enforce(var_lc(take_generic), var_lc(yg), var_lc(prod_gen_y))?;

    let y3 = builder.alloc_with_value(y3_val)?;
    let mut y3_lc = var_lc(prod_p2_y);
    for (c, v) in var_lc(prod_p1_y).0 {
        y3_lc.0.push((c, v));
    }
    for (c, v) in var_lc(prod_gen_y).0 {
        y3_lc.0.push((c, v));
    }
    y3_lc.0.push((-Fr::one(), y3));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), y3_lc)?;

    // is_inf3 = take_p2 * rhs_inf + take_p1 * lhs_inf + take_inverse * 1
    // = take_p2 * rhs_inf + take_p1 * 0 (since take_p1 requires not lhs_inf) + take_inverse
    // = take_p2 * rhs_inf + take_inverse
    // (We compute it via the simpler relation.)
    // prod_inf_rhs = take_p2 * rhs_inf
    let prod_inf_rhs_val = match (lhs_inf_val, rhs_inf_val) {
        (Some(a), Some(b)) => Some(if a && b { Fr::one() } else { Fr::zero() }),
        _ => None,
    };
    let prod_inf_rhs = builder.alloc_with_value(prod_inf_rhs_val)?;
    builder.enforce(
        var_lc(take_p2),
        var_lc(p2.is_infinity),
        var_lc(prod_inf_rhs),
    )?;

    let is_inf3 =
        builder.alloc_with_value(is_inf3_val.map(|b| if b { Fr::one() } else { Fr::zero() }))?;
    enforce_boolean(builder, is_inf3)?;
    let mut inf_lc = var_lc(prod_inf_rhs);
    inf_lc.0.push((Fr::one(), take_inverse));
    inf_lc.0.push((-Fr::one(), is_inf3));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), inf_lc)?;

    Ok(CurvePoint {
        x: x3,
        y: y3,
        is_infinity: is_inf3,
        x_val: x3_val,
        y_val: y3_val,
        is_inf_val: is_inf3_val,
    })
}

// ---------------------------------------------------------------------------
// In-circuit scalar mul + MSM.
// ---------------------------------------------------------------------------

/// Allocate a constant `CurvePoint` representing the point at infinity.
/// Returns a fresh `(x=0, y=0, is_infinity=1)` triple bound by linear
/// constraints to `One`-scaled constants. Adds 3 small linear constraints.
fn alloc_constant_infinity(builder: &mut R1csBuilder<'_>) -> Result<CurvePoint, SynthesisError> {
    // x = 0
    let x = builder.alloc_with_value(Some(Fr::zero()))?;
    builder.enforce(builder.zero_lc(), builder.zero_lc(), var_lc(x))?;
    // y = 0
    let y = builder.alloc_with_value(Some(Fr::zero()))?;
    builder.enforce(builder.zero_lc(), builder.zero_lc(), var_lc(y))?;
    // is_infinity = 1
    let is_inf = builder.alloc_with_value(Some(Fr::one()))?;
    let mut lc = var_lc(is_inf);
    lc.0.push((-Fr::one(), Variable::One));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), lc)?;
    enforce_boolean(builder, is_inf)?;
    Ok(CurvePoint {
        x,
        y,
        is_infinity: is_inf,
        x_val: Some(Fr::zero()),
        y_val: Some(Fr::zero()),
        is_inf_val: Some(true),
    })
}

/// Conditional select: `out = sel ? a : b` for scalars (Variable + value).
/// `out = b + sel * (a - b)`.
fn conditional_select_scalar(
    builder: &mut R1csBuilder<'_>,
    sel: Variable,
    sel_val: Option<bool>,
    a: Variable,
    a_val: Option<Fr>,
    b: Variable,
    b_val: Option<Fr>,
) -> Result<(Variable, Option<Fr>), SynthesisError> {
    let diff_val = match (a_val, b_val) {
        (Some(av), Some(bv)) => Some(av - bv),
        _ => None,
    };
    let prod_val = match (sel_val, diff_val) {
        (Some(s), Some(d)) => Some(if s { d } else { Fr::zero() }),
        _ => None,
    };
    let prod = builder.alloc_with_value(prod_val)?;
    let diff_lc = sub_lc(&var_lc(a), &var_lc(b));
    builder.enforce(var_lc(sel), diff_lc, var_lc(prod))?;

    let out_val = match (b_val, prod_val) {
        (Some(bv), Some(pv)) => Some(bv + pv),
        _ => None,
    };
    let out = builder.alloc_with_value(out_val)?;
    let mut lc = var_lc(b);
    lc.0.push((Fr::one(), prod));
    lc.0.push((-Fr::one(), out));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), lc)?;
    Ok((out, out_val))
}

/// Conditional select over a `CurvePoint`: returns `sel ? p : q`.
fn conditional_select_point(
    builder: &mut R1csBuilder<'_>,
    sel: Variable,
    sel_val: Option<bool>,
    p: &CurvePoint,
    q: &CurvePoint,
) -> Result<CurvePoint, SynthesisError> {
    let (x, x_val) = conditional_select_scalar(builder, sel, sel_val, p.x, p.x_val, q.x, q.x_val)?;
    let (y, y_val) = conditional_select_scalar(builder, sel, sel_val, p.y, p.y_val, q.y, q.y_val)?;
    let (is_inf, _) = conditional_select_scalar(
        builder,
        sel,
        sel_val,
        p.is_infinity,
        p.is_inf_val.map(|b| if b { Fr::one() } else { Fr::zero() }),
        q.is_infinity,
        q.is_inf_val.map(|b| if b { Fr::one() } else { Fr::zero() }),
    )?;
    enforce_boolean(builder, is_inf)?;
    let is_inf_val = match sel_val {
        Some(s) => {
            if s {
                p.is_inf_val
            } else {
                q.is_inf_val
            }
        }
        None => None,
    };
    Ok(CurvePoint {
        x,
        y,
        is_infinity: is_inf,
        x_val,
        y_val,
        is_inf_val,
    })
}

/// Scalar multiplication `s · P` in-circuit via bit-by-bit double-and-add.
///
/// `scalar_bits` is LSB-first; each entry is a boolean Variable (already
/// constrained to 0/1) plus its proving-time value.
pub fn scalar_mul_in_circuit(
    builder: &mut R1csBuilder<'_>,
    point: &CurvePoint,
    scalar_bits: &[(Variable, Option<bool>)],
) -> Result<CurvePoint, SynthesisError> {
    let mut acc = alloc_constant_infinity(builder)?;
    let mut running = point.clone();
    for (bit_var, bit_val) in scalar_bits.iter() {
        // candidate = acc + running
        let candidate = ec_add_in_circuit(builder, &acc, &running)?;
        // acc = bit ? candidate : acc
        acc = conditional_select_point(builder, *bit_var, *bit_val, &candidate, &acc)?;
        // running = running + running (double)
        running = ec_add_in_circuit(builder, &running, &running)?;
    }
    Ok(acc)
}

/// MSM: `sum_i scalars[i] * points[i]`. Each scalar is given as `(lo, hi)`
/// limb variables with their 128-bit values; we bit-decompose each limb into
/// 128 boolean bits (LSB-first) so the total scalar width is 256.
///
/// `scalar_limbs` slice: `[(lo_var, lo_val, hi_var, hi_val),...]`.
pub fn msm_in_circuit(
    builder: &mut R1csBuilder<'_>,
    points: &[CurvePoint],
    scalar_limbs: &[(Variable, Option<Fr>, Variable, Option<Fr>)],
) -> Result<CurvePoint, SynthesisError> {
    assert_eq!(points.len(), scalar_limbs.len());
    let mut acc = alloc_constant_infinity(builder)?;
    for (i, point) in points.iter().enumerate() {
        let (lo_var, lo_val, hi_var, hi_val) = scalar_limbs[i];
        // Decompose lo into 128 bits, hi into 128 bits, then concatenate.
        let lo_bits = crate::gadgets::range::decompose_into_bits(builder, lo_var, 128, lo_val)?;
        let hi_bits = crate::gadgets::range::decompose_into_bits(builder, hi_var, 128, hi_val)?;

        let lo_vals: Vec<Option<bool>> = match lo_val {
            Some(v) => bits_of(v, 128).into_iter().map(Some).collect(),
            None => vec![None; 128],
        };
        let hi_vals: Vec<Option<bool>> = match hi_val {
            Some(v) => bits_of(v, 128).into_iter().map(Some).collect(),
            None => vec![None; 128],
        };

        let mut all_bits: Vec<(Variable, Option<bool>)> = Vec::with_capacity(256);
        for j in 0..128 {
            all_bits.push((lo_bits[j], lo_vals[j]));
        }
        for j in 0..128 {
            all_bits.push((hi_bits[j], hi_vals[j]));
        }

        let term = scalar_mul_in_circuit(builder, point, &all_bits)?;
        acc = ec_add_in_circuit(builder, &acc, &term)?;
    }
    Ok(acc)
}

/// Extract the low `num_bits` bits of an `Fr` value as little-endian booleans.
fn bits_of(value: Fr, num_bits: usize) -> Vec<bool> {
    let big: BigUint = value.into_bigint().into();
    let mut bits = Vec::with_capacity(num_bits);
    for i in 0..num_bits {
        bits.push(big.bit(i as u64));
    }
    bits
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::gr1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use crate::witness::WitnessMap;

    fn alloc_point(builder: &mut R1csBuilder<'_>, x: Fr, y: Fr, is_inf: bool) -> CurvePoint {
        let xv = builder.alloc_with_value(Some(x)).unwrap();
        let yv = builder.alloc_with_value(Some(y)).unwrap();
        let infv = builder
            .alloc_with_value(Some(if is_inf { Fr::one() } else { Fr::zero() }))
            .unwrap();
        curve_point_from_vars(builder, xv, yv, infv, Some(x), Some(y), Some(is_inf)).unwrap()
    }

    fn assigned(cs: &ConstraintSystem<Fr>, v: Variable) -> Fr {
        cs.assigned_value(v).expect("variable has assignment")
    }

    /// Native generator (`G`) of Grumpkin.
    fn grumpkin_generator() -> GrumpkinAffine {
        GrumpkinConfig::GENERATOR
    }

    #[test]
    fn generator_is_on_curve() {
        let g = grumpkin_generator();
        assert!(g.is_on_curve());
        // sanity: g.y^2 == g.x^3 - 17
        let (x, y) = g.xy().unwrap();
        let lhs = y * y;
        let rhs = x * x * x + GrumpkinConfig::COEFF_B;
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn ec_add_native_matches_arkworks() {
        // 2G via doubling vs. G+G via addition.
        let g = grumpkin_generator();
        let g2_via_double = ec_double_native(g);
        let g2_via_add = ec_add_native(g, g);
        assert_eq!(g2_via_double, g2_via_add);

        // 5G = 2G + 3G = 4G + G (consistency).
        let three = BigUint::from(3u64);
        let four = BigUint::from(4u64);
        let five = BigUint::from(5u64);
        let g3 = msm_native(&[g], &[three]);
        let g4 = msm_native(&[g], &[four]);
        let g5 = msm_native(&[g], &[five]);
        let g5_v2 = ec_add_native(g2_via_double, g3);
        let g5_v3 = ec_add_native(g4, g);
        assert_eq!(g5, g5_v2);
        assert_eq!(g5, g5_v3);
    }

    #[test]
    fn ec_add_in_circuit_matches_native_generic() {
        let g = grumpkin_generator();
        let two_g = ec_double_native(g);
        let (gx, gy) = g.xy().unwrap();
        let (tx, ty) = two_g.xy().unwrap();
        let expected = ec_add_native(g, two_g);
        let (ex, ey) = expected.xy().unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::new();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&map));
        builder.finish_public_pass();

        let p1 = alloc_point(&mut builder, gx, gy, false);
        let p2 = alloc_point(&mut builder, tx, ty, false);
        let sum = ec_add_in_circuit(&mut builder, &p1, &p2).unwrap();
        cs.finalize();
        let cs_ref = cs.borrow().unwrap();
        assert_eq!(assigned(&cs_ref, sum.x), ex);
        assert_eq!(assigned(&cs_ref, sum.y), ey);
        assert_eq!(assigned(&cs_ref, sum.is_infinity), Fr::zero());
        drop(cs_ref);
        assert!(cs.is_satisfied().unwrap(), "ec_add_in_circuit generic case");
    }

    #[test]
    fn ec_add_in_circuit_handles_doubling() {
        let g = grumpkin_generator();
        let (gx, gy) = g.xy().unwrap();
        let expected = ec_double_native(g);
        let (ex, ey) = expected.xy().unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::new();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&map));
        builder.finish_public_pass();

        let p1 = alloc_point(&mut builder, gx, gy, false);
        let p2 = alloc_point(&mut builder, gx, gy, false);
        let sum = ec_add_in_circuit(&mut builder, &p1, &p2).unwrap();
        cs.finalize();
        let cs_ref = cs.borrow().unwrap();
        assert_eq!(assigned(&cs_ref, sum.x), ex);
        assert_eq!(assigned(&cs_ref, sum.y), ey);
        assert_eq!(assigned(&cs_ref, sum.is_infinity), Fr::zero());
        drop(cs_ref);
        assert!(cs.is_satisfied().unwrap(), "ec_add doubling case");
    }

    #[test]
    fn ec_add_in_circuit_handles_infinity_lhs() {
        let g = grumpkin_generator();
        let (gx, gy) = g.xy().unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::new();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&map));
        builder.finish_public_pass();

        let p1 = alloc_point(&mut builder, Fr::zero(), Fr::zero(), true);
        let p2 = alloc_point(&mut builder, gx, gy, false);
        let sum = ec_add_in_circuit(&mut builder, &p1, &p2).unwrap();
        cs.finalize();
        let cs_ref = cs.borrow().unwrap();
        assert_eq!(assigned(&cs_ref, sum.x), gx);
        assert_eq!(assigned(&cs_ref, sum.y), gy);
        assert_eq!(assigned(&cs_ref, sum.is_infinity), Fr::zero());
        drop(cs_ref);
        assert!(cs.is_satisfied().unwrap(), "ec_add inf lhs");
    }

    #[test]
    fn ec_add_in_circuit_handles_infinity_rhs() {
        let g = grumpkin_generator();
        let (gx, gy) = g.xy().unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::new();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&map));
        builder.finish_public_pass();

        let p1 = alloc_point(&mut builder, gx, gy, false);
        let p2 = alloc_point(&mut builder, Fr::zero(), Fr::zero(), true);
        let sum = ec_add_in_circuit(&mut builder, &p1, &p2).unwrap();
        cs.finalize();
        let cs_ref = cs.borrow().unwrap();
        assert_eq!(assigned(&cs_ref, sum.x), gx);
        assert_eq!(assigned(&cs_ref, sum.y), gy);
        assert_eq!(assigned(&cs_ref, sum.is_infinity), Fr::zero());
        drop(cs_ref);
        assert!(cs.is_satisfied().unwrap(), "ec_add inf rhs");
    }

    #[test]
    fn ec_add_in_circuit_handles_inverse() {
        // G + (-G) = infinity.
        let g = grumpkin_generator();
        let neg_g = (-g.into_group()).into_affine();
        let (gx, gy) = g.xy().unwrap();
        let (nx, ny) = neg_g.xy().unwrap();
        assert_eq!(nx, gx);
        assert_eq!(ny, -gy);

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::new();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&map));
        builder.finish_public_pass();

        let p1 = alloc_point(&mut builder, gx, gy, false);
        let p2 = alloc_point(&mut builder, nx, ny, false);
        let sum = ec_add_in_circuit(&mut builder, &p1, &p2).unwrap();
        cs.finalize();
        let cs_ref = cs.borrow().unwrap();
        assert_eq!(assigned(&cs_ref, sum.is_infinity), Fr::one());
        drop(cs_ref);
        assert!(cs.is_satisfied().unwrap(), "ec_add inverse case");
    }

    #[test]
    fn msm_in_circuit_single_point_small_scalar() {
        // 5 * G via MSM should equal 5G computed natively.
        let g = grumpkin_generator();
        let (gx, gy) = g.xy().unwrap();
        let expected = msm_native(&[g], &[BigUint::from(5u64)]);
        let (ex, ey) = expected.xy().unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::new();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&map));
        builder.finish_public_pass();

        let point = alloc_point(&mut builder, gx, gy, false);
        let lo = builder.alloc_with_value(Some(Fr::from(5u64))).unwrap();
        let hi = builder.alloc_with_value(Some(Fr::zero())).unwrap();
        let result = msm_in_circuit(
            &mut builder,
            &[point],
            &[(lo, Some(Fr::from(5u64)), hi, Some(Fr::zero()))],
        )
        .unwrap();
        cs.finalize();
        let cs_ref = cs.borrow().unwrap();
        assert_eq!(assigned(&cs_ref, result.x), ex);
        assert_eq!(assigned(&cs_ref, result.y), ey);
        assert_eq!(assigned(&cs_ref, result.is_infinity), Fr::zero());
        drop(cs_ref);
        assert!(cs.is_satisfied().unwrap(), "msm single small");
    }

    #[test]
    fn msm_in_circuit_two_points() {
        // 3 * G + 7 * 2G = (3 + 14) * G = 17 * G.
        let g = grumpkin_generator();
        let two_g = ec_double_native(g);
        let (gx, gy) = g.xy().unwrap();
        let (tx, ty) = two_g.xy().unwrap();
        let expected = msm_native(&[g, two_g], &[BigUint::from(3u64), BigUint::from(7u64)]);
        let (ex, ey) = expected.xy().unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::new();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&map));
        builder.finish_public_pass();

        let p1 = alloc_point(&mut builder, gx, gy, false);
        let p2 = alloc_point(&mut builder, tx, ty, false);

        let lo1 = builder.alloc_with_value(Some(Fr::from(3u64))).unwrap();
        let hi1 = builder.alloc_with_value(Some(Fr::zero())).unwrap();
        let lo2 = builder.alloc_with_value(Some(Fr::from(7u64))).unwrap();
        let hi2 = builder.alloc_with_value(Some(Fr::zero())).unwrap();

        let result = msm_in_circuit(
            &mut builder,
            &[p1, p2],
            &[
                (lo1, Some(Fr::from(3u64)), hi1, Some(Fr::zero())),
                (lo2, Some(Fr::from(7u64)), hi2, Some(Fr::zero())),
            ],
        )
        .unwrap();
        cs.finalize();
        let cs_ref = cs.borrow().unwrap();
        assert_eq!(assigned(&cs_ref, result.x), ex);
        assert_eq!(assigned(&cs_ref, result.y), ey);
        assert_eq!(assigned(&cs_ref, result.is_infinity), Fr::zero());
        drop(cs_ref);
        assert!(cs.is_satisfied().unwrap(), "msm two points");
    }

    /// Constraint count for one EC add.
    #[test]
    fn report_ec_add_constraints() {
        let g = grumpkin_generator();
        let two_g = ec_double_native(g);
        let (gx, gy) = g.xy().unwrap();
        let (tx, ty) = two_g.xy().unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::new();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&map));
        builder.finish_public_pass();
        let p1 = alloc_point(&mut builder, gx, gy, false);
        let p2 = alloc_point(&mut builder, tx, ty, false);
        let before = cs.num_constraints();
        let _sum = ec_add_in_circuit(&mut builder, &p1, &p2).unwrap();
        let after = cs.num_constraints();
        eprintln!("ec_add constraints: {}", after - before);
    }

    /// Constraint count for a 1-point MSM (256-bit scalar), for the report.
    #[test]
    fn report_msm_single_constraints() {
        let g = grumpkin_generator();
        let (gx, gy) = g.xy().unwrap();
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::new();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&map));
        builder.finish_public_pass();
        let point = alloc_point(&mut builder, gx, gy, false);
        let lo = builder.alloc_with_value(Some(Fr::from(5u64))).unwrap();
        let hi = builder.alloc_with_value(Some(Fr::zero())).unwrap();
        let before = cs.num_constraints();
        let _result = msm_in_circuit(
            &mut builder,
            &[point],
            &[(lo, Some(Fr::from(5u64)), hi, Some(Fr::zero()))],
        )
        .unwrap();
        let after = cs.num_constraints();
        eprintln!("1-point MSM constraints: {}", after - before);
    }

    /// Emit generator and `2G` as decimal `Fr` strings. Used to populate the
    /// Noir `Prover.toml` for `crates/tests/circuits/curve_basic/`. Gated behind
    /// `--ignored` so it doesn't pollute normal CI output.
    #[test]
    #[ignore]
    fn print_generator_and_2g_decimal() {
        let g = grumpkin_generator();
        let (gx, gy) = g.xy().unwrap();
        let g2 = ec_double_native(g);
        let (tx, ty) = g2.xy().unwrap();
        println!("G.x = {}", crate::field::fr_to_decimal_string(&gx));
        println!("G.y = {}", crate::field::fr_to_decimal_string(&gy));
        println!("2G.x = {}", crate::field::fr_to_decimal_string(&tx));
        println!("2G.y = {}", crate::field::fr_to_decimal_string(&ty));
    }

    #[test]
    fn random_scalars_match_native() {
        // Pick a random small scalar and a random Grumpkin point, check
        // that the in-circuit MSM matches the native one.
        let mut rng = ark_std::test_rng();
        let g = grumpkin_generator();
        let factor = u64::rand(&mut rng) % 1024;
        let point = ec_add_native(g, g); // 2G
        let expected = msm_native(&[point], &[BigUint::from(factor)]);
        let (gx, gy) = point.xy().unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::new();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&map));
        builder.finish_public_pass();
        let cp = alloc_point(&mut builder, gx, gy, false);
        let lo = builder.alloc_with_value(Some(Fr::from(factor))).unwrap();
        let hi = builder.alloc_with_value(Some(Fr::zero())).unwrap();
        let res = msm_in_circuit(
            &mut builder,
            &[cp],
            &[(lo, Some(Fr::from(factor)), hi, Some(Fr::zero()))],
        )
        .unwrap();
        cs.finalize();
        let cs_ref = cs.borrow().unwrap();
        if expected.is_zero() {
            assert_eq!(assigned(&cs_ref, res.is_infinity), Fr::one());
        } else {
            let (ex, ey) = expected.xy().unwrap();
            assert_eq!(assigned(&cs_ref, res.x), ex);
            assert_eq!(assigned(&cs_ref, res.y), ey);
            assert_eq!(assigned(&cs_ref, res.is_infinity), Fr::zero());
        }
        drop(cs_ref);
        assert!(cs.is_satisfied().unwrap());
    }
}
