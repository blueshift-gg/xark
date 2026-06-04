// Embedded-curve (Grumpkin) basic example. Exercises both
// `BlackBoxFuncCall::EmbeddedCurveAdd` and `BlackBoxFuncCall::MultiScalarMul`
// end-to-end (ROADMAP step WS-D.5).
//
// The Noir stdlib's `EmbeddedCurvePoint` carries only `(x, y)`; the
// `is_infinite` flag that the ACIR opcode takes is derived by Noir's compiler
// from `(x == 0) & (y == 0)`, which lowers to a `BrilligCall` (inverse hint).
// To stay within WS-D.5's scope (no Brillig lowering yet), we build the points
// from the curve generator helper, which Noir's optimizer simplifies away
// before emitting Brillig.
use std::embedded_curve_ops::{
    embedded_curve_add, multi_scalar_mul, EmbeddedCurvePoint, EmbeddedCurveScalar,
};

fn main(scalar_lo: Field, expected_x: pub Field, expected_y: pub Field) {
    let g = EmbeddedCurvePoint::generator();

    // EmbeddedCurveAdd: g + g.
    let sum = embedded_curve_add(g, g);
    assert(sum.x == expected_x);
    assert(sum.y == expected_y);

    // MultiScalarMul: scalar_lo * g (private scalar, public expected point).
    let s = EmbeddedCurveScalar { lo: scalar_lo, hi: 0 };
    let msm = multi_scalar_mul([g], [s]);
    assert(msm.x == expected_x);
    assert(msm.y == expected_y);
}
