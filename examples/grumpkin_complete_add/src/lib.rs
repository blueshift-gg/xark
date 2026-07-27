//! **Complete (identity-safe) Grumpkin affine addition** — the missing
//! prerequisite for real Nova folding. The `xark-grumpkin` gadget's `ec_add` is
//! *incomplete* (can't represent ∞), which the fold demos sidestepped by using
//! non-identity commitments. But a fresh Nova instance has `comm_E = ∞`, so the
//! commitment fold must handle the point at infinity.
//!
//! Points are **flagged affine** `[x, y, inf]` (`inf ∈ {0,1}`; `inf=1 ⇒ (0,0)`).
//! The addition is fully branch-free — all exceptional cases (`P+∞`, `∞+Q`,
//! `P+(−P)=∞`, `P+P`, generic `P+Q`) are resolved with `is_zero` gadgets, safe
//! conditional inverses, and arithmetic muxes. Grumpkin is prime-order (no
//! 2-torsion), so `y=0` never occurs for a real point — the only ∞ is the flag.

#![cfg_attr(xark, no_std)]
#![allow(clippy::assign_op_pattern)]

use xark::prelude::*;

/// Fully-pinned inverse-or-zero: returns `(w, z)` with `w = 1/x` and `z = 0`
/// when `x ≠ 0`, and `w = 0`, `z = 1` when `x = 0`. Both branches are pinned
/// (`x·z == 0` forces `z=0`/`w=1/x` for `x≠0`; `z·w == 0` forces `w=0` for
/// `x=0`), so no free advice remains even at `x = 0`.
fn inv_or_zero(x: Field) -> (Field, Field) {
    let w = Field::hint_inverse_or_zero(x);
    let z = Field::from(1u8) - x * w;
    require_eq(x * z, Field::from(0u8));
    require_eq(z * w, Field::from(0u8));
    (w, z)
}

/// `sel ? a : b` for a boolean `sel`.
fn mux(sel: Field, a: Field, b: Field) -> Field {
    b + sel * (a - b)
}

/// Complete affine addition of flagged points `[x, y, inf]`.
fn complete_add(p: [Field; 3], q: [Field; 3]) -> [Field; 3] {
    let one = Field::from(1u8);
    let (px, py, pinf) = (p[0], p[1], p[2]);
    let (qx, qy, qinf) = (q[0], q[1], q[2]);

    // addition slope λ = (qy−py)/(qx−px); `inv_dx` is `1/dx` (or 0), pinned.
    let dx = qx - px;
    let (inv_dx, eq_x) = inv_or_zero(dx);
    let dy = qy - py;
    let (_inv_dy, eq_y) = inv_or_zero(dy);
    let lam_add = dy * inv_dx;

    // doubling slope λ = 3x²/(2y); safe even when 2y = 0 (∞ operand).
    let two_py = py + py;
    let (inv_2py, _z2) = inv_or_zero(two_py);
    let lam_dbl = (px * px * Field::from(3u8)) * inv_2py;

    // same x ⇒ doubling slope (also covers the P+(−P) branch, discarded below).
    let lam = mux(eq_x, lam_dbl, lam_add);
    let x3 = lam * lam - px - qx;
    let y3 = lam * (px - x3) - py;

    // generic result; it's ∞ exactly when p = −q (same x, different y).
    let opp = eq_x * (one - eq_y);
    let (gx, gy, ginf) = (x3, y3, opp);

    // q = ∞ ⇒ result p ; then p = ∞ ⇒ result q  (both ∞ ⇒ ∞ via the q branch).
    let rx = mux(pinf, qx, mux(qinf, px, gx));
    let ry = mux(pinf, qy, mux(qinf, py, gy));
    let rinf = mux(pinf, qinf, mux(qinf, pinf, ginf));

    // canonicalize ∞ to (0, 0).
    let notinf = one - rinf;
    [rx * notinf, ry * notinf, rinf]
}

/// Verify a claimed complete-addition `R = P + Q` of flagged Grumpkin points.
#[circuit]
#[allow(clippy::too_many_arguments)]
pub fn grumpkin_complete_add(
    px: Public<Field>,
    py: Public<Field>,
    pinf: Public<Field>,
    qx: Public<Field>,
    qy: Public<Field>,
    qinf: Public<Field>,
    rx: Public<Field>,
    ry: Public<Field>,
    rinf: Public<Field>,
) {
    let r = complete_add([px, py, pinf], [qx, qy, qinf]);
    require_eq(r[0], rx);
    require_eq(r[1], ry);
    require_eq(r[2], rinf);
}
