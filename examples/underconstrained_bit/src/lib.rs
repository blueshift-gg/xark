//! **Intentionally unsound** circuit: a witness-based under-constraint the
//! structural build-time pin check (`lower_mir::check_pinning`) cannot catch.
//!
//! `b` is hinted to bit 0 of `x` and only pinned *boolean* (`b*b == b`). That
//! constraint *references* `b`, so the build-time structural gate is satisfied —
//! but booleanity alone leaves `b` **two-valued** (0 and 1 both satisfy it), and
//! nothing pins `b` to the actual bit of `x`. A malicious prover could flip `b`
//! freely. This is exactly the class `xark_ir::solver::analyze_underconstrained`
//! catches from the solved witness, so `xark prove` must reject it.
//!
//! Contrast with `examples/to_bits`, which additionally recomposes the bits
//! (`Σ bitᵢ·2ⁱ == x`) — that recomposition pins every bit and proves clean.
#![no_std]

use xark::{assert_eq, Field, Private, Public};

pub fn circuit(x: Private<Field>, out: Public<Field>) {
    let b = Field::hint_bit(x, 0);
    b.assert_bool(); // booleanity only: references `b` but leaves it two-valued
    assert_eq(x, out);
}
