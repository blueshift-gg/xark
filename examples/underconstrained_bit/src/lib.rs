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
#![cfg_attr(xark, no_std)]

use xark::{assert_eq, circuit, Field, Private, Public};

#[circuit]
pub fn underconstrained_bit(x: Private<Field>, out: Public<Field>) {
    let b = Field::hint_bit(x, 0);
    b.assert_bool(); // booleanity only: references `b` but leaves it two-valued
    assert_eq(x, out);
}

#[cfg(test)]
mod tests {
    use super::underconstrained_bit;

    // Intentionally unsound (see the module doc): `b` is pinned boolean but not
    // tied to the real bit of `x`. `check` verifies constraint *satisfaction*, not
    // uniqueness, so the two-valued `b` is caught by `xark prove`'s under-constraint
    // analyzer — see the `underconstrained_bit` snapshot test. What `check` asserts
    // here is that a mismatched output still fails, the *expected* rejection.
    #[test]
    fn rejects_mismatched_output() {
        assert!(underconstrained_bit("5".into(), "6".into()).is_err());
    }
}
