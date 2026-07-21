//! **Intentionally unsound** circuit: a witness-based under-constraint the
//! structural build-time pin check (`lower_mir::check_pinning`) cannot catch.
//!
//! `b` is hinted to bit 0 of `x` and only pinned boolean (`b*b == b`). That
//! constraint references `b` so the structural gate is satisfied, but booleanity
//! alone leaves `b` two-valued and nothing pins it to the actual bit of `x` — a
//! prover could flip `b` freely. `xark_ir::solver::analyze_underconstrained`
//! catches this from the solved witness, so `xark prove` must reject it.
//!
//! Contrast `examples/to_bits`, which recomposes the bits (`Σ bitᵢ·2ⁱ == x`) —
//! that recomposition pins every bit and proves clean.
#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};

#[circuit]
pub fn underconstrained_bit(x: Private<Field>, out: Public<Field>) {
    let b = Field::hint_bit(x, 0);
    b.require_bool(); // booleanity only: leaves `b` two-valued
    require_eq(x, out);
}

#[cfg(test)]
mod tests {
    use super::underconstrained_bit;

    // `check` verifies constraint satisfaction, not uniqueness (the under-constraint
    // is caught by `xark prove`; see the module doc). This test only asserts that a
    // mismatched output still fails — the expected rejection.
    #[test]
    fn rejects_mismatched_output() {
        assert!(underconstrained_bit("5".into(), "6".into()).is_err());
    }
}
