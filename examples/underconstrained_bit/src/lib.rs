//! **Intentionally unsound** circuit: a witness-based under-constraint the
//! structural build-time pinning gate (`xark-frontend`'s `check_pinning`) cannot catch.
//!
//! `b` is hinted to bit 0 of `x` and only pinned boolean (`b*b == b`). That
//! constraint references `b` so the structural gate is satisfied, but booleanity
//! alone leaves `b` two-valued and nothing pins it to the actual bit of `x` — a
//! prover could flip `b` freely. `xark_ir::solver::analyze_underconstrained`
//! catches this from the solved witness, so the circuit's tests (`check`, what
//! the generated validator runs) reject it. `xark prove` doesn't check soundness.
//!
//! Contrast `examples/to_bits`, which recomposes the bits (`Σ bitᵢ·2ⁱ == x`) —
//! that recomposition pins every bit and proves clean.
use xark::{circuit, require_eq, Field, Private, Public};

#[circuit]
pub fn underconstrained_bit(x: Private<Field>, out: Public<Field>) {
    let b = Field::hint_bit(x, 0);
    b.require_bool(); // booleanity only: leaves `b` two-valued
    require_eq(x, out);
}

#[cfg(test)]
mod tests {
    use super::{UnderconstrainedBitInputs, underconstrained_bit};

    // `check` (what `underconstrained_bit(..)` runs) also looks for free witness
    // variables, and finds `b`, even on honest inputs.
    #[test]
    fn check_finds_the_free_bit() {
        let err = underconstrained_bit(5, 5).expect_err("`b` is two-valued");
        assert!(err.to_string().contains("under-constrained"), "{err}");
    }

    // `check_satisfied` verifies constraint satisfaction alone: honest inputs
    // pass it, a mismatched output doesn't.
    #[test]
    fn honest_inputs_satisfy_it() {
        let circuit = xark::prover::circuit("underconstrained_bit");
        let inputs = |x: u64, out: u64| UnderconstrainedBitInputs {
            x: x.into(),
            out: out.into(),
        };
        assert!(circuit.check_satisfied(inputs(5, 5)).is_ok());
        assert!(circuit.check_satisfied(inputs(5, 6)).is_err());
    }
}
