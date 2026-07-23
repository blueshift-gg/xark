
use xark::prelude::*;

/// Field inverse as an *advice* gadget.
///
/// `1/x` cannot be computed with `+ - *`, so the prover supplies it as advice
/// and the circuit only verifies `x * w == 1`. This is the canonical shape for
/// every non-algebraic gadget (is_zero, bit-decomposition, range checks, ...).
fn inv(x: Field) -> Field {
    let w = Field::hint_inverse(x); // witness-gen records `w = 1/x`
    require_eq(x * w, Field::constant("1"));
    w
}

/// Prove that the public `x_inv` really is the inverse of the private `x`.
#[circuit]
pub fn inverse(x: Private<Field>, x_inv: Public<Field>) {
    require_eq(inv(x), x_inv);
}

#[cfg(test)]
mod tests {
    use super::inverse;

    #[test]
    fn accepts_valid() {
        // 1⁻¹ = 1
        inverse("1".into(), "1".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(inverse("1".into(), "2".into()).is_err());
    }
}
