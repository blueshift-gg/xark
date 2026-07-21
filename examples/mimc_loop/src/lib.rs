#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};

/// One MiMC round: `(state + key + round_constant)^3`.
fn round(state: Field, key: Field, c: Field) -> Field {
    let t = state + key + c;
    t.pow(3)
}

/// MiMC written idiomatically with a `while` loop over an array of round
/// constants. Lowers to *exactly the same* R1CS as the hand-unrolled
/// `examples/mimc`: the loop is unrolled at compile time, the `[Field; 3]`
/// constants are indexed by the counter, and `round` inlines per iteration.
#[circuit]
pub fn mimc_loop(x: Private<Field>, k: Public<Field>, h: Public<Field>) {
    let cs = [
        Field::constant("0"),
        Field::constant(
            "7120861356467033611736373842526102177239622603558704633600844922174959859415",
        ),
        Field::constant(
            "5464731394973421946722394282035800941955447322641943688940765294088180338198",
        ),
    ];

    let mut s = x;
    let mut i = 0usize;
    while i < 3 {
        s = round(s, k, cs[i]);
        i += 1;
    }

    require_eq(s + k, h);
}

#[cfg(test)]
mod tests {
    use super::mimc_loop;

    #[test]
    fn accepts_valid() {
        // same 3-round MiMC as `mimc`
        mimc_loop(
            "3".into(),
            "5".into(),
            "20571574433789244246851793328630243816385775205591326058386183977315966726389".into(),
        )
        .unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(mimc_loop("3".into(), "5".into(), "1".into()).is_err());
    }
}
