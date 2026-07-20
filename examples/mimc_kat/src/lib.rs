#![cfg_attr(xark, no_std)]

use xark_mimc::prelude::*;

/// Known-answer circuit for the real MiMC-BN254 hash (port of `noir-lang/mimc`).
///
/// Constrains the public output to `mimc_bn254([12, 45, 78, 41])`, whose Noir
/// KAT value is
/// `18226366069841799622585958305961373004333097209608110160936134895615261821931`.
/// Solving with that value must succeed; any other value must be rejected.
#[circuit]
pub fn mimc_kat(out: Public<Field>) {
    assert_eq(
        mimc_bn254([
            Field::from(12u8),
            Field::from(45u8),
            Field::from(78u8),
            Field::from(41u8),
        ]),
        out,
    );
}

#[cfg(test)]
mod tests {
    use super::mimc_kat;

    #[test]
    fn accepts_valid() {
        // mimc_bn254([12,45,78,41])
        mimc_kat("18226366069841799622585958305961373004333097209608110160936134895615261821931".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(mimc_kat("1".into()).is_err());
    }
}
