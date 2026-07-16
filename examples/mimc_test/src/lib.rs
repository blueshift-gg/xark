//! Native-typed `#[circuit]` inputs over a MiMC hash — prove knowledge of the four
//! field pre-images of a MiMC-BN254 Feistel hash.

#![cfg_attr(not(any(test, feature = "host")), no_std)]

use xark::{circuit, Private, Public};
use xark_mimc::mimc_bn254;

#[circuit]
pub fn mimc_test(
    a: Private<Field>,
    b: Private<Field>,
    c: Private<Field>,
    d: Private<Field>,
    result: Public<Field>,
) {
    assert_eq(mimc_bn254([a, b, c, d]), result);
}

#[cfg(test)]
mod tests {
    use super::mimc_test;

    /// `mimc_bn254([12, 45, 78, 41])`.
    const H: &str = "18226366069841799622585958305961373004333097209608110160936134895615261821931";

    #[test]
    fn accepts_valid() {
        mimc_test("12".into(), "45".into(), "78".into(), "41".into(), H.into()).unwrap();
    }

    #[test]
    fn rejects_invalid() {
        assert!(mimc_test("12".into(), "45".into(), "78".into(), "42".into(), H.into()).is_err());
    }
}
