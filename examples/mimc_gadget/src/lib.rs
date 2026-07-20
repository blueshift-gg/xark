#![cfg_attr(xark, no_std)]

use xark_mimc::prelude::*;

/// Prove knowledge of a MiMC-BN254 hash preimage: `mimc_bn254([x, k]) == h`.
///
/// The entire hash is imported from the `xark-mimc` gadget crate (a faithful
/// port of `noir-lang/mimc`: MiMC-p/p, exponent 7, 91 rounds); the compiler
/// inlines it across the crate boundary into this circuit.
#[circuit]
pub fn mimc_gadget(x: Private<Field>, k: Private<Field>, h: Public<Field>) {
    assert_eq(mimc_bn254([x, k]), h);
}

#[cfg(test)]
mod tests {
    use super::mimc_gadget;

    #[test]
    fn accepts_valid() {
        // mimc_bn254([3, 5])
        mimc_gadget("3".into(), "5".into(), "45829284839521097241407480053690972327868918845246359604235530970166825256".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(mimc_gadget("3".into(), "5".into(), "1".into()).is_err());
    }
}
