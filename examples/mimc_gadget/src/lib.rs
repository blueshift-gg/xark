#![no_std]

use xark::{assert_eq, Field, Private, Public};
use xark_mimc::mimc_bn254;

/// Prove knowledge of a MiMC-BN254 hash preimage: `mimc_bn254([x, k]) == h`.
///
/// The entire hash is imported from the `xark-mimc` gadget crate (a faithful
/// port of `noir-lang/mimc`: MiMC-p/p, exponent 7, 91 rounds); the compiler
/// inlines it across the crate boundary into this circuit.
pub fn circuit(x: Private<Field>, k: Private<Field>, h: Public<Field>) {
    assert_eq(mimc_bn254([x, k]), h);
}
