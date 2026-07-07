#![no_std]

use xark::{assert_eq, Field, Private, Public};
use xark_mimc::mimc3;

/// Prove knowledge of a MiMC preimage: `mimc3(x, k) == h`.
///
/// The entire hash is imported from the `xark-mimc` gadget crate; the compiler
/// inlines it into this circuit.
pub fn circuit(x: Private<Field>, k: Public<Field>, h: Public<Field>) {
    assert_eq(mimc3(x, k), h);
}
