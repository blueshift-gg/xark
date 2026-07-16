//! Native-typed `#[circuit]` inputs over a Poseidon hash — prove knowledge of the
//! two field pre-images of a Poseidon-BN254 (t=3) hash.
//!
//! The expected digest is computed with HorizenLabs' reference `zkhash` crate
//! (whose BN256 parameters `xark-poseidon` transcribes), like the SHA-256 example
//! checks against `sha2`. `hash2(a, b)` is `poseidon_perm([0, a, b])[0]`.

#![cfg_attr(not(any(test, feature = "host")), no_std)]

use xark::{circuit, Private, Public};
use xark_poseidon::hash2;

#[circuit]
pub fn poseidon_test(a: Private<Field>, b: Private<Field>, result: Public<Field>) {
    assert_eq(hash2(a, b), result);
}

#[cfg(test)]
mod tests {
    use super::poseidon_test;
    use zkhash::fields::bn256::FpBN256;
    use zkhash::poseidon::poseidon::Poseidon;
    use zkhash::poseidon::poseidon_instance_bn256::POSEIDON_BN_PARAMS;

    /// The reference `hash2(a, b) = poseidon_perm([0, a, b])[0]` via HorizenLabs'
    /// `zkhash`, as a decimal string.
    fn reference_hash2(a: u64, b: u64) -> String {
        let perm = Poseidon::new(&POSEIDON_BN_PARAMS);
        let out = perm.permutation(&[FpBN256::from(0u64), FpBN256::from(a), FpBN256::from(b)]);
        out[0].to_string()
    }

    #[test]
    fn accepts_valid() {
        poseidon_test("2".into(), "3".into(), reference_hash2(2, 3)).unwrap();
    }

    #[test]
    fn rejects_invalid() {
        assert!(poseidon_test("2".into(), "4".into(), reference_hash2(2, 3)).is_err());
    }
}
