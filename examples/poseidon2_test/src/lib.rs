//! Native-typed `#[circuit]` inputs over a Poseidon2 hash — prove knowledge of the
//! two field pre-images of a Poseidon2-BN254 (t=3) hash.
//!
//! The expected digest isn't hardcoded: it's computed with HorizenLabs' reference
//! `zkhash` crate (whose BN256 parameters `xark-poseidon2` transcribes), the same
//! way the SHA-256 example checks against `sha2`. `hash2(a, b)` is
//! `poseidon2_perm([a, b, 0])[0]`, so the reference is that permutation over `[a,
//! b, 0]`, element 0.

#![cfg_attr(not(any(test, feature = "host")), no_std)]

use xark::{circuit, Private, Public};
use xark_poseidon2::hash2;

#[circuit]
pub fn poseidon2_test(a: Private<Field>, b: Private<Field>, result: Public<Field>) {
    assert_eq(hash2(a, b), result);
}

#[cfg(test)]
mod tests {
    use super::poseidon2_test;
    use zkhash::fields::bn256::FpBN256;
    use zkhash::poseidon2::poseidon2::Poseidon2;
    use zkhash::poseidon2::poseidon2_instance_bn256::POSEIDON2_BN256_PARAMS;

    /// The reference `hash2(a, b) = poseidon2_perm([a, b, 0])[0]` via HorizenLabs'
    /// `zkhash`, as a decimal string.
    fn reference_hash2(a: u64, b: u64) -> String {
        let perm = Poseidon2::new(&POSEIDON2_BN256_PARAMS);
        let out = perm.permutation(&[FpBN256::from(a), FpBN256::from(b), FpBN256::from(0u64)]);
        out[0].to_string()
    }

    #[test]
    fn accepts_valid() {
        poseidon2_test("2".into(), "3".into(), reference_hash2(2, 3)).unwrap();
    }

    #[test]
    fn rejects_invalid() {
        assert!(poseidon2_test("2".into(), "4".into(), reference_hash2(2, 3)).is_err());
    }
}
