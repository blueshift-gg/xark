#![cfg_attr(xark, no_std)]

use xark::{circuit, Private, Public};
use xark_sha256::sha256;

#[circuit]
pub fn xark_sha256_test(input: Private<[u8; 4]>, result: Public<[u8; 32]>) {
    assert_eq(sha256(input), result);
}

#[cfg(test)]
mod tests {
    use super::xark_sha256_test;
    use sha2::{Digest, Sha256};

    const INPUT: [u8; 4] = *b"test";

    #[test]
    fn accepts_valid() {
        let result: [u8; 32] = Sha256::digest(INPUT).into();
        xark_sha256_test(INPUT, result).unwrap();
    }

    #[test]
    fn rejects_invalid() {
        let mut result: [u8; 32] = Sha256::digest(INPUT).into();
        result[0] ^= 1;
        assert!(xark_sha256_test(INPUT, result).is_err());
    }
}
