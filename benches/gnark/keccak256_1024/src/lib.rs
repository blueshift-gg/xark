//! The benchmark's long Keccak-256: `examples/keccak256` over a private message
//! of 1024 bytes, 8 blocks once padded. gnark's `std/hash/sha3` pays for its
//! lookup tables once a circuit, so one block shows it at its worst; this shows
//! the cost of a block.
use xark_keccak::prelude::*;

#[circuit]
pub fn keccak256_1024(msg: Private<[u8; 1024]>, digest: Public<Hash>) {
    require_eq(xark_keccak::keccak256(msg), digest);
}

#[cfg(test)]
mod tests {
    use super::keccak256_1024;
    use sha3::{Digest, Keccak256};

    /// `inputs.json`: the bytes 0, 1, …, 255, four times over; `pure/main.go`
    /// hashes the same.
    fn msg() -> [u8; 1024] {
        core::array::from_fn(|i| i as u8)
    }

    #[test]
    fn accepts_valid() {
        let digest: [u8; 32] = Keccak256::digest(msg()).into();
        keccak256_1024(msg(), digest).unwrap();
    }

    #[test]
    fn rejects_wrong_digest() {
        let mut digest: [u8; 32] = Keccak256::digest(msg()).into();
        digest[0] ^= 1;
        assert!(keccak256_1024(msg(), digest).is_err());
    }
}
