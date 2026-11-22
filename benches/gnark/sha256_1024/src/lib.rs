//! The benchmark's long SHA-256: `examples/sha256` over a private message of
//! 1024 bytes, 17 blocks once padded. gnark's `std/hash/sha2` pays for its lookup
//! tables once a circuit, so one block shows it at its worst; this shows the cost
//! of a block.
use xark_sha256::prelude::*;

#[circuit]
pub fn sha256_1024(msg: Private<[u8; 1024]>, digest: Public<Hash>) {
    require_eq(xark_sha256::sha256(msg), digest);
}

#[cfg(test)]
mod tests {
    use super::sha256_1024;
    use sha2::{Digest, Sha256};

    /// `inputs.json`: the bytes 0, 1, …, 255, four times over; `pure/main.go`
    /// hashes the same.
    fn msg() -> [u8; 1024] {
        core::array::from_fn(|i| i as u8)
    }

    #[test]
    fn accepts_valid() {
        let digest: [u8; 32] = Sha256::digest(msg()).into();
        sha256_1024(msg(), digest).unwrap();
    }

    #[test]
    fn rejects_wrong_digest() {
        let mut digest: [u8; 32] = Sha256::digest(msg()).into();
        digest[0] ^= 1;
        assert!(sha256_1024(msg(), digest).is_err());
    }
}
