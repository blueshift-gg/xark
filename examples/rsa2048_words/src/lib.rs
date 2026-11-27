//! RSA-2048 PKCS#1 v1.5 SHA-256 verification on the 17×121 whole-number API.
//!
//! The modulus and signature are whole numbers split into 17 little-endian
//! 121-bit limbs by the input reader (each limb range-checked); `convert_wide`
//! re-limbs them to the 25×82 chain. This is the `verify_sha256` entry point,
//! where [`verify_sha256_bytes`] is the octet-string one used by `rsa2048`.

use xark::prelude::*;
use xark_rsa::U2048;

#[circuit]
pub fn rsa2048_words(n: Public<U2048>, sig: Private<U2048>, digest: Public<[u8; 32]>) {
    xark_rsa::verify_sha256(n, sig, digest);
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::{Digest, Sha256};

    /// The `rsa2048` example's generated test key.
    const N_HEX: &str = "0xB4AFCE0C2B5961134236B5BA13AD4F12588F46BA02BA0724B9FBDC14800ECEE5FD90FA573EBBE10613B48A6784FBB85FF2DD527B765BB9041168DF35E45BCD8244E689C32F2829D0EB323761A3F1BC6F71DBDC96D08D8CBDF12264941219178B2A93A8963DABB80679D8613DC346E0D29420E97F889216C9555AC533904B4364E8C06FA81C44C7DC70ECE28372D543FE7CD14B2A9D5516D6A299FBEC68CA553305EBD79C5F113812A785C1CE679513AC234F7786A1E871833FED75A8778CF741452915F4A979792C9FA22AF82F60785CFB9CA0A3437A9F90C657E8590340958A6A8C2CEDD7E7714135C030844542A9EC88137346A97EDDE441630B7D2B6AD3AF";
    const SIG_HEX: &str = "0x7cde0ace8e6e4f3e4b55c6902d73d092a3581f04ec44f9cccd0bf5e1838b66e46a0927bd52ad223547c0e757175641c07ae543319f69644c27a6151cc228a900f29f23c2178ac0b319de2a1887815592805d0f52298fd7d0bad7a71e803aeff3e628b397355e66ecf4cddfa730f5e25e5ab93438611e68bf147a18e0cbe051346f5450c91e554d99eea8d3f6055f380a2ab9f969f20d971391f6a578f6e139c6ecff44884d46891cde5bfc61a2cf438f20f9a82f76e6bdd0c206498598197005e96bddbb80a65733ccb9111206b4e6a7658499900c285fd0f304128e5f1143ebb013762acda4c3681b4c03859dd336a3b0abe959a6e02cb24147f8d06d127b0a";
    const DIGEST_HEX: &str = "715976a685083f4be3a60e926f9e31a5b671a4a389b4cf709afb4c0c41c96baa";
    const MESSAGE: &[u8] = b"xark RSA-2048 PKCS#1 v1.5 SHA-256 generic test vector";

    fn n() -> U2048 {
        U2048::from(N_HEX)
    }

    fn sig() -> U2048 {
        U2048::from(SIG_HEX)
    }

    fn digest() -> [u8; 32] {
        hex::decode(DIGEST_HEX).unwrap().try_into().unwrap()
    }

    #[test]
    fn digest_is_sha256_of_the_test_message() {
        let d: [u8; 32] = Sha256::digest(MESSAGE).into();
        assert_eq!(d, digest());
    }

    #[test]
    fn accepts_the_generated_rsa_signature() {
        rsa2048_words(n(), sig(), digest()).unwrap();
    }

    #[test]
    fn rejects_a_tampered_digest() {
        let mut d = digest();
        d[0] ^= 1;
        assert!(rsa2048_words(n(), sig(), d).is_err());
    }
}
