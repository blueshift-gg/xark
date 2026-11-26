//! RSA-2048 PKCS#1 v1.5 SHA-256 verification, with the host doing the decoding.
//!
//! The test vector is a real signature from the iAM Smart PKI: the leaf
//! certificate `CN=IAM SMART` signed by `ID-CERT SIGNING CA CERT 3`. The host
//! extracts the TBSCertificate bytes, hashes them with SHA-256, and decodes the
//! issuer's 2048-bit modulus and the certificate's 2048-bit signature. The
//! circuit receives only the modulus, the signature, and the digest.

use xark::prelude::*;
use xark_rsa::prelude::*;

#[circuit]
pub fn rsa2048(n: Public<U2048>, sig: Private<U2048>, digest: Public<[u8; 32]>) {
    xark_rsa::verify_sha256(n, sig, digest);
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::{Digest, Sha256};

    /// Issuer (`ID-CERT SIGNING CA CERT 3`) RSA-2048 modulus.
    const N_HEX: &str = "0xB74D4050E5CF00D346155882720815975CEBDB78AF0DAB899CF329416ADE0AD119BA89DE657F1DF84C75182356405CB6A7BB75455F54353D839555AE608774694D7C832BBE12CAE6EE22CA1BFC27DC25F38DF8CC9FE318D128C0973F069CBB54466E0D95F0ADEBC67F52FE69F076792AFE87BC4FF45083C378F2DB6B63D0D4AF25F309654219C71F42C69F1673850D193786E5011524AC8B4CC4E7EB496A57331831A5C3646D9B7EAB1F70816C72077E057C273F3CA12FC468E1921AC856892AEA47F674F18347A687DE8CA29A9C81DFCFBAEAEE72272F37B552306770FCF3B2756726782291708A0616CEDC36A09E7E428157D8FCB29A748568A0A089F5B031";
    /// Signature of the leaf certificate's TBS under that modulus.
    const SIG_HEX: &str = "0xaef25a19594b31a5ba05d24938db1f19fd6576f7369b413f5a8a38c7a12b33d09e09b2f0907e2ad409a73c55d15991040f55357c1e6f2b1fe773cea79e6d45b69ad4af84e039ca1dfcb69f6238ef67bc19990eb532cfce1cc6138891a3924ad13b8c480a930f1c6293b9a470937dcf91ab0cc41ba1a3f23cc63598d2c2a41dbbbf1105bab494e714a79dc33b210ca47464610d47b203cf9f86f8d696dbcbbaa78c88adb0e0224be8bc55af725ec0f7227e0e94b9b3242a9bc46ad3789f4d268cd8906270fa27a9e5c2d071703b02c891a06a001fe39c1c7eb2ea9424fa51ee46770901a2c041007994119a095c58b74304e51fa68ce2ab6a449e2e91305769c2";
    /// SHA-256 of the leaf certificate's TBSCertificate TLV.
    const DIGEST_HEX: &str = "c37a1c1585bccadb102bba2ee173596132d6a355e9dbf4921096564937f690be";

    fn n() -> U2048 {
        N_HEX.into()
    }

    fn sig() -> U2048 {
        SIG_HEX.into()
    }

    fn digest() -> [u8; 32] {
        hex::decode(DIGEST_HEX).unwrap().try_into().unwrap()
    }

    #[test]
    fn kat_digest_is_sha256_of_the_leaf_tbs() {
        let tbs = include_bytes!("../../../gadgets/xark-rsa/tests/fixtures/leaf_tbs.der");
        let d: [u8; 32] = Sha256::digest(tbs).into();
        assert_eq!(d, digest());
    }

    #[test]
    fn accepts_the_real_leaf_certificate_signature() {
        rsa2048(n(), sig(), digest()).unwrap();
    }

    #[test]
    fn rejects_a_tampered_digest() {
        let mut d = digest();
        d[0] ^= 1;
        assert!(rsa2048(n(), sig(), d).is_err());
    }
}
