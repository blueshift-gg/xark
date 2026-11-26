//! Raw-limb RSA-2048 fixture for the harness test.
use xark::{Field, Private, Public, circuit};
use xark_rsa::verify_sha256_limbs;

#[circuit]
pub fn rsa2048(n: Public<[Field; 17]>, sig: Private<[Field; 17]>, digest: Public<[u8; 32]>) {
    verify_sha256_limbs(n, sig, digest);
}
