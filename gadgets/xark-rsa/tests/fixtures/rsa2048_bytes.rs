use xark::prelude::*;

#[circuit]
pub fn rsa2048_bytes(n: Public<[u8; 256]>, sig: Private<[u8; 256]>, digest: Public<[u8; 32]>) {
    xark_rsa::prelude::verify_sha256_bytes(n, sig, digest);
}
