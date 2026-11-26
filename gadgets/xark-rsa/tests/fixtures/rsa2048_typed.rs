use xark::prelude::*;
use xark_rsa::prelude::*;

#[circuit]
pub fn rsa2048_typed(n: Public<U2048>, sig: Private<U2048>, digest: Public<[u8; 32]>) {
    xark_rsa::verify_sha256(n, sig, digest);
}
