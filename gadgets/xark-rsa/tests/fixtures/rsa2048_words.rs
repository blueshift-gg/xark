//! Raw-limb RSA-2048 fixture taking the digest as SHA-256 output words.
use xark::{Field, Private, Public, circuit};
use xark_bignum::{Bignum, range_check_limbs};
use xark_rsa::verify_sha256_words;

#[circuit]
pub fn rsa2048_words(
    n: Public<[Field; 17]>,
    sig: Private<[Field; 17]>,
    flat: Public<[Field; 256]>,
) {
    range_check_limbs::<17, 121>(n);
    range_check_limbs::<17, 121>(sig);
    let mut words = [[Field::from(0u8); 32]; 8];
    let mut i = 0usize;
    while i < 8usize {
        let mut j = 0usize;
        while j < 32usize {
            words[i][j] = flat[32 * i + j];
            j += 1;
        }
        i += 1;
    }
    verify_sha256_words(Bignum::new(n), Bignum::new(sig), words);
}
