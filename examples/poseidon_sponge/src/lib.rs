//! Variable-length hashing with the Poseidon **sponge** (`hash::<N>`). `N` is a
//! compile-time constant; here we hash 5 private inputs and expose the digest.
#![cfg_attr(xark, no_std)]
use xark_poseidon::prelude::*;

#[circuit]
pub fn poseidon_sponge(
    a: Private<Field>,
    b: Private<Field>,
    c: Private<Field>,
    d: Private<Field>,
    e: Private<Field>,
    out: Public<Field>,
) {
    require_eq(hash::<5>([a, b, c, d, e]), out);
}

#[cfg(test)]
mod tests {
    use super::poseidon_sponge;

    #[test]
    #[ignore = "heavy: original-Poseidon solve (big-coefficient MDS-fold LCs)"]
    fn accepts_valid() {
        // poseidon sponge hash([1..5])
        poseidon_sponge(
            "1".into(),
            "2".into(),
            "3".into(),
            "4".into(),
            "5".into(),
            "11125748760708140916786033670969375031496395171002607896175853736491095949636".into(),
        )
        .unwrap();
    }

    #[test]
    #[ignore = "heavy: original-Poseidon solve (big-coefficient MDS-fold LCs)"]
    fn rejects_wrong() {
        assert!(poseidon_sponge(
            "1".into(),
            "2".into(),
            "3".into(),
            "4".into(),
            "5".into(),
            "1".into()
        )
        .is_err());
    }
}
