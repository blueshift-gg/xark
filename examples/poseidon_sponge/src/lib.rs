//! Variable-length hashing with the Poseidon **sponge** (`hash::<N>`). `N` is a
//! compile-time constant; here we hash 5 private inputs and expose the digest.
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
    fn accepts_valid() {
        // poseidon sponge hash([1..5])
        poseidon_sponge(
            1,
            2,
            3,
            4,
            5,
            "11125748760708140916786033670969375031496395171002607896175853736491095949636",
        )
        .unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(poseidon_sponge(
            1,
            2,
            3,
            4,
            5,
            1
        )
        .is_err());
    }
}
