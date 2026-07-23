//! Variable-length hashing with the Poseidon2 **sponge** (`hash::<N>`). A circuit
//! is fixed-size, so the element count `N` is a compile-time constant and the
//! absorb loop unrolls. Here we hash 5 private inputs and expose the digest.
use xark_poseidon2::prelude::*;

#[circuit]
pub fn poseidon2_sponge(
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
    use super::poseidon2_sponge;

    #[test]
    fn accepts_valid() {
        // poseidon2 sponge hash([1..5])
        poseidon2_sponge(
            "1".into(),
            "2".into(),
            "3".into(),
            "4".into(),
            "5".into(),
            "8828141863764826539393608139805007447022200187560478202710690249571019683634".into(),
        )
        .unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(poseidon2_sponge(
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
