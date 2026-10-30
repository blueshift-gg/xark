#![cfg_attr(xark, no_std)]

use xark_poseidon::pinned::hash2;
use xark_poseidon::prelude::*;

/// The `poseidon` example on `xark_poseidon::pinned::hash2`: the same relation
/// and the same digest, with the partial-round lanes pinned. 240 S-box gates
/// plus 112 linear pins, and a witness solve light enough to run by default.
#[circuit]
pub fn poseidon_pinned(a: Private<Field>, b: Private<Field>, out: Public<Field>) {
    require_eq(hash2(a, b), out);
}

#[cfg(test)]
mod tests {
    use super::poseidon_pinned as poseidon;

    #[test]
    fn accepts_valid() {
        // poseidon.hash2(3, 5)
        poseidon(
            "3".into(),
            "5".into(),
            "7003178825990875955236852857865616475160076985313430133088248668396799513116".into(),
        )
        .unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(poseidon("3".into(), "5".into(), "1".into()).is_err());
    }
}
