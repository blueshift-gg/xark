//! Grumpkin Pedersen hash example circuit.
//!
//! Hashes two private 128-bit message scalars `m0, m1` to a public Grumpkin
//! point `(hx, hy)` via `H = m0·G0 + m1·G1`, then constrains the computed point
//! to equal the claimed public output.
#![cfg_attr(xark, no_std)]

use xark_pedersen::prelude::*;

#[circuit]
pub fn pedersen(m0: Private<Field>, m1: Private<Field>, hx: Public<Field>, hy: Public<Field>) {
    let h = pedersen_hash([m0, m1]);
    assert_eq(h[0], hx);
    assert_eq(h[1], hy);
}

#[cfg(test)]
mod tests {
    use super::pedersen;

    #[test]
    fn accepts_valid() {
        // pedersen_hash([m0, m1]) reference vector
        pedersen("1512366075204170929049582354406559215".into(), "338770000845734292534325025077361652240".into(), "56611582869820574239993287487223071380142614942819473392064448158736499405".into(), "14972036576598595980490710075994278492926559370076661242801210938371392582550".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(pedersen("1512366075204170929049582354406559215".into(), "338770000845734292534325025077361652240".into(), "56611582869820574239993287487223071380142614942819473392064448158736499405".into(), "1".into()).is_err());
    }
}
