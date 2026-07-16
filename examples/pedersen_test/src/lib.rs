//! Native-typed `#[circuit]` inputs over a Grumpkin Pedersen hash — prove
//! knowledge of the two field pre-images `(m0, m1)` of a Pedersen point.
//!
//! Validated against `ark-grumpkin`: the test reproduces xark-pedersen's
//! nothing-up-my-sleeve generators (`Gᵢ = hash_to_curve("xark-pedersen:generator:i")`)
//! and checks the circuit output equals `m0·G0 + m1·G1` computed with the real
//! curve library — the same cross-implementation guarantee sha256 gets from `sha2`.
//! The output is a curve point `[x, y]`, so `result` is two public field
//! coordinates rather than a packed `Hash`.

#![cfg_attr(not(any(test, feature = "host")), no_std)]

use xark::{circuit, Private, Public};
use xark_pedersen::pedersen_hash;

#[circuit]
pub fn pedersen_test(m0: Private<Field>, m1: Private<Field>, x: Public<Field>, y: Public<Field>) {
    let h = pedersen_hash([m0, m1]);
    assert_eq(h[0], x);
    assert_eq(h[1], y);
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::PrimeField;
    use ark_grumpkin::{Affine, Fq, Fr};
    use sha2::{Digest, Sha256};
    use std::str::FromStr;

    /// The same nothing-up-my-sleeve derivation `xark-pedersen` uses: try-and-
    /// increment from `x = SHA256(domain)` on Grumpkin, taking the smaller `y`.
    fn hash_to_curve(domain: &str) -> Affine {
        let mut ctr = 0u32;
        loop {
            let mut h = Sha256::new();
            h.update(domain.as_bytes());
            h.update(ctr.to_be_bytes());
            let x = Fq::from_be_bytes_mod_order(&h.finalize());
            if let Some(p) = Affine::get_point_from_x_unchecked(x, false) {
                return p;
            }
            ctr += 1;
        }
    }

    /// Reference `H = m0·G0 + m1·G1` over the derived generators, as `(x, y)` decimals.
    fn reference(m0: &str, m1: &str) -> (String, String) {
        let g0 = hash_to_curve("xark-pedersen:generator:0");
        let g1 = hash_to_curve("xark-pedersen:generator:1");
        let h = (g0 * Fr::from_str(m0).unwrap() + g1 * Fr::from_str(m1).unwrap()).into_affine();
        (h.x().unwrap().to_string(), h.y().unwrap().to_string())
    }

    const M0: &str = "1512366075204170929049582354406559215";
    const M1: &str = "338770000845734292534325025077361652240";

    #[test]
    fn accepts_valid() {
        let (x, y) = reference(M0, M1);
        pedersen_test(M0.into(), M1.into(), x, y).unwrap();
    }

    #[test]
    fn rejects_invalid() {
        let (_, y) = reference(M0, M1);
        assert!(pedersen_test(M0.into(), M1.into(), "123".into(), y).is_err());
    }
}
