//! Grumpkin multi-scalar-multiplication as a `#[circuit]`: constrain
//! `R = s0·P0 + s1·P1` for two 128-bit scalars and two witness points.
//!
//! Grumpkin's base field is BN254's scalar field (the circuit `Field`), so a
//! point is just two native field coordinates — the transparent `Affine` type
//! (`x`/`y` as decimal strings on the host, no limbs). A test/prover passes the
//! scalars and points as native field values.
#![cfg_attr(xark, no_std)]

use xark_grumpkin::prelude::*;

#[circuit]
pub fn grumpkin(
    s0: Public<Field>,
    s1: Public<Field>,
    p0: Public<Affine>,
    p1: Public<Affine>,
    r: Public<Affine>,
) {
    let out = multi_scalar_mul([s0, s1], [[p0.x, p0.y], [p1.x, p1.y]]);
    assert_eq(out[0], r.x);
    assert_eq(out[1], r.y);
}

#[cfg(test)]
mod tests {
    use super::grumpkin;

    // Reference vector (scratchpad `gref.py`): R = s0·P0 + s1·P1, N_BITS = 128.
    const S0: &str = "1512366075204170929049582354406559215";
    const S1: &str = "338770000845734292534325025077361652240";
    const P0: [&str; 2] = [
        "8",
        "17211924001480414201552586258339381047922154443519291062668150353239757288029",
    ];
    const P1: [&str; 2] = [
        "10",
        "3764497608137669826449761938357951019955713832105137848030504861970310222496",
    ];
    const R: [&str; 2] = [
        "18795281547672131371183968279919782939389077073414573264326681878560793134719",
        "2414680004978840508961516437196481407162521166594374623807266823818455121132",
    ];

    fn pt(p: [&str; 2]) -> [String; 2] {
        [p[0].into(), p[1].into()]
    }

    #[test]
    fn accepts_valid() {
        grumpkin(S0.into(), S1.into(), pt(P0), pt(P1), pt(R)).unwrap();
    }

    #[test]
    fn rejects_tampered() {
        let bad_r = [String::from("123"), R[1].into()];
        assert!(grumpkin(S0.into(), S1.into(), pt(P0), pt(P1), bad_r).is_err());
    }
}
