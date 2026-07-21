//! Validate 3-limb incomplete secp256k1 EC ops as a `#[circuit]`: `2·G == 2G`
//! and `G + 2G == 3G` (exercises the whole 3×86-bit field stack: add, sub, mul,
//! inverse). `Point` is the transparent compact uncompressed `[u8; 64]` (`x ‖ y`)
//! type, so the test passes the raw `G`/`2G`/`3G` coordinate bytes `k256` emits.
#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Private, Public};
use xark_secp256k1::affine::{ec_add_incomplete, ec_double_incomplete, Point};

fn ceq(got: Point, want: Point) {
    let mut i = 0;
    while i < 3 {
        require_eq(got.x.limbs[i], want.x.limbs[i]);
        i += 1;
    }
    let mut i = 0;
    while i < 3 {
        require_eq(got.y.limbs[i], want.y.limbs[i]);
        i += 1;
    }
}

#[circuit]
pub fn ec_incomplete(g: Private<Point>, two_g: Public<Point>, three_g: Public<Point>) {
    ceq(ec_double_incomplete(g), two_g);
    ceq(ec_add_incomplete(g, two_g), three_g);
}

#[cfg(test)]
mod tests {
    use super::ec_incomplete;
    use k256::elliptic_curve::sec1::ToEncodedPoint;
    use k256::ProjectivePoint;

    fn enc(p: ProjectivePoint) -> [u8; 64] {
        let ep = p.to_affine().to_encoded_point(false);
        ep.as_bytes()[1..].try_into().unwrap() // x ‖ y, drop 0x04 tag
    }

    /// `(G, 2G, 3G)` on secp256k1.
    fn g123() -> ([u8; 64], [u8; 64], [u8; 64]) {
        let g = ProjectivePoint::GENERATOR;
        let g2 = g.double();
        (enc(g), enc(g2), enc(g2 + g))
    }

    #[test]
    fn accepts_valid() {
        let (g, g2, g3) = g123();
        ec_incomplete(g, g2, g3).unwrap();
    }

    #[test]
    fn rejects_tampered() {
        let (g, g2, mut g3) = g123();
        g3[63] ^= 1; // wrong 3G
        assert!(ec_incomplete(g, g2, g3).is_err());
    }
}
