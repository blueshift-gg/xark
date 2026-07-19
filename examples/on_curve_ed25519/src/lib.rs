//! Assert an Ed25519 point `q = (x, y)` lies on the twisted-Edwards curve
//! `−x² + y² = 1 + d·x²·y²`, as a `#[circuit]`. This is the `enforce_on_curve`
//! check `eddsa_verify` runs on its `A`/`R` point inputs. `Point` is the
//! transparent compact uncompressed `[u8; 64]` (`x ‖ y`) type; the test uses the
//! Ed25519 basepoint as a known on-curve point.
#![cfg_attr(not(any(test, feature = "host")), no_std)]

use xark::{circuit, Public};
use xark_ed25519::{enforce_on_curve, Point};

#[circuit]
pub fn on_curve_ed25519(q: Public<Point>) {
    enforce_on_curve(q);
}

#[cfg(test)]
mod tests {
    use super::on_curve_ed25519;
    use xark_ed25519::base_be;

    #[test]
    fn accepts_on_curve() {
        on_curve_ed25519(base_be()).unwrap();
    }

    #[test]
    fn rejects_off_curve() {
        let mut q = base_be();
        q[63] ^= 1; // perturb y → off the curve
        assert!(on_curve_ed25519(q).is_err());
    }
}
