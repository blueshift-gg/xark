use xark::{Field, Private, circuit};

/// `xark_ed25519::ed_torsion_check` on fresh limbs.
#[circuit]
pub fn ed_torsion_check(
    x: Private<[Field; 8]>,
    y: Private<[Field; 8]>,
    s: Private<[Field; 8]>,
    u: Private<[Field; 8]>,
    m: Private<[Field; 8]>,
) {
    xark_ed25519::ed_torsion_check(x, y, s, u, m);
}
