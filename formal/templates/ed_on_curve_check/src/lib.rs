use xark::{Field, Private, circuit};

/// `xark_ed25519::ed_on_curve_check` on fresh limbs.
#[circuit]
pub fn ed_on_curve_check(
    x: Private<[Field; 8]>,
    y: Private<[Field; 8]>,
    s: Private<[Field; 8]>,
    u: Private<[Field; 8]>,
) {
    xark_ed25519::ed_on_curve_check(x, y, s, u);
}
