use xark::{Field, Private, circuit};

/// `xark_ed25519::ed_double_check` on fresh limbs.
#[circuit]
pub fn ed_double_check(
    x: Private<[Field; 8]>,
    y: Private<[Field; 8]>,
    s: Private<[Field; 8]>,
    u: Private<[Field; 8]>,
    x2: Private<[Field; 8]>,
    y2: Private<[Field; 8]>,
) {
    xark_ed25519::ed_double_check(x, y, s, u, x2, y2);
}
