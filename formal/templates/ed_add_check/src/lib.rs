use xark::{Field, Private, circuit};

/// `xark_ed25519::ed_add_check` on fresh limbs.
#[circuit]
#[allow(clippy::too_many_arguments)]
pub fn ed_add_check(
    x1: Private<[Field; 8]>,
    y1: Private<[Field; 8]>,
    x2: Private<[Field; 8]>,
    y2: Private<[Field; 8]>,
    f2: Private<[Field; 8]>,
    t: Private<[Field; 8]>,
    e: Private<[Field; 8]>,
    x3: Private<[Field; 8]>,
    y3: Private<[Field; 8]>,
) {
    xark_ed25519::ed_add_check(x1, y1, x2, y2, f2, t, e, x3, y3);
}
