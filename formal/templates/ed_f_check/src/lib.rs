use xark::{Field, Private, circuit};

/// `xark_ed25519::ed_f_check` on fresh limbs.
#[circuit]
pub fn ed_f_check(x: Private<[Field; 8]>, y: Private<[Field; 8]>, f: Private<[Field; 8]>) {
    xark_ed25519::ed_f_check(x, y, f);
}
