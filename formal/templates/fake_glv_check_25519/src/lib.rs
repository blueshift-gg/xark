use xark::{Field, Private, circuit};

/// `xark_ed25519::fake_glv_check_25519` on fresh inputs.
#[circuit]
#[allow(clippy::too_many_arguments)]
pub fn fake_glv_check_25519(
    k: Private<[Field; 4]>,
    s: Private<[Field; 4]>,
    ca: Private<Field>,
    cb: Private<Field>,
    w: Private<[Field; 4]>,
    q1: Private<[Field; 3]>,
    q2: Private<[Field; 3]>,
    h1: Private<[Field; 5]>,
    h2: Private<[Field; 5]>,
) {
    let _ = xark_ed25519::fake_glv_check_25519(k, s, ca, cb, w, q1, q2, h1, h2);
}
