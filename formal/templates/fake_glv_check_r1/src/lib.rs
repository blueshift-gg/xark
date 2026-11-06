use xark::{Field, Private, circuit};

/// `xark_secp256r1::fake_glv_check_r1` on fresh limbs.
#[circuit]
#[allow(clippy::too_many_arguments)]
pub fn fake_glv_check_r1(
    r: Private<[Field; 4]>,
    s: Private<[Field; 4]>,
    e: Private<[Field; 4]>,
    xr: Private<[Field; 4]>,
    ab: Private<[Field; 2]>,
    g: Private<[Field; 4]>,
    q1: Private<Field>,
    q2: Private<[Field; 5]>,
    h1: Private<[Field; 3]>,
    h2: Private<[Field; 7]>,
    tu: Private<[Field; 2]>,
) {
    let _ = xark_secp256r1::fake_glv_check_r1(r, s, e, xr, ab, g, q1, q2, h1, h2, tu);
}
