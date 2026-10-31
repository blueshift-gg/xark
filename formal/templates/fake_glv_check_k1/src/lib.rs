use xark::{Field, Private, circuit};

/// `xark_secp256k1::fake_glv_check_k1` on fresh limbs.
#[circuit]
#[allow(clippy::too_many_arguments)]
pub fn fake_glv_check_k1(
    r: Private<[Field; 4]>,
    s: Private<[Field; 4]>,
    e: Private<[Field; 4]>,
    xr: Private<[Field; 4]>,
    c: Private<[Field; 4]>,
    g: Private<[Field; 4]>,
    q1: Private<[Field; 6]>,
    q2: Private<[Field; 6]>,
    h1: Private<[Field; 8]>,
    h2: Private<[Field; 8]>,
    tu: Private<[Field; 2]>,
) {
    let _ = xark_secp256k1::fake_glv_check_k1(r, s, e, xr, c, g, q1, q2, h1, h2, tu);
}
