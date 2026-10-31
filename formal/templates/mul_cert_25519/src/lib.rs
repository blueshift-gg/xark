use xark::{Field, Private, circuit};

/// `xark_ed25519::mul_cert_25519` on fresh limbs.
#[circuit]
#[allow(clippy::too_many_arguments)]
pub fn mul_cert_25519(
    a1: Private<[Field; 8]>,
    b1: Private<[Field; 8]>,
    a2: Private<[Field; 8]>,
    b2: Private<[Field; 8]>,
    a3: Private<[Field; 8]>,
    b3: Private<[Field; 8]>,
    t: Private<[Field; 8]>,
) {
    xark_ed25519::mul_cert_25519(a1, b1, a2, b2, a3, b3, t);
}
