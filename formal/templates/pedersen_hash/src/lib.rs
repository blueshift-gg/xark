use xark::{Field, Private, circuit};

/// `xark_pedersen::pedersen_hash` on two fresh scalars.
#[circuit]
pub fn pedersen_hash(m: Private<[Field; 2]>) {
    xark_pedersen::pedersen_hash(m);
}
