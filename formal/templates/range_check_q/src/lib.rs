use xark::{Field, Private, circuit};

#[circuit]
pub fn range_check_q(q: Private<[Field; 25]>) {
    xark_rsa::range_check_q(q);
}
