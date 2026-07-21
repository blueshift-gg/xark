//! `Field::to_bits` / `from_bits`: bit decomposition as a first-class `Field`
//! operation. `to_bits::<N>()` pins each bit boolean and proves `self < 2^N`;
//! `from_bits` recomposes.
#![cfg_attr(xark, no_std)]
use xark::{circuit, require_eq, Field, Private, Public};

#[circuit]
pub fn to_bits(x: Private<Field>, out: Public<Field>) {
    let bits = x.to_bits::<8>(); // proves x < 256
    require_eq(Field::from_bits::<8>(bits), out);
}

#[cfg(test)]
mod tests {
    use super::to_bits;

    #[test]
    fn accepts_valid() {
        to_bits("200".into(), "200".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(to_bits("200".into(), "201".into()).is_err());
    }
}
