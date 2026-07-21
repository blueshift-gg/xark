#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};
use xark_bits::{add32, and32, rotr32, xor32};

/// Exercises the 32-bit word gadget layer:
/// `out == (rotr(a XOR b, 7) + (a AND b)) mod 2^32`.
/// Bitwise ops cost 1 gate/bit; rotations are free re-wiring; `add32` is modular
/// addition via carry decomposition.
#[circuit]
pub fn word_ops(a: Private<Field>, b: Private<Field>, out: Public<Field>) {
    let ba = a.to_bits::<32>();
    let bb = b.to_bits::<32>();
    let mixed = add32(rotr32(xor32(ba, bb), 7), and32(ba, bb));
    require_eq(Field::from_bits::<32>(mixed), out);
}

#[cfg(test)]
mod tests {
    use super::word_ops;

    #[test]
    fn accepts_valid() {
        word_ops("0".into(), "0".into(), "0".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(word_ops("0".into(), "0".into(), "1".into()).is_err());
    }
}
