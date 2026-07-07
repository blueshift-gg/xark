#![no_std]

use xark::{assert_eq, Field, Private, Public};
use xark_bits::{add32, and32, rotr32, xor32};

/// Exercises the 32-bit word gadget layer:
/// `out == (rotr(a XOR b, 7) + (a AND b)) mod 2^32`.
///
/// Bitwise ops cost 1 gate/bit; rotations are free re-wiring; `add32` is modular
/// addition via carry decomposition.
pub fn circuit(a: Private<Field>, b: Private<Field>, out: Public<Field>) {
    let ba = a.to_bits::<32>();
    let bb = b.to_bits::<32>();
    let mixed = add32(rotr32(xor32(ba, bb), 7), and32(ba, bb));
    assert_eq(Field::from_bits::<32>(mixed), out);
}
