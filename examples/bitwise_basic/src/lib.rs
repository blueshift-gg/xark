#![no_std]

use xark_bits::{and32, xor32};
use xark::{assert_eq, Field, Private, Public};

// bitwise_basic: a,b: u32; assert(a & b == and_out); assert(a ^ b == xor_out).
// Each u32 is carried as a Field, decomposed to 32 bits (which range-checks it),
// combined bitwise, and recomposed to compare against the public outputs.
pub fn circuit(
    a: Private<Field>,
    b: Private<Field>,
    and_out: Public<Field>,
    xor_out: Public<Field>,
) {
    let ab = a.to_bits::<32>();
    let bb = b.to_bits::<32>();
    assert_eq(Field::from_bits::<32>(and32(ab, bb)), and_out);
    assert_eq(Field::from_bits::<32>(xor32(ab, bb)), xor_out);
}
