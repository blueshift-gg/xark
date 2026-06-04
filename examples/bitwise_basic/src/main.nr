// Bitwise AND + XOR over `u32`. Exercises Noir's `BlackBoxFuncCall::AND`
// and `BlackBoxFuncCall::XOR` opcodes (ROADMAP step WS-B.1).
fn main(a: u32, b: u32, and_out: pub u32, xor_out: pub u32) {
    assert(a & b == and_out);
    assert(a ^ b == xor_out);
}
