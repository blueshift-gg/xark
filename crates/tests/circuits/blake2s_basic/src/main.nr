// Blake2s digest of a 3-byte message. Exercises Noir's
// `BlackBoxFuncCall::Blake2s` opcode end-to-end (ROADMAP step WS-D.2).
//
// Input `msg` is private; the expected `digest` is public and asserted
// byte-by-byte against the in-circuit hash output.
use std::hash::blake2s;

fn main(msg: [u8; 3], digest: pub [u8; 32]) {
    let h = blake2s(msg);
    for i in 0..32 {
        assert(h[i] == digest[i]);
    }
}
