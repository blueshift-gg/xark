use std::hash::sha256_compression;

// Run one SHA-256 compression on a single padded block.
//
// `state_out` is the 8-word post-compression state. With `state` set to the
// SHA-256 IV and `block` set to the padded "abc" message block, this should
// equal SHA-256("abc").
fn main(
    block: [u32; 16],
    state: [u32; 8],
    state_out: pub [u32; 8],
) {
    let next = sha256_compression(block, state);
    for i in 0..8 {
        assert(next[i] == state_out[i]);
    }
}
