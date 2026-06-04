use std::hash::blake2s;

fn main(msg: [u8; 3], digest: pub [u8; 32]) {
    let h = blake2s(msg);
    for i in 0..32 {
        assert(h[i] == digest[i]);
    }
}
