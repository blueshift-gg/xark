use std::hash::poseidon2_permutation;

// One Poseidon2 permutation over BN254 Fr. State width is fixed at 4 by
// Noir's `POSEIDON2_CONFIG_STATE_SIZE` (see noir_stdlib/src/hash/mod.nr in
// v1.0.0-beta.21). Exercises `BlackBoxFuncCall::Poseidon2Permutation`.
fn main(input: [Field; 4], out: pub [Field; 4]) {
    let result = poseidon2_permutation(input);
    for i in 0..4 {
        assert(result[i] == out[i]);
    }
}
