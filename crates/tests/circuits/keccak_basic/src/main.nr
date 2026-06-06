// Keccak-f[1600] permutation. Exercises Noir's `BlackBoxFuncCall::Keccakf1600`
// opcode (ROADMAP step WS-D.1).
//
// Input is a private 25-lane state; output is the same state after one
// invocation of the Keccak-f[1600] permutation. The expected output is
// supplied as a public input and asserted lane-by-lane.
fn main(input: [u64; 25], output: pub [u64; 25]) {
    let res = std::hash::keccakf1600(input);
    for i in 0..25 {
        assert(res[i] == output[i]);
    }
}
