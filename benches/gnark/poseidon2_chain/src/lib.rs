//! The benchmark's larger Poseidon2 workload: a thousand permutations (BN254,
//! t = 3, R_F = 8, R_P = 56, as `examples/poseidon2` has one) applied in a row to
//! a private state, the last state public. One permutation proves in a few
//! milliseconds, most of it fixed cost; this one is large enough to time.
use xark_poseidon2::prelude::*;

/// The number of permutations; `pure/main.go` takes the same.
const PERMUTATIONS: usize = 1000;

#[circuit]
pub fn poseidon2_chain(
    in0: Private<Field>,
    in1: Private<Field>,
    in2: Private<Field>,
    out0: Public<Field>,
    out1: Public<Field>,
    out2: Public<Field>,
) {
    let mut state = [in0, in1, in2];
    for _ in 0..PERMUTATIONS {
        state = poseidon2_perm(state);
    }
    require_eq(state[0], out0);
    require_eq(state[1], out1);
    require_eq(state[2], out2);
}

#[cfg(test)]
mod tests {
    use super::poseidon2_chain;

    /// `inputs.json`: `xark_poseidon2::native::poseidon2_perm` applied a thousand
    /// times to `[1, 2, 3]`.
    const OUT: [&str; 3] = [
        "14416705696433053464219811056942153684863736366292246734334405709709983697277",
        "2270894603678904117439101887945138592429929676231810757711615110598216146128",
        "19519760076396696738963030487593173652559655403542015695463327545820205794887",
    ];

    #[test]
    fn accepts_valid() {
        poseidon2_chain(1, 2, 3, OUT[0], OUT[1], OUT[2]).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(poseidon2_chain(1, 2, 4, OUT[0], OUT[1], OUT[2]).is_err());
    }
}
