# xark-poseidon2

Poseidon2 hash gadget for xark zero-knowledge circuits.

Part of [xark](https://github.com/blueshift-gg/xark) — write, prove, and verify zero-knowledge circuits in Rust.

## Outside the circuit

`xark_poseidon2::native` runs the same permutation on the host, over
`ark_bn254::Fr`, so a wallet or test can compute the digest a circuit commits to
without a second Poseidon2 implementation:

```rust
use xark_poseidon2::native::{hash, Fr};

let commitment: Fr = hash([Fr::from(7u64), Fr::from(11u64)]);
```

`poseidon2_perm`, `hash2` and `hash` all have native versions. Both sides are
one generic implementation (constants, rounds, S-box and linear layers), and the
tests check them against each other and the reference vectors.
