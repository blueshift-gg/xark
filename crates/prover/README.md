# xark-prover

xark's Groth16 (BN254) prover: witness solving, trusted setup, prove, and verify.
Circuit crates use it through `xark::prover` (re-exported in host builds), so
they need no direct dependency on it.

Part of [xark](https://github.com/blueshift-gg/xark) — write, prove, and verify zero-knowledge circuits in Rust.
