# xark-verifier

Solana on-chain Groth16 (BN254) verifier. Consumes the little-endian wire
format produced by `xark export` and runs the Groth16 pairing check via the
`alt_bn128` syscalls. Curve arithmetic is delegated to
[`solana-nostd-alt-bn128`]; off-chain it falls through to Arkworks, so the same
code runs in host tests and on chain.

The crate is `#![no_std]` on the Solana target (linking only `core`), so the
whole verifier can be pulled into the `#![no_std]` cdylibs `svm-unit-test`
generates — see the on-chain `sbpf` test in the `xark-tests` crate.

## Usage

```rust
use xark_verifier::{Verifier, Proof};
// Typed, compile-time VK (recommended — the VK is baked in, can't be swapped):
const VERIFIER: Verifier<1> = Verifier::from_le_bytes(include_bytes!("vk.solana.bin"));
const PROOF: Proof = Proof::from_le_bytes(include_bytes!("proof.solana.bin"));
assert!(VERIFIER.verify(&PROOF, &public_inputs)); // public_inputs: &[[u8;32]; 1]
```

In practice you don't write this by hand: `xark export` emits a small,
self-contained crate that bakes in your circuit's VK and exposes `verify(...)`
/ `verify_instruction_data(...)`. Your Solana program depends on that crate;
re-export when the circuit changes and the generated crate is the only thing
that updates. Or call `verify_groth16(vk_bytes, proof_bytes, public_inputs)`
directly when the VK is loaded dynamically — in that case the program **must**
authenticate the VK (e.g. pin its hash).

## Wire format (little-endian, `x || y`)

```
vk_bytes : alpha (G1, 64) | beta (G2, 128) | gamma (G2, 128) | delta (G2, 128)
 | (N+1) * G1 (64 each) // IC; count = N+1, implied by length
proof_bytes : A (G1, 64) | B (G2, 128) | C (G1, 64) (256 B)
public_inputs: N * Fr (32 B LE each, each < r — non-canonical inputs are rejected)
```

Every `Fq`/`Fr` element is a 32-byte little-endian limb fed straight to the
syscalls. `proof.A` is pre-negated by the exporter. There is no `ic_count`
field — it is recoverable from the byte length (and fixed by `N` in the typed
API). See `src/verifier.rs` for the pairing equation and `crates/backend/src/solana.rs`
for the canonical encoder.

## Security-relevant properties (tested)

- Off-curve / non-subgroup proof points are rejected by the syscalls.
- Non-canonical public inputs (`>= r`) are rejected (prevents encoding malleability).
- Every public input is cryptographically bound (`binding` test).
- `verify_groth16` never panics and never accepts adversarial bytes (`fuzz` test).
- The entrypoint is fail-closed (anything not `Ok(true)` → reject).

## Testing

The whole workspace's tests (host, fuzz, binding, and the on-chain Mollusk
suite) live in the `xark-tests` crate:

```
cargo test -p xark-tests # host (Arkworks path) + fuzz + binding
cargo test -p xark-tests --test sbpf # on-chain in Mollusk (needs cargo-build-sbf)
```

[`solana-nostd-alt-bn128`]: https://crates.io/crates/solana-nostd-alt-bn128
