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

## Batches

`verify_groth16_batch(vk_bytes, batch, scratch)` checks several proofs of one
circuit (one VK) with a single pairing call: `M + 3` pairs instead of `4M`.
`batch` is the proofs' instruction data back to back (`proof || public_inputs`
each), and `scratch` holds the `M + 3` pairing operands (192 bytes each). For a small batch it fits on the stack (a Solana stack frame
is 4 KB, so up to about 16 proofs); otherwise use the heap or account data:

```rust
let mut scratch = [[0u8; PAIRING_PAIR_BYTES]; 4 + 3];
let ok = verify_groth16_batch(VK_BYTES, instruction_data, &mut scratch)?;
```

Measured on chain (Mollusk), proofs with one public input:

| proofs | batched | one at a time |
|---|---|---|
| 1 | 77,560 CU | 77,043 CU |
| 4 | 168,199 CU | 309,633 CU |
| 16 | 513,223 CU | ~1,240,000 CU |

Each extra proof costs about 29k CU instead of 77k, so the 1.4M CU compute
limit allows about 46 proofs instead of 18. How many fit in the transaction
itself depends on the transaction format (each one-input entry is 288 bytes);
past that, pass the batch in account data. A `false` result says some proof in the
batch is invalid, not which one: verify them one by one to find it.

Each proof's check is weighted by a 252-bit number taken from a SHA-256 of the
VK and the whole batch, so invalid proofs can't be built to cancel each other
out: a batch with an invalid proof passes with probability about 2⁻²⁵² for
each batch an attacker tries (the weights are public, so the margin has to
cover grinding; full-width weights cost the same as narrow ones). The batch is
always strict: non-canonical coordinates are rejected.

### Using batches safely

- **Reject duplicates inside the batch.** Anyone can copy or re-randomize a
  valid proof, so one batch can hold the same statement twice. Check each
  entry's nullifier (or nonce) against the others in the batch as well as
  against storage, before recording any of them. Checking every entry against
  storage first and writing afterwards lets the same nullifier through twice.
- **Act only on the bytes you verified.** The result covers exactly the
  `batch` buffer passed in: read each entry's public inputs (amounts,
  recipients, …) from that same buffer, not from another account or offset.
- **One bad proof fails the batch.** If you batch other people's proofs (a
  relayer), verify each one off-chain first, or a single invalid proof keeps
  everyone else's from landing.
- **Don't alias `scratch` and `batch`.** Safe Rust can't, but a program that
  builds both from raw account memory with `unsafe` must keep them apart: the
  pairing operands are written while entries are still being read.
- As with single proofs, anything but `Ok(true)` is a rejection.

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
- The `*_strict` entry points also reject non-canonical proof/VK coordinates.
  Neither makes a proof unique: Groth16 proofs are re-randomizable, so anyone
  holding a valid proof can make a different valid proof of the same public
  inputs. Never use proof bytes as a replay or dedup key; bind a nullifier,
  nonce or signer into the public inputs instead.
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
