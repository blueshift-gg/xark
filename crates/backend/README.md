# xark-backend

Host-side Groth16 (BN254) plumbing for xark: key bundles and their files, the
Powers-of-Tau transcript and the trusted-setup ceremony, and the
little-endian Solana wire format that [`xark-verifier`] consumes on chain. The
Groth16 setup, prover and verifier themselves live in `xark-groth16`; arkworks
supplies only the BN254 arithmetic.

## What it does

- **Keys** (`src/keys.rs`): `Groth16Keys`, reading and writing `pk.bin` /
 `vk.bin`, and the key metadata.
- **Ptau ingest** (`src/ptau.rs`): parses a snarkjs-format `powersoftau` file
 (with admissibility checks) as the phase-1 source of randomness, and
 `setup_from_ptau` derives phase-2 keys from it with `xark-groth16`'s setup.
- **Ceremony** (`src/ceremony.rs`): the phase-2 MPC — each contributor applies a
 fresh `δ`, with a Schnorr proof of contribution and δ-consistency pairing
 checks over the chain (`xark ceremony`).
- **Solana encoding** (`src/solana.rs`): the canonical LE encoder for VK /
 proof / public-input bytes (re-exported from `xark_groth16::solana`), and the
 big-endian point encoding the ceremony transcript hashes. No `ic_count` field —
 the IC count is recoverable from length and fixed by `N` on the typed verifier
 side.

## Usage

Driven via the `xark` CLI (`xark-cli`). The library exposes the key and proof
types, the `.ptau`/ceremony support and the serialization helpers; setup,
proving and verification (`xark_groth16::verify`) are in `xark-groth16`.

## Determinism

The `test-deterministic` feature adds `test_rng()`, a fixed-seed RNG, so
fixtures and differential tests reproduce byte-for-byte. **Do not** enable it in
production — a real deployment needs a genuine trusted-setup ceremony (see
`xark ceremony` and `docs/trusted-setup.md`).

[`xark-verifier`]:../verifier
