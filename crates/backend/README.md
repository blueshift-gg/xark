# xark-backend

The Groth16 (BN254) proving backend for xark. Given a circuit lowered to R1CS
it runs the full Arkworks Groth16 pipeline — trusted
setup, prove, verify — and serializes keys, proofs, and public inputs into the
little-endian Solana wire format that [`xark-verifier`] consumes on chain.

This is the host-side workhorse behind the `xark` CLI. It pulls in Arkworks
(`ark-groth16`, `ark-bn254`, …) with the `parallel` feature, so proving and
setup scale across cores.

## What it does

- **Setup** (`src/setup.rs`, `src/setup_phase2.rs`): Groth16 trusted setup,
 including the phase-2 MPC contribution flow used by `xark ceremony`.
- **Ptau ingest** (`src/ptau.rs`): consumes a snarkjs `powersoftau` file as the
 phase-1 source of randomness for a real ceremony.
- **Prove** (`src/prove.rs`): produces a proof **and self-verifies it** against
 the proving key's embedded VK before returning — Arkworks' `prove` does not
 check that the witness satisfied the R1CS, so this fail-fast guard turns a
 lowering/witness bug into an immediate `Unsatisfiable` instead of a silently
 broken proof shipped downstream.
- **Verify** (`src/verify.rs`): the host-side verifier (mirrors the on-chain
 one; used in tests and the `xark verify` command).
- **Solana encoding** (`src/solana.rs`): the canonical LE encoder for VK /
 proof / public-input bytes. No `ic_count` field — the IC count is recoverable
 from length and fixed by `N` on the typed verifier side.

## Usage

Driven via the `xark` CLI (`xark-cli`). The library API in `src/lib.rs` exposes
`setup`, `prove`, `verify`, and the serialization helpers if you want to embed
the backend directly.

## Determinism

The `test-deterministic` feature seeds proving/setup RNG from a fixed value so
fixtures and differential tests reproduce byte-for-byte. **Do not** enable it in
production — a real deployment needs a genuine trusted-setup ceremony (see
`xark ceremony` and `docs/trusted-setup.md`).

[`xark-verifier`]:../verifier
