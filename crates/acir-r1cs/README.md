# xark-acir-r1cs

Lowers a compiled Noir program (ACIR, as emitted by `nargo`) into an Arkworks
R1CS constraint system over BN254. This is the front half of the xark backend:
it turns the ACIR opcode stream into constraints and a witness assignment that
`xark-backend` then feeds to Groth16.

It is a library with no Groth16 / proving dependency of its own — just ACIR
parsing and constraint generation — so it can be unit-tested gadget-by-gadget
in isolation.

## What it does

- **Parses** the ACIR artifact and the `nargo`-solved witness map
 (`src/artifact.rs`, `src/witness.rs`).
- **Lowers** every supported opcode to constraints (`src/lower.rs`,
 `src/opcodes/`): arithmetic gates, memory (init/read/write), Brillig
 (unconstrained) blocks, and function calls across a multi-function program.
- **Implements the black-box gadgets** in `src/gadgets/`: range checks,
 bitwise ops, the hashes (SHA-256, Keccak, Blake2s, Blake3, Poseidon),
 AES, ECDSA (secp256k1 / secp256r1), and elliptic-curve ops.
- **Tracks public inputs** (`src/public_inputs.rs`) so the prover and the
 on-chain verifier agree on exactly which witnesses are public and in what
 order.

## Usage

You normally drive this through `xark-backend` / the `xark` CLI rather than
directly. The entry point is the lowering routine in `src/lib.rs`, which takes
the parsed ACIR + witness and returns a constraint system ready for
`ConstraintSynthesizer`.

## Scope

Supports the opcode and black-box-function subset exercised by the circuits in
`crates/tests/circuits/` (pinned to `nargo 1.0.0-beta.21`). Unsupported opcodes fail loudly
(`src/opcodes/unsupported.rs`) rather than silently producing a wrong circuit.
