# xark and gnark, side by side

The same function, four ways:

- **xark + arkworks**: a xark circuit, proved by `ark-groth16`.
- **xark + xark-groth16**: the same circuit, proved by xark's own prover (what
  `xark prove` runs; its keys and proofs are arkworks').
- **xark + gnark**: the same circuit, proved by gnark (`xark prove --backend
  gnark`, see [docs/gnark.md](../../docs/gnark.md)).
- **pure gnark**: the function written against gnark's frontend
  ([`pure/main.go`](pure/main.go)) and proved by gnark.

| function | frontend + backend | R1CS constraints | prove (ms) |
|---|---|---:|---:|
| sha256 (3-byte message) | xark + arkworks | 16,472 | 66 |
| | xark + xark-groth16 | 16,472 | 37 |
| | xark + gnark | 16,472 | 22 |
| | pure gnark | 156,681 | 244 |
| keccak256 (3-byte message) | xark + arkworks | 89,375 | 209 |
| | xark + xark-groth16 | 89,375 | 72 |
| | xark + gnark | 89,375 | 66 |
| | pure gnark | 187,607 | 307 |
| poseidon2 (1 permutation) | xark + arkworks | 243 | 8.0 |
| | xark + xark-groth16 | 243 | 5.9 |
| | xark + gnark | 243 | 1.8 |
| | pure gnark | 243 | 1.7 |
| poseidon2 (1000 permutations) | xark + arkworks | 240,003 | 1106 |
| | xark + xark-groth16 | 240,003 | 397 |
| | xark + gnark | 240,003 | 407 |
| | pure gnark | 240,003 | 460 |

Apple M4 Max (16 cores), 2026-11-22: gnark 0.14.0, ark-groth16 0.6, Rust 1.99.1,
Go 1.25.5; the median of 9 proofs. `./run.sh [runs]` prints the table for your
machine.

## Reading it

- **Poseidon2 costs the same in both frontends.** Each folds additions and
  multiplications by constants into linear combinations and spends a row only on
  a product of two variables or an assertion: a permutation (t = 3, R_F = 8,
  R_P = 56) has 80 S-boxes of three rows each, plus three rows for the public
  outputs. The xark + gnark count is xark's by construction: the conversion
  carries the rows over one for one.
- **SHA-256 does not.** gnark's `std/hash/sha2` works on bytes through lookup
  tables (`uints`), and most of its 156,681 rows are a fixed cost: a second block
  adds 26,500 (183,152 rows for a 67-byte message), which leaves about 130,000
  that do not depend on the message. One block is the worst case for it; over a
  long message that cost amortizes, and each further block still costs more than
  the 16,472 rows of the whole xark circuit.
- **Keccak-256 is closer.** gnark's `std/hash/sha3` is built on the same byte
  tables and takes 187,607 rows for one block against xark-keccak's 89,375, a
  little over twice. How much of gnark's count is fixed was not measured here.
- **A time is the proof alone**, with the key in memory and every core, after the
  witness is solved. gnark's times include its solver, which for a xark circuit
  only checks the rows (xark solved the witness) and for the pure circuit computes
  it. xark's witness solve, not in the table, is 0.11 s for the 1000 permutations.
  gnark's lookup tables also add a commitment to the pure SHA-256 and
  Keccak-256 proofs, which their times include.
- **One Poseidon2 permutation is too small to rank provers by**: at 243
  constraints a proof is a few fixed-cost multi-scalar multiplications and thread
  start-up. The 1000-permutation chain is there to have something to time.
- gnark-crypto derives its own Poseidon2 round constants, so the pure gnark
  circuit computes a different permutation of the same shape as xark-poseidon2's:
  the same rows and the same cost, other outputs.

## What is here

- `poseidon2_chain/`: the xark circuit of the 1000 permutations, with the inputs
  it is proved with (`inputs.json`). SHA-256, Keccak-256 and the single
  permutation are `examples/sha256`, `examples/keccak256` and
  `examples/poseidon2`, with their inputs beside this file.
- `pure/`: the four circuits in gnark, one Go program, each on gnark's standard
  library (`std/hash/sha2`, `std/hash/sha3`, `std/permutation/poseidon2`).
- `run.sh`: builds everything, keys each circuit's template-reduced rows over a
  2^k domain for every backend (the form arkworks' prover takes), and measures
  with `bench_prove warm` (arkworks and xark-groth16), `xark-gnark bench` (xark +
  gnark) and `pure/` (pure gnark).
