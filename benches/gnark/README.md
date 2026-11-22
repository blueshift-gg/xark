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
| fibonacci (1000 steps) | xark + arkworks | 1 | 1.5 |
| | xark + xark-groth16 | 1 | 3.2 |
| | xark + gnark | 1 | 0.5 |
| | pure gnark | 1 | 0.6 |
| poseidon2 (1 permutation) | xark + arkworks | 243 | 7.4 |
| | xark + xark-groth16 | 243 | 5.7 |
| | xark + gnark | 243 | 1.8 |
| | pure gnark | 243 | 1.7 |
| poseidon2 (1000 permutations) | xark + arkworks | 240,003 | 1084 |
| | xark + xark-groth16 | 240,003 | 392 |
| | xark + gnark | 240,003 | 401 |
| | pure gnark | 240,003 | 449 |

Apple M4 Max (16 cores), 2026-11-22: gnark 0.14.0, ark-groth16 0.6, Rust 1.99.1,
Go 1.25.5; the median of 9 proofs. `./run.sh [runs]` prints the table for your
machine.

## Reading it

- **The constraint counts are equal.** Both frontends fold additions and
  multiplications by constants into linear combinations and spend a row only on a
  product of two variables or an assertion. Fibonacci's recurrence is linear, so
  the whole circuit is its closing equality. A Poseidon2 permutation (t = 3,
  R_F = 8, R_P = 56) has 80 S-boxes of three rows each, plus three rows for the
  public outputs. The xark + gnark count is xark's by construction: the conversion
  carries the rows over one for one.
- **A time is the proof alone**, with the key in memory and every core, after the
  witness is solved. gnark's times include its solver, which for a xark circuit
  only checks the rows (xark solved the witness) and for the pure circuit computes
  it. xark's witness solve, not in the table, is 0.11 s for the 1000 permutations.
- **The first two functions are too small to rank provers by**: at 1 and 243
  constraints a proof is a few fixed-cost multi-scalar multiplications and
  thread start-up. The 1000-permutation chain is there to have something to time.
- gnark-crypto derives its own Poseidon2 round constants, so the pure gnark
  circuit computes a different permutation of the same shape as xark-poseidon2's:
  the same rows and the same cost, other outputs.

## What is here

- `fibonacci/`, `poseidon2_chain/`: the xark circuits, with the inputs they are
  proved with (`inputs.json`). The single permutation is `examples/poseidon2`.
- `pure/`: the three circuits in gnark, one Go program.
- `run.sh`: builds everything, keys each circuit's template-reduced rows over a
  2^k domain for every backend (the form arkworks' prover takes), and measures
  with `bench_prove warm` (arkworks and xark-groth16), `xark-gnark bench` (xark +
  gnark) and `pure/` (pure gnark).
