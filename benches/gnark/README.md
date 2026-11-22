# xark and gnark, side by side

The same function, four ways:

- **xark + arkworks**: a xark circuit, proved by `ark-groth16`.
- **xark + xark-groth16**: the same circuit, proved by xark's own prover (what
  `xark prove` runs; its keys and proofs are arkworks').
- **xark + gnark**: the same circuit, proved by gnark (`xark prove --backend
  gnark`, see [docs/gnark.md](../../docs/gnark.md)).
- **pure gnark**: the function written against gnark's frontend
  ([`pure/main.go`](pure/main.go)) and proved by gnark.

| function | frontend + backend | R1CS constraints | prove (ms) | prove, 1 thread (ms) |
|---|---|---:|---:|---:|
| sha256 (3-byte message) | xark + arkworks | 16,472 | 63 | 167 |
| | xark + xark-groth16 | 16,472 | 35 | 129 |
| | xark + gnark | 16,472 | 22 | 142 |
| | pure gnark | 156,681 | 239 | 1645 |
| keccak256 (3-byte message) | xark + arkworks | 89,375 | 201 | 681 |
| | xark + xark-groth16 | 89,375 | 69 | 505 |
| | xark + gnark | 89,375 | 65 | 500 |
| | pure gnark | 187,607 | 298 | 2410 |
| sha256 (1024-byte message) | xark + arkworks | 299,978 | 651 | 2561 |
| | xark + xark-groth16 | 299,978 | 206 | 1923 |
| | xark + gnark | 299,978 | 243 | 2055 |
| | pure gnark | 580,217 | 1151 | 9677 |
| keccak256 (1024-byte message) | xark + arkworks | 752,576 | 1425 | 5593 |
| | xark + xark-groth16 | 752,576 | 414 | 4157 |
| | xark + gnark | 752,576 | 450 | 3827 |
| | pure gnark | 583,346 | 1251 | 10754 |
| poseidon2 (1 permutation) | xark + arkworks | 243 | 7.1 | 14 |
| | xark + xark-groth16 | 243 | 5.8 | 15 |
| | xark + gnark | 243 | 1.7 | 14 |
| | pure gnark | 243 | 1.7 | 13 |
| poseidon2 (1000 permutations) | xark + arkworks | 240,003 | 1076 | 5764 |
| | xark + xark-groth16 | 240,003 | 392 | 3969 |
| | xark + gnark | 240,003 | 399 | 4434 |
| | pure gnark | 240,003 | 442 | 4000 |

Apple M4 Max (16 cores), 2026-11-22: gnark 0.14.0, ark-groth16 0.6, Rust 1.99.1,
Go 1.25.5; the median of 5 proofs, made one after another in one process with
the key in memory. The first time is with every core. The second is on one thread
(`RAYON_NUM_THREADS=1`, and `GOMAXPROCS` lowered to 1): the number about the work
rather than the machine. `./run.sh [runs]` prints the table for your machine.

## Reading it

- **Poseidon2 costs the same in both frontends.** Each folds additions and
  multiplications by constants into linear combinations and spends a row only on
  a product of two variables or an assertion: a permutation (t = 3, R_F = 8,
  R_P = 56) has 80 S-boxes of three rows each, plus three rows for the public
  outputs. The xark + gnark count is xark's by construction: the conversion
  carries the rows over one for one.
- **SHA-256 and Keccak-256 differ by a fixed cost.** gnark's `std/hash/sha2` and
  `std/hash/sha3` work on bytes through lookup tables (`uints`): an XOR and an AND
  table of 65,536 entries each, one row per entry, so about 131,000 rows before
  the first byte is hashed (gnark's profiler: 131,328 of SHA-256's 156,681 rows
  and 131,200 of Keccak-256's 187,607). xark's gadgets work on bits in plain
  rows and have no such cost.
- **Past the tables, SHA-256 is still smaller in xark and Keccak-256 is not.**
  The 1024-byte messages show the cost of a block. SHA-256 (17 blocks) is 17,600
  rows a block in xark and 26,400 in gnark: a three-input XOR, a majority or a
  choice is one row a bit in xark and a rotation is free, where a byte lookup
  takes a row a byte for each two-input operation and a rotation by other than
  whole bytes splits every byte. Keccak-256 (8 blocks) is 94,100 rows a block in
  xark and 56,500 in gnark, so there the gnark circuit is the smaller one.
- **gnark's smaller Keccak-256 circuit is not the faster proof**: 1251 ms for
  583,346 rows written in gnark against 450 ms for xark's 752,576 rows on the
  same prover, and 10.8 s against 3.8 s on one thread. The benchmark times a
  proof whole, so it does not say which part of gnark's prover the difference
  is in.
- **On one thread xark-groth16 and gnark are within an eighth of each other** on
  every xark circuit, and neither is first throughout (xark-groth16 on the
  SHA-256 circuits and the Poseidon2 chain, gnark on the long Keccak-256);
  arkworks' prover takes 1.2 to 1.45 times the faster of the two. With every
  core it takes two to three and a half times as long as they do past a few
  thousand rows.
- **A time is the proof alone**, with the key in memory, after the witness is
  solved. gnark's times include its solver, which for a xark circuit
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

- `poseidon2_chain/`, `sha256_1024/`, `keccak256_1024/`: the xark circuits of
  the 1000 permutations and the 1024-byte messages. The three-byte SHA-256 and
  Keccak-256 and the single permutation are `examples/sha256`,
  `examples/keccak256` and `examples/poseidon2`.
- `pure/`: the six circuits in gnark, one Go program, each on gnark's standard
  library (`std/hash/sha2`, `std/hash/sha3`, `std/permutation/poseidon2`). It
  also writes the inputs of the four digest circuits for xark (`pure-gnark
  inputs <circuit>`), so both sides prove the same message and digest. The
  Poseidon2 inputs are files here (`poseidon2.inputs.json`,
  `poseidon2_chain/inputs.json`): the two sides' permutations differ.
- `run.sh`: builds everything, keys each circuit's template-reduced rows over a
  2^k domain for every backend (the form arkworks' prover takes), and measures
  with `bench_prove warm` (arkworks and xark-groth16), `xark-gnark bench` (xark +
  gnark) and `pure/` (pure gnark). slow.yml runs it with one proof a measurement,
  and the three circuits' tests.
