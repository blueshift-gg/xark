# xark-groth16

xark's **Groth16 (BN254)**: key generation, a **streaming prover**,
verification, and the key/proof types. Keys and proofs are byte-compatible with
`ark-groth16` (for the same randomness `(r, s)` the proof is **byte-identical**,
checked in the tests, where `ark-groth16` is a dev-dependency), but the prover
never materializes the constraint system or the proving key.

| piece | what it does |
|---|---|
| `r1cs` | The ordering contract (`VarLayout`: `1`, publics, then the rest, each in id order — arkworks' `gr1cs` allocation) and chunked row sources: `BytecodeSource` expands rows window-by-window straight from `circuit.xbc`; `ProgramSource` chunks an in-memory `R1csProgram`. |
| `msm` | Our Pippenger (magnitude-classed scalars, cost-model window widths, signed Booth digits, parallel over windows × slices, **batch-affine bucket accumulation** with XYZZ side buckets for conflicts), a naive double-and-add oracle, and `StreamingMsm`. |
| `decode` | Compressed point decoding, the same points as arkworks' (tested bit-for-bit) with cheaper square roots: a windowed exponentiation, and one exponentiation instead of a Legendre symbol, root and inversion inside the `Fq2` root. 1.24× (G1) and 1.74× (G2) faster per point; with a compressed key this is most of a proof's work. |
| `pk` | Chunked proving-key readers: `SerializedPk` (a `pk.bin` file, or bytes, decoded one chunk at a time) and `InMemoryPk`. |
| `fft` | Blocked four-step FFT with tiled column gathers and a tiled transpose. Transforms alternate natural ↔ "T-layout", so the quotient step needs no standalone transpose: the only one is fused into the final `h → integer` conversion. Domains of `2^k`, `3·2^k` and `9·2^k` points (radix-3 layers in the column FFTs). |
| `qap` | `h = (A·B − C)/Z`, bit-identical to `LibsnarkReduction::witness_map`; rows are streamed twice (A, B, then C), so the peak is two domain vectors. |
| `accel` | Hooks + pure kernels to offload FFT sweeps and MSM chunks (used by xark-wasm's Web-Worker pool). |

```rust
let src = xark_groth16::BytecodeSource::new(&xbc)?;          // ~bytecode-sized
let z = src.layout().assignment_from_map(&witness);           // z[0] = 1
let mut pk = xark_groth16::SerializedPk::open(path)?;         // header only
let proof = xark_groth16::prove(&src, &z, &mut pk, &mut rng, &Default::default())?;
```

Row sources match the key's R1CS form (`metadata.json` `r1cs_form`, chosen by
`xark setup --r1cs-form auto|reduced|minimized`): `BytecodeSource` streams the
**template-reduced** circuit straight from `circuit.xbc`; `RowFileSource` streams
the **boundary-minimized** circuit from the compact `r1cs.stream` setup writes next
to a `minimized` key. `xark prove` picks the right one automatically. A key/circuit
mismatch is rejected up front (`ProveError::KeyMismatch`), and every proof is
self-verified before it is returned. A proof that fails that check says why:
`ProveError::Unsatisfied { row }` when the witness breaks a row,
`SelfCheckFailed` when every row holds (the key is for another circuit).

Other entry points:

* `PushProver` — feed the serialized key **as it arrives** (any chunking, e.g. a
  network stream); the key is consumed in file order and never held.
* `transcode::KeyTranscoder` / `SerializedPk::tee_uncompressed` — re-encode a
  compressed key with uncompressed points (from a stream, or as a by-product of a
  proof), so later proofs skip per-point decompression (`xark prove --cache`
  writes `pk.decoded.bin`; Ed25519 2.1× faster natively, 3.5× in WASM).
* `InMemoryPk` — prove against an already-decoded key (no per-proof point
  decompression: Ed25519 3.7 s vs arkworks' 6.2 s with the key resident).
* `ProverConfig::spill_dir` — low-memory mode: one domain-sized vector resident
  during the quotient step, the other parked in a temp file.

**Rows are evaluated, not expanded.** `BytecodeSource` compiles each template
once (field coefficients, resolved variable references) and evaluates calls
numerically against the witness — 7–12× faster than rebuilding rows symbolically,
bit-identical results.

**Setup streams too** (`setup` module): `dev_setup` (trusted dealer) and
`phase2_setup` (from a Powers-of-Tau transcript) take any row source and write
`pk.bin` vector by vector. Each variable's QAP evaluations come from one
*transposed* pass over the compiled templates (row weights pushed back onto
variables, through plug expressions once per call); phase 2 builds a compact
column index from streamed rows instead of synthesizing the constraint system.
Both are byte-identical to the previous setup for the same randomness. `xark
setup` uses them (Ed25519 dev setup: 0.65 GB / 10 s, was 6.35 GB / 17.5 s).

**Smooth domains** (`DomainKind::Smooth`; `xark setup`'s default for dev keys,
`--domain radix2` opts out). BN254's
scalar field also has a subgroup of order 9, so the QAP domain can be the smallest
of `2^k`, `3·2^k`, `9·2^k` points instead of the next power of two. Ed25519's
2,358,839 rows fit `9·2^18 = 2,359,296` (radix-2: 4,194,304), so the `H` vector,
its MSM and every quotient FFT shrink by 44%: `H` MSM 3.0 s → 1.7 s, quotient
0.59 s → 0.36 s, dev setup 10 s → 6.7 s, key 509 → 451 MB (native, 16 threads).
The verifier and verifying key are unaffected. The key's header (`KeyFormat` v2)
states the domain size, so a push-streamed proof computes `h` from the first bytes
of the key; `H`'s length implies it too, which every reader cross-checks. Only this prover (`xark prove`, xark-wasm)
and arkworks with a mixed-radix QAP reduction can prove against such a key —
snarkjs and rapidsnark cannot — and a Powers-of-Tau transcript only supplies
radix-2 Lagrange bases, so ptau setups stay radix-2.

## Validation

`cargo test -p xark-groth16 --release`:

* **MSM** vs arkworks *and* the naive oracle (normalized comparison), random sizes,
  witness-like scalar mixes, random chunk seams; seeded edge cases (∞, zero, `r`,
  `r−1`, `2²⁵⁶−1`, repeated / cancelling bases, empty, length mismatch).
* **FFT** bit-identical to ark-poly for every size 2⁰…2¹⁴, tile 1…64, both
  layouts, and the coset pipeline; tiled transpose for odd shapes. Smooth sizes
  (`3·2^k`, `9·2^k`, plain and blocked) bit-identical to ark-poly's
  `MixedRadixEvaluationDomain`.
* **Ordering contract**: streamed assignment and every streamed row equal
  arkworks' allocation and matrices; relabelling two variables (rows still
  satisfied) makes the proof fail — the contract has teeth.
* **Setup**: dev keys byte-identical to `circuit_specific_setup` (bytecode and
  program sources, both encodings); phase-2 keys byte-identical to
  `xark_backend::ptau::setup_from_ptau`.
* **Whole proof**: byte-identical to `Groth16::prove` (in-memory and serialized
  keys: compressed, uncompressed, legacy), from bytecode and from `r1cs.stream`,
  pushed in any chunking (down to 1 byte), through the spill path, and through a
  step-for-step emulation of the worker decomposition.
* **Smooth domains**: keys, `h` and proofs byte-identical to arkworks'
  `Groth16<Bn254, MixedReduction>` (libsnark's reduction over a mixed-radix
  domain) for `3·2^k`, `9·2^k` and `2^k` circuits — pulled, pushed with the right
  domain hint and with none (`h` recomputed when the key's `H` length arrives),
  and through the worker decomposition.

## Benchmarks

`examples/bench_prove.rs` (end-to-end, per-phase peak heap) and
`examples/bench_kernels.rs` (FFT tile sweep, transpose, MSM vs arkworks),
`examples/bench_setup.rs` (previous vs streaming setup, dev and phase 2).
