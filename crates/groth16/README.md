# xark-groth16

xark's **Groth16 (BN254)**: key generation, a **streaming prover**,
verification, and the key/proof types. Keys and proofs are byte-compatible with
`ark-groth16` (for the same randomness `(r, s)` the proof is **byte-identical**,
checked in the tests, where `ark-groth16` is a dev-dependency), but the prover
never materializes the constraint system or the proving key.

| piece | what it does |
|---|---|
| `r1cs` | The ordering contract (`VarLayout`: `1`, publics, then the rest, each in id order — arkworks' `gr1cs` allocation) and chunked row sources: `BytecodeSource` expands rows window-by-window straight from `circuit.xbc`; `ProgramSource` chunks an in-memory `R1csProgram`. |
| `msm` | Our Pippenger (magnitude-classed scalars, full-width ones split with the GLV endomorphism (`glv`), cost-model window widths, signed Booth digits, parallel over windows × slices, **batch-affine bucket accumulation** with XYZZ side buckets for conflicts), a naive double-and-add oracle, and `StreamingMsm`. |
| `decode` | Compressed point decoding, the same points as arkworks' (tested bit-for-bit) with cheaper square roots: a windowed exponentiation, and one exponentiation instead of a Legendre symbol, root and inversion inside the `Fq2` root. 1.24× (G1) and 1.74× (G2) faster per point; with a compressed key this is most of a proof's work. |
| `pk` | Chunked proving-key readers: `SerializedPk` (a `pk.bin` file, or bytes, decoded one chunk at a time) and `InMemoryPk`. |
| `fft` | Blocked four-step FFT with tiled column gathers and a tiled transpose. Transforms alternate natural ↔ "T-layout", so the quotient step needs no standalone transpose: the only one is fused into the final `h → integer` conversion. Domains of `2^k`, `3·2^k` and `9·2^k` points (radix-3 layers in the column FFTs). |
| `qap` | `h = (A·B − C)/Z`, bit-identical to `LibsnarkReduction::witness_map`, in six transforms: `h = (coset_iFFT(A·B) − iFFT(C)) / Z(g)`. Rows are streamed twice (A, B, then C), so the peak is two domain vectors; up to 2^20 points, once, with `C = A∘B` as a third. |
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
mismatch is rejected up front (`ProveError::KeyMismatch`). With
`ProverConfig::self_check` (off by default; `xark prove --verify`) the proof is
verified before it is returned, and one that fails says why:
`ProveError::Unsatisfied { row }` when the witness breaks a row,
`SelfCheckFailed` when every row holds (the key is for another circuit).

Every prover can stand in for another through `Prover` (`provers.rs`): it
holds its key and proves with the caller's `(r, s)`, so two provers give the
same proof bytes. `Cpu` is this crate's prover; the tests and `bench_prove warm`
run arkworks through the same interface (`tests/support/arkworks_prover.rs`).

`Accelerated<D, P>` is the prover with a device beside the CPU: the device
takes the quotient and the H MSM while the CPU takes A, B and L, and declines a
domain too small to repay its fixed cost (`Accelerator::wants_proof`). The
OpenCL device is `xark-groth16-opencl` (kept out of the workspace, since it
links the system's OpenCL library); `xark prove --prover opencl`, in an `xark`
built with `--features opencl`, proves through it. On an Apple M3 Max, `xark
prove` of Ed25519 (397k constraints) takes 243 ms instead of 364 and secp256r1
ECDSA 260 instead of 351, the device's set-up included (about 80 ms, beside the
witness solve); circuits under a 2^18-point domain stay on the CPU.

## GPU MSM security boundary

GPU MSM execution is not verified constant-time. The OpenCL kernels branch on
scalar bits and on intermediate curve values, so their execution time can depend
on the prover's scalars. GPU execution also relies on the device runtime and
driver, which this crate does not audit. Scalar staging and intermediate device
buffers are released without a guaranteed secure wipe. `xark prove --prover
opencl` therefore requires `--acknowledge-gpu-side-channel-risk`. That flag
records acceptance of this risk; it does not make the backend constant-time.

Do not prove on a GPU on shared or untrusted devices, or when the threat model
requires witness secrecy from the device runtime. The CPU prover has not been
certified constant-time either.

Other entry points:

* `PushProver` — feed the serialized key **as it arrives** (any chunking, e.g. a
  network stream); the key is consumed in file order and never held.
* `transcode::KeyTranscoder` / `SerializedPk::tee_uncompressed` — re-encode a
  compressed key with uncompressed points (from a stream, or as a by-product of a
  proof), so later proofs skip per-point decompression (`xark prove --cache`
  writes `pk.decoded.bin`; Ed25519 2.1× faster natively, 3.5× in WASM).
* `InMemoryPk` — prove against an already-decoded key (no per-proof point
  decompression: Ed25519 3.7 s vs arkworks' 6.2 s with the key resident). Its
  MSMs run side by side with the quotient, and a small circuit's proof
  (`ProverConfig::merge_below`) takes three MSMs instead of five.
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
setup` uses them.

**Smooth domains** (`DomainKind::Smooth`; `xark setup`'s default for a key made without a `.ptau`,
`--domain radix2` opts out). BN254's
scalar field also has a subgroup of order 9, so the QAP domain can be the smallest
of `2^k`, `3·2^k`, `9·2^k` points instead of the next power of two. The 16,472
rows of `examples/sha256` fit `9·2^11 = 18,432` (radix-2: 32,768), so the `H`
vector, its MSM and every quotient FFT shrink by 44%.
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
* **Setup**: keys made without a `.ptau` byte-identical to `circuit_specific_setup` (bytecode and
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
