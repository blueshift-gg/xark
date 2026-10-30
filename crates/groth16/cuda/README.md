# BN254 MSM CUDA work

Xark already has a BN254 Groth16 prover and a CPU Pippenger MSM in `../src/`. The
prover's `Accelerator::msm` hook receives serialized proving-key chunks and the
matching scalars. This directory starts an original CUDA path against that seam.

## First kernel

`msm_digits_test.cu` extracts fixed-width windows from four little-endian 64-bit
scalar limbs. With an 11-bit window, each scalar has 24 digits, where

```text
s = Σ[j=0..23] digit[j] · 2^(11j)
digit[j] = (s >> 11j) mod 2^11
```

The output is window-major (`digits[window * scalar_count + scalar]`) so adjacent
threads write adjacent entries. Inputs use a structure-of-arrays limb layout for
the same reason. The test compares every device result with a separate CPU
bit-extraction routine over boundary patterns and 1,024 deterministic 256-bit
inputs. The upper eight bits in the final window are zero because the source has
four limbs. The randomized inputs exercise raw extraction, not field canonicality;
the Rust adapter must pass canonical BN254 `Fr` values.

Run on a host with the NVIDIA CUDA Toolkit and a visible CUDA device:

```sh
make -C crates/groth16/cuda test
```

The same digit routine can be checked against the independent bit-by-bit
reference on a host without CUDA:

```sh
make -C crates/groth16/cuda test-host
```

This host check covers the shared extraction function only. It does not compile
or run the CUDA kernel.

The `.cu` kernel in this directory still tests scalar decomposition only. It does
not perform bucket accumulation and is not connected to `Accelerator::msm`. The
separate native adapter in `../../groth16-cuda` calls ICICLE's BN254 G1 MSM through
the existing hook. It is opt-in and falls back to CPU when CUDA is unavailable or
the adapter declines a chunk. The adapter has not yet been compiled or run on an
NVIDIA host, so there is no GPU correctness or performance claim yet.

## Proof and implementation boundary

For a chunk of points and scalars, the MSM is `Σ sᵢPᵢ`. Window decomposition
rewrites it as a sum of bucket contributions, with each window weighted by
`2^(11j)`. The next step is to accumulate points by digit and reduce the buckets
on device. The host adapter must convert Xark's canonical point/scalar encodings
to the device representation, check all lengths before launch, synchronize before
reading results, and serialize the returned group element in the format expected
by `sum_g1` / `sum_g2`.

The adapter starts with G1 MSM on the prover's existing streamed chunks. Its
tests compare GPU output with Xark CPU MSM for zero and maximum canonical
scalars, infinity, cancelling points, and seeded full-width values. A proof test
compares fixed-randomness CPU and GPU proofs and verifies the result. These are
implemented checks; they still need to run on a CUDA host. GPU performance
measurements must separate input size, host-to-device transfer, kernel,
device-to-host transfer, and total chunk time.

## References

- Groth16's original proof system: [On the Size of Pairing-based Non-interactive
  Arguments](https://eprint.iacr.org/2016/260).
- GPU MSM and proof-generation design reference: [cuZK: Accelerating
  Zero-Knowledge Proof with a Faster Parallel Multi-Scalar Multiplication
  Algorithm on GPUs](https://eprint.iacr.org/2022/1321). This implementation is
  written from the mathematical description; it does not copy cuZK source.
- CUDA thread layout, asynchronous execution, and memory transfer guidance:
  [CUDA C++ Programming Guide](https://docs.nvidia.com/cuda/cuda-c-programming-guide/)
  and [CUDA C++ Best Practices Guide](https://docs.nvidia.com/cuda/cuda-c-best-practices-guide/).
- Rust's safety boundary for a later native adapter:
  [The Rustonomicon, Foreign Function Interface](https://doc.rust-lang.org/nomicon/ffi.html).
