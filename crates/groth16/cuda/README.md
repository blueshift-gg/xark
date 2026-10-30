# BN254 MSM CUDA work

This directory contains CUDA scalar-window extraction, bucket-index, G1 bucket
accumulation/reduction, and tiny end-to-end MSM tests. The custom kernels are
not connected to the prover. The optional
adapter in `../../groth16-cuda` connects Xark's `Accelerator::msm` hook to
ICICLE's BN254 G1 MSM; ICICLE performs the curve arithmetic and bucket
accumulation. Unsupported operations and unavailable CUDA backends fall back to
Xark's CPU implementation.

## Scalar-window kernel

`msm_digits_test.cu` extracts fixed-width windows from four little-endian
64-bit scalar limbs. With an 11-bit window, each scalar has 24 digits:

```text
s = Σ[j=0..23] digit[j] · 2^(11j)
digit[j] = (s >> 11j) mod 2^11
```

The kernel stores digits window-major as `digits[window * scalar_count +
scalar]`. Adjacent threads therefore write adjacent values. The limb input is
structure-of-arrays for the same reason. The final window starts at bit 253 and
contains the remaining three bits of a 256-bit input.

The test compares device output with a separate CPU bit-extraction routine for
boundary patterns and 1,024 deterministic 256-bit inputs. Those inputs test bit
extraction, not BN254 field canonicality. The Rust adapter separately checks
that scalar inputs are canonical `Fr` values before calling ICICLE.

On a host with the NVIDIA CUDA Toolkit and a visible CUDA device, run:

```sh
make -C crates/groth16/cuda test
```

The shared extraction routine can also be checked without CUDA:

```sh
make -C crates/groth16/cuda test-host
```

This host target checks digit extraction and the independent CSR reference,
including repeated bucket members, zero digits, maximum bucket IDs, and rejected
out-of-range digits. It also runs BN254 Fq and G1 arithmetic against Python
integer/affine references. It does not compile or execute a `.cu` kernel.

## Bucket-index stage

`msm_bucketize_test.cu` builds a CSR-style index list for each nonzero digit in
each scalar window. A count pass tallies `(window, digit)` pairs, a prefix pass
creates bucket offsets, and a scatter pass writes scalar indices. Zero digits
are omitted. The CUDA test checks offsets and compares every bucket's member
indices with a host-built reference over repeated-digit, zero-digit, and maximum
bucket inputs. The lists can feed a point-accumulation stage. This kernel still
does not add or reduce curve points. `msm_accumulate_test.cu` separately consumes
a small prepared CSR fixture, adds each bucket's points, and applies descending
weighted-bucket reduction. For digit `d`, the bucket is
`B[d] = Σ Pᵢ` over inputs assigned to that digit, and the window result is
`Σ d·B[d]`. `g1_combine_windows` then applies the `2^11` weight between adjacent
windows. The host oracle checks this prepared-CSR-to-MSM path across multiple
windows. The unit device fixture checks bucket accumulation and two-window
recomposition; the pipeline test below also connects digit extraction,
bucket-index construction, accumulation, reduction, and recomposition.
`msm_pipeline_test.cu` runs a tiny end-to-end device fixture: scalar window
extraction, CSR bucket construction, point accumulation, weighted bucket
reduction, and window recomposition. One scalar has a nonzero digit in the
second window, so the fixture checks cross-window weighting as well as bucket
construction. It compares `1·G + 2049·(2G) + 3·(3G)` with the independently
calculated `4108G`. This validates the custom kernel path for that fixture only.
It is not yet connected to `Accelerator::msm`, does not exercise production-sized
chunks, and has not been compiled or run on this Mac.

## BN254 arithmetic foundation

`bn254_fq.cuh` implements canonical-input Fq addition/subtraction and
Montgomery multiplication. `bn254_g1.cuh` implements Jacobian G1 doubling,
mixed affine addition, and affine conversion. The host probes compare those
operations with independent Python big-integer field and affine-curve formulas.
`g1_from_canonical_checked` rejects noncanonical coordinates and points outside
the curve before converting coordinates to Montgomery form. The scalar input
helper rejects values at or above the BN254 Fr modulus in the SoA buffer before
window extraction. These helpers do not replace the Rust adapter's subgroup
check and are not yet connected to `Accelerator::msm`.
The CUDA tests run doubling, equal-point mixed addition, inverse-point
cancellation, and a small full device MSM fixture. They do not yet exercise
production-sized chunks or connect this custom path to `Accelerator::msm`. The
current G1 affine conversion uses
exponentiation for inversion, suitable for checking formulas but not a
production normalization strategy for an MSM.

## Adapter validation

The adapter's host tests cover point and scalar conversion. CUDA-host tests
compare G1 MSM results with Xark's CPU Pippenger, including zero and maximum
canonical scalars, infinity, cancelling points, and deterministic subgroup
points. A proof test compares CPU and GPU proofs with fixed randomness and
verifies the result. These checks have not yet been run on an NVIDIA host, so
GPU correctness and performance remain unverified.

The adapter processes the prover's streamed G1 chunks. GPU measurements should
report input size, host-to-device transfer, kernel, device-to-host transfer, and
total chunk time separately. See `../../groth16-cuda/README.md` for build and
runtime instructions.

## References

- Groth16: [On the Size of Pairing-based Non-interactive Arguments][groth16-paper].
- GPU MSM design: [cuZK](https://eprint.iacr.org/2022/1321). This implementation
  follows the mathematical description and does not copy cuZK source.
- CUDA programming and performance: [CUDA C++ Programming Guide][cuda-guide]
  and [CUDA C++ Best Practices Guide][cuda-best-practices].
- Rust FFI safety: [The Rustonomicon](https://doc.rust-lang.org/nomicon/ffi.html).

[groth16-paper]: https://eprint.iacr.org/2016/260
[cuda-guide]: https://docs.nvidia.com/cuda/cuda-c-programming-guide/
[cuda-best-practices]: https://docs.nvidia.com/cuda/cuda-c-best-practices-guide/
