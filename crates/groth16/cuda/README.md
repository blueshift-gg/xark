# BN254 MSM CUDA work

This directory contains a CUDA scalar-window extraction kernel and its tests. It
does not implement a curve MSM and is not called by the prover. The optional
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
structure-of-arrays for the same reason. The final window contains only the
remaining eight bits of a 256-bit input.

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

The host test does not compile or execute the `.cu` kernel.

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

- Groth16: [On the Size of Pairing-based Non-interactive Arguments](https://eprint.iacr.org/2016/260).
- GPU MSM design: [cuZK](https://eprint.iacr.org/2022/1321). This implementation is written from the mathematical description and does not copy cuZK source.
- CUDA programming and performance: [CUDA C++ Programming Guide](https://docs.nvidia.com/cuda/cuda-c-programming-guide/) and [CUDA C++ Best Practices Guide](https://docs.nvidia.com/cuda/cuda-c-best-practices-guide/).
- Rust FFI safety: [The Rustonomicon](https://doc.rust-lang.org/nomicon/ffi.html).
