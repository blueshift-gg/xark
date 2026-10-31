# Xark Groth16 CUDA MSM

This crate provides optional BN254 G1 MSM accelerators for Xark's streaming
Groth16 prover. `IcicleMsm` delegates curve arithmetic to ICICLE.
`CustomCudaMsm`, enabled by the `custom-cuda` feature, runs Xark's scalar-window,
bucket-index, point-accumulation, and reduction kernels. Both adapters validate
proving-key inputs and returned points, then decline unsupported work so the
prover can use its CPU path. G2 MSM currently stays on CPU.

Xark streams proving-key MSM work in chunks, with `ProverConfig::msm_chunk`
defaulting to 524,288 points. ICICLE's signed `i32` count limit applies to one
adapter call, not the total circuit size. If a configured chunk exceeds that
limit, the adapter splits it into `i32`-sized calls and sums their results.

The default Xark workspace and wasm builds do not depend on this crate. The
ICICLE Rust crates are pinned to commit
[`6c77775961b0e4dc2be359feec1ac11536c18043`](https://github.com/ingonyama-zk/icicle/releases/tag/v4.0.0),
the ICICLE v4.0.0 release. Pinning fixes the source revision used to build this
adapter; it does not represent an independent security audit. ICICLE loads its
CUDA backend at runtime. Install a
compatible ICICLE CUDA backend and set `ICICLE_BACKEND_INSTALL_DIR` before use.
The CUDA backend is separate from the Rust frontend; follow ICICLE's [v4 setup
guide](https://dev.ingonyama.com/setup) and install a backend built for the same
ICICLE release and a supported NVIDIA GPU.

Build the adapter and run its host-side representation checks:

```sh
cargo test --manifest-path crates/groth16-cuda/Cargo.toml --lib
cargo test --manifest-path crates/groth16-cuda/Cargo.toml --no-run
```

Build the custom CUDA backend on a host with `nvcc`:

```sh
cargo test --manifest-path crates/groth16-cuda/Cargo.toml \
  --features custom-cuda --lib
```

Pass `CustomCudaMsm` to the prover to select the custom backend. It is not
enabled implicitly and does not fall through to ICICLE. If its CUDA call fails,
the prover uses CPU MSM.

The library tests also generate and verify a deterministic Groth16 proof with
both `Local` and `IcicleMsm`, then compare the proof bytes. Without a CUDA
backend, `IcicleMsm` declines and the prover exercises its CPU fallback. With a
working CUDA backend, the adapter path is used. This host test does not require
CUDA; the required-device integration test below does.

Run the MSM and proof-equivalence checks on a CUDA host:

```sh
XARK_CUDA_REQUIRED=1 cargo test --manifest-path crates/groth16-cuda/Cargo.toml --test gpu_msm
XARK_CUDA_REQUIRED=1 cargo test --manifest-path crates/groth16-cuda/Cargo.toml --test gpu_proof
XARK_CUDA_REQUIRED=1 cargo test --manifest-path crates/groth16-cuda/Cargo.toml \
  --features custom-cuda --test gpu_custom_cuda
```

The ICICLE tests require the ICICLE backend at runtime. The custom test compiles
the `.cu` bridge with `nvcc` and requires a CUDA device. For a
custom backend install directory, prefix those commands with
`ICICLE_BACKEND_INSTALL_DIR=/path/to/icicle/backend`.

The required run fails if the CUDA device/backend is missing, so it cannot silently
report a CPU-only run as GPU validation. The MSM comparison checks the result
against Xark's CPU Pippenger with a cancelling pair, an infinity point, and mixed
scalar values. The proof test creates a small real R1CS, generates a setup key,
requires each G1 proving-key chunk to be accepted by the GPU adapter, and verifies
the resulting proof with Xark's verifier.

## CUDA host validation

Requirements: Linux, an NVIDIA GPU, CUDA Toolkit, Nsight Systems, GNU time, and the ICICLE
CUDA backend matching the pinned v4.0.0 Rust frontend. Run from a clean checkout:

```sh
crates/groth16-cuda/scripts/run_cuda_validation.sh
```

The run executes host checks, builds both adapters, requires CUDA for the ICICLE
and custom MSM comparisons and verified proofs, writes a benchmark CSV per
backend, and captures Nsight Systems traces at 65,536 and 524,288 points for
both. It saves the source revision, toolchain and GPU details, test logs, CSVs,
and profiler reports under `out/cuda-validation/<commit>/`.

Set `ICICLE_BACKEND_INSTALL_DIR` for a non-default backend path. Workload and
output settings are available through `XARK_MSM_SIZES`, `XARK_PROFILE_SIZES`,
`XARK_MSM_REPEATS`, `XARK_MSM_SEED`, and `XARK_CUDA_RESULTS_DIR`.
Set `XARK_CUDA_SANITIZE=1` to run the custom CUDA integration tests under
Compute Sanitizer's memory checker with device leak checking enabled. This checks
CUDA memory accesses and device allocations; it does not measure host RSS.
Each benchmark log also records peak process RSS through GNU time.

The custom path converts canonical arkworks points and scalars to the native
input layout, checks curve coordinates and scalar bounds, then runs window
extraction, CSR bucketization, G1 accumulation, weighted bucket reduction, and
window recomposition in `../groth16/cuda`. Arkworks checks the result before
serialization. Each bucket currently accumulates its members serially. This
backend includes CUDA MSM and proof integration tests, which require an NVIDIA
host to run. No performance claim is made before those checks and measurements.

The adapters remain opt-in and outside the root Cargo workspace, so CPU and wasm
builds do not compile CUDA code. G2 MSM and quotient FFTs continue on the existing
CPU path. The benchmark below can select either backend. No
performance claim is made until both backends are measured on documented
hardware and compared against Xark's CPU path.

To measure the current CPU G2 MSM baseline against Arkworks at one thread and
the available Rayon thread count, run:

```sh
cargo run --release -p xark-groth16 --example bench_kernels -- g2
```

This seeded benchmark checks each result against Arkworks and reports the input
size, thread count, and elapsed time. It measures CPU MSM only; it is not a GPU
result or a full proof benchmark.

## Reproducible MSM benchmark

`examples/msm_bench.rs` compares the selected GPU adapter call with Xark's CPU
Pippenger on the same deterministic, canonical BN254 scalars and valid G1 points.
It reports CPU Pippenger alone, parallel CPU point decoding alone, CPU decode
plus Pippenger, and the complete GPU adapter call. The decode-only number gives
a host-side baseline; it is not a measured speedup over GPU-side preparation.
It checks output equality before and during timing. Input
generation and runtime initialization are outside the timed region. The default
sweep is 1,024, 65,536, and 524,288 points, with seven timed repetitions per
path. Each repetition runs the CPU paths and selected backend in a rotated
order to reduce ordering bias. Output includes every raw sample and median,
minimum, and maximum rows. The CSV has separate `repeat` and `stat` columns.
Compressed points are the default; use `--encoding both` to include uncompressed
key input.

Record the machine and backend, then save the CSV output with the source revision:

```sh
nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv
nvcc --version
git rev-parse HEAD
cargo run --release --manifest-path crates/groth16-cuda/Cargo.toml \
  --features custom-cuda --example msm_bench -- --backend icicle \
  --sizes 1024,65536,524288 --repeats 7 \
  --seed 24841619657020237 > xark-icicle-msm.csv
cargo run --release --manifest-path crates/groth16-cuda/Cargo.toml \
  --features custom-cuda --example msm_bench -- --backend custom \
  --sizes 1024,65536,524288 --repeats 7 \
  --seed 24841619657020237 > xark-msm.csv
```

The adapters decode and convert point inputs in parallel for chunks of at least
1,024 points; smaller chunks remain serial to avoid thread-pool overhead. The
GPU wall time covers point decoding, curve checks, transfers, the
selected MSM, and result conversion. BN254 G1 has cofactor one, so checking that
a point is on the curve also establishes subgroup membership. This is not a
kernel-only number. The CPU decode-only time measures parallel decoding, and
CPU chunk time decodes the same serialized input and runs Pippenger. CPU MSM
time isolates Pippenger on already-decoded points. To inspect
transfers and kernel durations, build the example and capture the same run with
Nsight Systems:

```sh
cargo build --release --manifest-path crates/groth16-cuda/Cargo.toml \
  --example msm_bench
nsys profile --trace=cuda,osrt --stats=true --force-overwrite=true \
  --output=xark-msm-65536 \
  crates/groth16-cuda/target/release/examples/msm_bench \
  --sizes 65536 --repeats 3 --seed 24841619657020237
nsys stats --report cuda_gpu_kern_sum,cuda_gpu_mem_time_sum,cuda_api_sum \
  xark-msm-65536.nsys-rep
nsys profile --trace=cuda,osrt --stats=true --force-overwrite=true \
  --output=xark-msm-524288 \
  crates/groth16-cuda/target/release/examples/msm_bench \
  --sizes 524288 --repeats 3 --seed 24841619657020237
nsys stats --report cuda_gpu_kern_sum,cuda_gpu_mem_time_sum,cuda_api_sum \
  xark-msm-524288.nsys-rep
```

Each capture includes the harness warmup and timed repetitions. Use the
Nsight Systems timeline to inspect CUDA activity; the aggregate summary includes
warmup activity as well. The CSV's ICICLE wall time is the full adapter call and
cannot by itself separate transfer and kernel time. Nsight's operation summaries
report CUDA API, kernel, and memory-operation durations separately; those
activity summaries are not the adapter's wall-clock chunk time and should not be
added to infer it. See NVIDIA's [Nsight Systems analysis guide](https://docs.nvidia.com/nsight-systems/AnalysisGuide/index.html).

The benchmark currently uses seeded random subgroup points, not points sampled
from a production proving key. The proof-equivalence test remains the end-to-end
check against a generated key and fixed randomness. Save the raw CSV, profiler
report, GPU/driver/toolkit versions, and ICICLE backend build together. Do not
infer a speedup from the small correctness test or from total time without the
CPU baseline.
