# Xark Groth16 CUDA MSM

This crate implements an optional BN254 G1 MSM accelerator for Xark's streaming
Groth16 prover. ICICLE performs the curve MSM. Xark's adapter decodes and checks
proving-key points, converts canonical arkworks limbs, validates the returned
point, and lets the prover fall back to CPU when CUDA is unavailable or an
operation is declined. G2 MSM currently stays on CPU.

The default Xark workspace and wasm builds do not depend on this crate. ICICLE is
pinned to the v4.0.0 commit and loads its CUDA backend at runtime. Install a
compatible ICICLE CUDA backend and set `ICICLE_BACKEND_INSTALL_DIR` before use.
The CUDA backend is separate from the Rust frontend; follow ICICLE's [v4 setup
guide](https://dev.ingonyama.com/setup) and install a backend built for the same
ICICLE release and a supported NVIDIA GPU.

Build the adapter and run its host-side representation checks:

```sh
cargo test --manifest-path crates/groth16-cuda/Cargo.toml --lib
cargo test --manifest-path crates/groth16-cuda/Cargo.toml --no-run
```

Run the MSM and proof-equivalence checks on a CUDA host:

```sh
XARK_CUDA_REQUIRED=1 cargo test --manifest-path crates/groth16-cuda/Cargo.toml --test gpu_msm
XARK_CUDA_REQUIRED=1 cargo test --manifest-path crates/groth16-cuda/Cargo.toml --test gpu_proof
```

The first command compiles the adapter and runs host-side checks. The latter two
require the ICICLE backend at runtime and fail if CUDA is not selected. For a
custom backend install directory, prefix those commands with
`ICICLE_BACKEND_INSTALL_DIR=/path/to/icicle/backend`.

The required run fails if the CUDA device/backend is missing, so it cannot silently
report a CPU-only run as GPU validation. The MSM comparison checks the result
against Xark's CPU Pippenger with a cancelling pair, an infinity point, and mixed
scalar values. The proof test creates a small real R1CS, generates a setup key,
requires each G1 proving-key chunk to be accepted by the GPU adapter, and verifies
the resulting proof with Xark's verifier.

## CUDA host validation

Requirements: Linux, an NVIDIA GPU, CUDA Toolkit, Nsight Systems, and the ICICLE
CUDA backend matching the pinned v4.0.0 Rust frontend. Run from a clean checkout:

```sh
crates/groth16-cuda/scripts/run_cuda_validation.sh
```

The run executes adapter unit tests, builds all adapter tests, requires CUDA for
the CPU/GPU MSM comparison and verified Groth16 proof, produces benchmark CSV,
and captures Nsight Systems traces at 65,536 and 524,288 points. It saves the
source revision, toolchain and GPU details, test logs, CSV, and profiler reports
under `out/cuda-validation/<commit>/`.

Set `ICICLE_BACKEND_INSTALL_DIR` for a non-default backend path. Workload and
output settings are available through `XARK_MSM_SIZES`, `XARK_PROFILE_SIZES`,
`XARK_MSM_REPEATS`, `XARK_MSM_SEED`, and `XARK_CUDA_RESULTS_DIR`.

Xark owns the serialization checks, arkworks-to-ICICLE field conversion, runtime
selection, output validation, and the small scalar-window CUDA kernel in
`../groth16/cuda`. ICICLE owns the BN254 curve MSM kernels, including bucket
accumulation. Keeping field and curve arithmetic in that audited implementation
avoids introducing a second cryptographic arithmetic stack in this adapter.
The window kernel is an independently tested building block today; it is not a
custom replacement for ICICLE's scalar decomposition.

The adapter remains opt-in and outside the root Cargo workspace, so CPU and wasm
builds do not acquire the ICICLE dependency. G2 MSM and quotient FFTs continue on
the existing CPU path. No performance claim is made until GPU timing is collected
on documented hardware and compared against Xark's CPU path.

## Reproducible MSM benchmark

`examples/msm_bench.rs` compares the complete adapter call with Xark's CPU
Pippenger on the same deterministic, canonical BN254 scalars and valid G1 points.
It reports CPU Pippenger alone, CPU decode plus Pippenger, and the complete GPU
adapter call. It checks output equality before and during timing. Input
generation and runtime initialization are outside the timed region. The default
sweep is 1,024, 65,536, and 524,288 points, with seven timed repetitions per
path. Each repetition runs CPU MSM, CPU decode plus MSM, and ICICLE in a rotated
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
  --example msm_bench -- --sizes 1024,65536,524288 --repeats 7 \
  --seed 24841619657020237 > xark-msm.csv
```

The GPU wall time covers point decoding, curve and subgroup checks, limb
conversion, the ICICLE call, and result conversion. The adapter uses the pinned
ICICLE `MSMConfig::default()`, which sets `is_async=false` and returns results to
host memory, so the call blocks before result conversion ([pinned source](https://github.com/ingonyama-zk/icicle/blob/6c77775961b0e4dc2be359feec1ac11536c18043/wrappers/rust/icicle-core/src/msm/mod.rs)). It is not a kernel-only number. The CPU chunk time decodes the same serialized input and runs Pippenger;
the CPU MSM time isolates Pippenger on already-decoded points. To inspect
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
