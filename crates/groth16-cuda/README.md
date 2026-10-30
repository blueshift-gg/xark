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
