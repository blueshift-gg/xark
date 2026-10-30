#!/usr/bin/env bash
set -Eeuo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$script_dir/../../.." && pwd)
manifest="$repo_root/crates/groth16-cuda/Cargo.toml"

if [[ ${1:-} == "--help" ]]; then
  cat <<'EOF'
Run the ICICLE MSM correctness, Groth16 proof, benchmark, and Nsight checks.

Optional environment:
  ICICLE_BACKEND_INSTALL_DIR  ICICLE CUDA backend installation directory
  XARK_CUDA_RESULTS_DIR       output directory (default: out/cuda-validation/<commit>)
  XARK_MSM_SIZES              comma-separated benchmark sizes
  XARK_PROFILE_SIZES          comma-separated sizes captured by Nsight
  XARK_MSM_REPEATS            benchmark repetitions (default: 7)
  XARK_MSM_SEED               deterministic input seed
EOF
  exit 0
fi

if [[ $# -ne 0 ]]; then
  printf 'unexpected argument: %s\n' "$1" >&2
  exit 2
fi

if [[ -n $(git -C "$repo_root" status --porcelain --untracked-files=all) ]]; then
  printf 'run CUDA validation from a clean Git worktree\n' >&2
  exit 2
fi

commit=$(git -C "$repo_root" rev-parse --short HEAD)
results_dir=${XARK_CUDA_RESULTS_DIR:-"$repo_root/out/cuda-validation/$commit"}
target_dir=${CARGO_TARGET_DIR:-"$repo_root/crates/groth16-cuda/target"}
sizes=${XARK_MSM_SIZES:-1024,65536,524288}
profile_sizes=${XARK_PROFILE_SIZES:-65536,524288}
repeats=${XARK_MSM_REPEATS:-7}
seed=${XARK_MSM_SEED:-24841619657020237}

for tool in cargo rustc nvidia-smi nvcc nsys; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'required tool is missing: %s\n' "$tool" >&2
    exit 2
  fi
done

mkdir -p "$results_dir"
export CARGO_TARGET_DIR="$target_dir"

{
  printf 'commit=%s\n' "$commit"
  printf 'date_utc=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf '\nrustc:\n'
  rustc --version --verbose
  printf '\ncargo:\n'
  cargo --version
  printf '\nnvcc:\n'
  nvcc --version
  printf '\nnsys:\n'
  nsys --version
  printf '\ngpu:\n'
  nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv
  printf '\nicicle_backend_install_dir=%s\n' "${ICICLE_BACKEND_INSTALL_DIR:-default}"
} >"$results_dir/environment.txt" 2>&1

cargo test --manifest-path "$manifest" --lib 2>&1 \
  | tee "$results_dir/adapter-unit-tests.log"
cargo test --manifest-path "$manifest" --no-run 2>&1 \
  | tee "$results_dir/adapter-test-build.log"
XARK_CUDA_REQUIRED=1 cargo test --manifest-path "$manifest" --test gpu_msm 2>&1 \
  | tee "$results_dir/gpu-msm-test.log"
XARK_CUDA_REQUIRED=1 cargo test --manifest-path "$manifest" --test gpu_proof 2>&1 \
  | tee "$results_dir/gpu-proof-test.log"
cargo run --release --manifest-path "$manifest" --example msm_bench -- \
  --sizes "$sizes" --repeats "$repeats" --seed "$seed" \
  >"$results_dir/msm-benchmark.csv" 2>"$results_dir/msm-benchmark.log"

IFS=',' read -r -a capture_sizes <<<"$profile_sizes"
benchmark="$target_dir/release/examples/msm_bench"
for size in "${capture_sizes[@]}"; do
  report="$results_dir/msm-$size"
  nsys profile --trace=cuda,osrt --stats=true --force-overwrite=true \
    --output="$report" "$benchmark" --sizes "$size" --repeats 3 --seed "$seed" \
    >"$report.log" 2>&1
  nsys stats --report cuda_gpu_kern_sum,cuda_gpu_mem_time_sum,cuda_api_sum \
    "$report.nsys-rep" >"$report-stats.txt" 2>&1
done

printf 'CUDA validation artifacts: %s\n' "$results_dir"
