#!/usr/bin/env bash
set -Eeuo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$script_dir/../../.." && pwd)
manifest="$repo_root/crates/groth16-cuda/Cargo.toml"

if [[ ${1:-} == "--help" ]]; then
  cat <<'EOF'
Run the ICICLE and custom CUDA MSM correctness, Groth16 proof, benchmark, and Nsight checks.

Optional environment:
  ICICLE_BACKEND_INSTALL_DIR  ICICLE CUDA backend installation directory
  XARK_CUDA_RESULTS_DIR       output directory (default: out/cuda-validation/<commit>)
  XARK_MSM_SIZES              comma-separated benchmark sizes
  XARK_PROFILE_SIZES          comma-separated sizes captured by Nsight
  XARK_MSM_REPEATS            benchmark repetitions (default: 7)
  XARK_MSM_SEED               deterministic input seed
  XARK_CUDA_SANITIZE=1        run the custom CUDA tests under Compute Sanitizer
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
if [[ "$target_dir" != /* ]]; then
  target_dir="$repo_root/$target_dir"
fi
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
if [[ ! -x /usr/bin/time ]]; then
  printf 'required tool is missing: /usr/bin/time (GNU time)\n' >&2
  exit 2
fi
if [[ ${XARK_CUDA_SANITIZE:-0} == 1 ]] && ! command -v compute-sanitizer >/dev/null 2>&1; then
  printf 'required tool is missing for XARK_CUDA_SANITIZE=1: compute-sanitizer\n' >&2
  exit 2
fi
if [[ ${XARK_CUDA_SANITIZE:-0} == 1 ]] && ! command -v python3 >/dev/null 2>&1; then
  printf 'required tool is missing for XARK_CUDA_SANITIZE=1: python3\n' >&2
  exit 2
fi

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
  if [[ ${XARK_CUDA_SANITIZE:-0} == 1 ]]; then
    printf '\ncompute-sanitizer:\n'
    compute-sanitizer --version
  fi
  printf '\ngpu:\n'
  nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv
  printf '\nicicle_backend_install_dir=%s\n' "${ICICLE_BACKEND_INSTALL_DIR:-default}"
} >"$results_dir/environment.txt" 2>&1

cargo test --manifest-path "$manifest" --lib 2>&1 \
  | tee "$results_dir/adapter-unit-tests.log"
cargo test --manifest-path "$manifest" --no-run 2>&1 \
  | tee "$results_dir/adapter-test-build.log"
cargo test --manifest-path "$manifest" --features custom-cuda --lib 2>&1 \
  | tee "$results_dir/custom-cuda-unit-tests.log"
cargo test --manifest-path "$manifest" --features custom-cuda --no-run 2>&1 \
  | tee "$results_dir/custom-cuda-test-build.log"
XARK_CUDA_REQUIRED=1 cargo test --manifest-path "$manifest" --test gpu_msm 2>&1 \
  | tee "$results_dir/gpu-msm-test.log"
XARK_CUDA_REQUIRED=1 cargo test --manifest-path "$manifest" --test gpu_proof 2>&1 \
  | tee "$results_dir/gpu-proof-test.log"
XARK_CUDA_REQUIRED=1 cargo test --manifest-path "$manifest" \
  --features custom-cuda --test gpu_custom_cuda 2>&1 \
  | tee "$results_dir/custom-gpu-msm-proof-test.log"
if [[ ${XARK_CUDA_SANITIZE:-0} == 1 ]]; then
  custom_test_binary=$(python3 - "$target_dir/debug/deps" <<'PY'
import os
import pathlib
import sys

executables = [
    path for path in pathlib.Path(sys.argv[1]).glob("gpu_custom_cuda-*")
    if path.is_file() and os.access(path, os.X_OK)
]
if executables:
    print(max(executables, key=lambda path: path.stat().st_mtime_ns))
PY
  )
  if [[ -z "$custom_test_binary" ]]; then
    printf 'custom CUDA test executable was not built\n' >&2
    exit 2
  fi
  compute-sanitizer --tool memcheck --leak-check full --error-exitcode 1 \
    "$custom_test_binary" --test-threads=1 2>&1 \
    | tee "$results_dir/custom-cuda-memcheck.log"
fi
cargo build --release --manifest-path "$manifest" --features custom-cuda \
  --example msm_bench 2>&1 | tee "$results_dir/msm-benchmark-build.log"
benchmark="$target_dir/release/examples/msm_bench"
/usr/bin/time -v "$benchmark" --backend icicle --sizes "$sizes" \
  --repeats "$repeats" --seed "$seed" \
  >"$results_dir/msm-benchmark-icicle.csv" \
  2>"$results_dir/msm-benchmark-icicle.log"
/usr/bin/time -v "$benchmark" --backend custom --sizes "$sizes" \
  --repeats "$repeats" --seed "$seed" \
  >"$results_dir/msm-benchmark-custom.csv" \
  2>"$results_dir/msm-benchmark-custom.log"

IFS=',' read -r -a capture_sizes <<<"$profile_sizes"
for backend in icicle custom; do
  for size in "${capture_sizes[@]}"; do
    report="$results_dir/msm-$backend-$size"
    nsys profile --trace=cuda,osrt --stats=true --force-overwrite=true \
      --output="$report" "$benchmark" --backend "$backend" --sizes "$size" \
      --repeats 3 --seed "$seed" >"$report.log" 2>&1
    nsys stats --report cuda_gpu_kern_sum,cuda_gpu_mem_time_sum,cuda_api_sum \
      "$report.nsys-rep" >"$report-stats.txt" 2>&1
  done
done

printf 'CUDA validation artifacts: %s\n' "$results_dir"
