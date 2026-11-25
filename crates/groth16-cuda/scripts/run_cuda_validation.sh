#!/usr/bin/env bash
set -Eeuo pipefail
export LC_ALL=C

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$script_dir/../../.." && pwd)
cd "$repo_root"
manifest="$repo_root/crates/groth16-cuda/Cargo.toml"
gpu_cli_manifest="$repo_root/crates/groth16-gpu-cli/Cargo.toml"

if [[ ${1:-} == "--help" ]]; then
  cat <<'EOF'
Run ICICLE and custom CUDA MSM correctness, cube CLI prove/verify, benchmarks, and Nsight checks.

Optional environment:
  ICICLE_BACKEND_INSTALL_DIR  ICICLE CUDA backend installation directory
  XARK_CUDA_RESULTS_DIR       output directory (default: out/cuda-validation/<commit>)
  XARK_MSM_SIZES              comma-separated benchmark sizes
  XARK_MSM_ENCODINGS          compressed, uncompressed, or both (default: both)
  XARK_PROFILE_SIZES          comma-separated sizes captured by Nsight
  XARK_MSM_REPEATS            benchmark repetitions (default: 7)
  XARK_MSM_SEED               deterministic input seed
  XARK_MSM_BACKEND_PASSES     benchmark passes, alternating backend order (default: 2)
  XARK_CUDA_CAPTURE_NSYS=0     skip Nsight traces for a correctness smoke run
  XARK_CUDA_SANITIZE=1        run custom CUDA tests under all Compute Sanitizer tools
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
sizes=${XARK_MSM_SIZES:-512,1023,1024,1025,4096,16384,65536,262144,524288}
encodings=${XARK_MSM_ENCODINGS:-both}
profile_sizes=${XARK_PROFILE_SIZES:-65536,524288}
repeats=${XARK_MSM_REPEATS:-7}
backend_passes=${XARK_MSM_BACKEND_PASSES:-2}
seed=${XARK_MSM_SEED:-24841619657020237}
capture_nsys=${XARK_CUDA_CAPTURE_NSYS:-1}

if [[ "$encodings" != compressed && "$encodings" != uncompressed && "$encodings" != both ]]; then
  printf 'XARK_MSM_ENCODINGS must be compressed, uncompressed, or both\n' >&2
  exit 2
fi

if [[ "$capture_nsys" != 0 && "$capture_nsys" != 1 ]]; then
  printf 'XARK_CUDA_CAPTURE_NSYS must be 0 or 1\n' >&2
  exit 2
fi
if [[ ! "$backend_passes" =~ ^[1-9][0-9]*$ ]]; then
  printf 'XARK_MSM_BACKEND_PASSES must be a positive integer\n' >&2
  exit 2
fi

required_tools=(cargo rustc git g++ make python3 nvidia-smi nvcc)
if [[ "$capture_nsys" == 1 ]]; then
  required_tools+=(nsys)
fi
for tool in "${required_tools[@]}"; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'required tool is missing: %s\n' "$tool" >&2
    exit 2
  fi
done
if [[ ! -x /usr/bin/time ]]; then
  printf 'required tool is missing: /usr/bin/time (GNU time)\n' >&2
  exit 2
fi

if [[ -z ${CUDA_VISIBLE_DEVICES+x} ]]; then
  gpu_selector=0
else
  gpu_selector=${CUDA_VISIBLE_DEVICES%%,*}
  if [[ -z "$gpu_selector" ]]; then
    printf 'CUDA_VISIBLE_DEVICES selects no visible GPU\n' >&2
    exit 2
  fi
fi
compute_cap=$(nvidia-smi --id="$gpu_selector" --query-gpu=compute_cap --format=csv,noheader | head -n 1 | tr -d '[:space:]')
if [[ ! "$compute_cap" =~ ^[0-9]+\.[0-9]+$ ]]; then
  printf 'could not read CUDA compute capability for selected GPU %s\n' "$gpu_selector" >&2
  exit 2
fi
cuda_arch=${compute_cap//./}
provided_nvcc_flags="${NVCC_PREPEND_FLAGS:-} ${NVCC_APPEND_FLAGS:-}"
if [[ ! "$provided_nvcc_flags" =~ (^|[[:space:]])(-arch(=|[[:space:]])|--gpu-architecture(=|[[:space:]])|-gencode(=|[[:space:]])|--generate-code(=|[[:space:]])) ]]; then
  export NVCC_PREPEND_FLAGS="${NVCC_PREPEND_FLAGS:+$NVCC_PREPEND_FLAGS }-arch=sm_${cuda_arch}"
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
stop_gpu_monitor() {
  if [[ -n ${gpu_monitor_pid:-} ]] && kill -0 "$gpu_monitor_pid" 2>/dev/null; then
    kill "$gpu_monitor_pid" 2>/dev/null || true
    wait "$gpu_monitor_pid" 2>/dev/null || true
  fi
}
finalize_artifacts() {
  run_status=$?
  stop_gpu_monitor
  if [[ -d "$results_dir" ]]; then
    (
      cd "$results_dir"
      find . -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 -r sha256sum >SHA256SUMS
    ) || true
  fi
  return "$run_status"
}
trap finalize_artifacts EXIT
export CARGO_TARGET_DIR="$target_dir"
export CXXFLAGS="${CXXFLAGS:+$CXXFLAGS }-include stdint.h"

{
  printf 'commit=%s\n' "$commit"
  printf 'date_utc=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf '\nhost:\n'
  uname -a
  if command -v lscpu >/dev/null 2>&1; then lscpu; fi
  if command -v free >/dev/null 2>&1; then free -h; fi
  printf '\nrustc:\n'
  rustc --version --verbose
  printf '\ncargo:\n'
  cargo --version
  printf '\ng++:\n'
  g++ --version
  printf '\nCXXFLAGS:\n%s\n' "$CXXFLAGS"
  printf '\nnvcc:\n'
  nvcc --version
  if [[ "$capture_nsys" == 1 ]]; then
    printf '\nnsys:\n'
    nsys --version
  else
    printf '\nnsys=skipped\n'
  fi
  printf '\ncuda_capture_nsys=%s\n' "$capture_nsys"
  printf 'cuda_compute_capability=%s\n' "$compute_cap"
  printf 'nvcc_prepend_flags=%s\n' "${NVCC_PREPEND_FLAGS:-unset}"
  printf 'nvcc_append_flags=%s\n' "${NVCC_APPEND_FLAGS:-unset}"
  printf 'cuda_visible_devices=%s\n' "${CUDA_VISIBLE_DEVICES:-unset}"
  printf 'cuda_build_gpu_selector=%s\n' "$gpu_selector"
  printf 'msm_sizes=%s\n' "$sizes"
  printf 'msm_encodings=%s\n' "$encodings"
  printf 'msm_repeats=%s\n' "$repeats"
  printf 'msm_backend_passes=%s\n' "$backend_passes"
  printf 'msm_seed=%s\n' "$seed"
  printf 'profile_sizes=%s\n' "$profile_sizes"
  if [[ ${XARK_CUDA_SANITIZE:-0} == 1 ]]; then
    printf '\ncompute-sanitizer:\n'
    compute-sanitizer --version
  fi
  printf '\ngpu:\n'
  nvidia-smi --query-gpu=index,name,compute_cap,driver_version,memory.total,memory.free --format=csv
  printf '\nGPU clocks, temperature, power, utilization, and memory snapshot:\n'
  nvidia-smi -q -d CLOCK,POWER,TEMPERATURE,UTILIZATION,MEMORY
  printf '\nICICLE Rust frontend revision:\n'
  awk '/^icicle-bn254 = \{/ { in_block = 1 } in_block { print } in_block && /}/ { exit }' "$manifest"
  printf '\nicicle_backend_install_dir=%s\n' "${ICICLE_BACKEND_INSTALL_DIR:-default}"
} >"$results_dir/environment.txt" 2>&1

if [[ -n ${ICICLE_BACKEND_INSTALL_DIR:-} && -d "$ICICLE_BACKEND_INSTALL_DIR" ]]; then
  find -L "$ICICLE_BACKEND_INSTALL_DIR" -type f \
    \( -name '*.so' -o -name '*.so.*' \) -print0 \
    | sort -z \
    | xargs -0 -r sha256sum >"$results_dir/icicle-backend-files.sha256"
fi

nvidia-smi dmon --id="$gpu_selector" -s pucm -d 1 >"$results_dir/gpu-dmon.log" 2>&1 &
gpu_monitor_pid=$!
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

cargo build --release -p xark-cli --features debug 2>&1 \
  | tee "$results_dir/cuda-cli-cpu-build.log"
cargo build --release --manifest-path "$gpu_cli_manifest" --features cuda-msm,debug \
  --bin xark-gpu 2>&1 | tee "$results_dir/cuda-cli-icicle-build.log"
cargo build --release --manifest-path "$gpu_cli_manifest" --features custom-cuda-msm,debug \
  --bin xark-gpu 2>&1 | tee "$results_dir/cuda-cli-custom-build.log"

/usr/bin/time -v cargo run --release -p xark-cli -- setup examples/cube 2>&1 \
  | tee "$results_dir/cuda-cli-setup.log"
PROVE_TIME=1 /usr/bin/time -v cargo run --release -p xark-cli --features debug -- \
  prove examples/cube --inputs '{"secret":"3","result":"27"}' 2>&1 \
  | tee "$results_dir/cuda-cli-cpu-prove.log"
/usr/bin/time -v cargo run --release -p xark-cli -- verify examples/cube 2>&1 \
  | tee "$results_dir/cuda-cli-cpu-verify.log"

PROVE_TIME=1 /usr/bin/time -v cargo run --release --manifest-path "$gpu_cli_manifest" --features cuda-msm,debug \
  --bin xark-gpu -- prove examples/cube \
  --inputs '{"secret":"3","result":"27"}' --accelerator cuda \
  --acknowledge-gpu-side-channel-risk 2>&1 \
  | tee "$results_dir/cuda-cli-icicle-prove.log"
grep -E 'MSM backend: Cuda; status=.*; GPU G1 chunks=[1-9][0-9]* points=' \
  "$results_dir/cuda-cli-icicle-prove.log"
PROVE_TIME=1 /usr/bin/time -v cargo run --release -p xark-cli -- verify examples/cube 2>&1 \
  | tee "$results_dir/cuda-cli-icicle-verify.log"

PROVE_TIME=1 /usr/bin/time -v cargo run --release --manifest-path "$gpu_cli_manifest" --features custom-cuda-msm,debug \
  --bin xark-gpu -- prove examples/cube \
  --inputs '{"secret":"3","result":"27"}' --accelerator cuda \
  --acknowledge-gpu-side-channel-risk 2>&1 \
  | tee "$results_dir/cuda-cli-custom-prove.log"
grep -E 'MSM backend: Cuda; status=.*; GPU G1 chunks=[1-9][0-9]* points=' \
  "$results_dir/cuda-cli-custom-prove.log"
PROVE_TIME=1 /usr/bin/time -v cargo run --release -p xark-cli -- verify examples/cube 2>&1 \
  | tee "$results_dir/cuda-cli-custom-verify.log"

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
  # Keep racecheck and synccheck in the matrix for future shared-memory kernels.
  for sanitizer_tool in memcheck initcheck racecheck synccheck; do
    sanitizer_options=(--tool "$sanitizer_tool" --error-exitcode 1)
    if [[ "$sanitizer_tool" == memcheck ]]; then
      sanitizer_options+=(--leak-check full)
    fi
    XARK_CUDA_REQUIRED=1 compute-sanitizer "${sanitizer_options[@]}" \
      "$custom_test_binary" --test-threads=1 2>&1 \
      | tee "$results_dir/custom-cuda-${sanitizer_tool}.log"
  done
fi
cargo build --release --manifest-path "$manifest" --features custom-cuda \
  --example msm_bench 2>&1 | tee "$results_dir/msm-benchmark-build.log"
benchmark="$target_dir/release/examples/msm_bench"
for ((pass = 1; pass <= backend_passes; pass++)); do
  if ((pass % 2 == 1)); then
    backend_order=(icicle custom)
  else
    backend_order=(custom icicle)
  fi
  for backend in "${backend_order[@]}"; do
    /usr/bin/time -v "$benchmark" --backend "$backend" --sizes "$sizes" \
      --encoding "$encodings" --repeats "$repeats" --seed "$seed" \
      >"$results_dir/msm-benchmark-${backend}-pass-${pass}.csv" \
      2>"$results_dir/msm-benchmark-${backend}-pass-${pass}.log"
  done
done

if [[ "$capture_nsys" == 1 ]]; then
  IFS=',' read -r -a capture_sizes <<<"$profile_sizes"
  for backend in icicle custom; do
    for size in "${capture_sizes[@]}"; do
      report="$results_dir/msm-$backend-$size"
      nsys profile --trace=cuda,osrt --stats=true --force-overwrite=true \
        --output="$report" "$benchmark" --backend "$backend" --sizes "$size" \
        --encoding compressed --repeats 3 --seed "$seed" >"$report.log" 2>&1
      nsys stats --report cuda_gpu_kern_sum,cuda_gpu_mem_time_sum,cuda_api_sum \
        "$report.nsys-rep" >"$report-stats.txt" 2>&1
    done
  done
fi

python3 - "$results_dir" <<'PY' >"$results_dir/proof-cli-timings.csv"
import csv
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1])
rows = []

def wall_seconds(path):
    text = path.read_text(errors="replace")
    match = re.search(
        r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)", text
    )
    if not match:
        raise SystemExit(f"could not read GNU time wall duration from {path}")
    value = [float(part) for part in match.group(1).split(":")]
    seconds = value[-1]
    if len(value) > 1:
        seconds += value[-2] * 60
    if len(value) > 2:
        seconds += value[-3] * 3600
    return seconds

def duration_seconds(value):
    units = {"h": 3600, "m": 60, "s": 1, "ms": 1e-3, "µs": 1e-6, "ns": 1e-9}
    parts = re.findall(r"([0-9]+(?:\.[0-9]+)?)(ms|µs|ns|h|m|s)", value)
    if not parts:
        raise SystemExit(f"could not parse Rust duration {value!r}")
    return sum(float(amount) * units[unit] for amount, unit in parts)

for label in ("cpu", "icicle", "custom"):
    prove_log = root / f"cuda-cli-{label}-prove.log"
    verify_log = root / f"cuda-cli-{label}-verify.log"
    prove_text = prove_log.read_text(errors="replace")
    phases = re.findall(
        r"PROVE_TIME: \[streaming\] solve=(.*?) prove=(\S+)", prove_text
    )
    solve_s = sum(duration_seconds(solve) for solve, _ in phases)
    prove_internal_s = sum(duration_seconds(prove) for _, prove in phases)
    prove_wall_s = wall_seconds(prove_log)
    verify_wall_s = wall_seconds(verify_log)
    rows.append({
        "backend": label,
        "prove_command_wall_s": f"{prove_wall_s:.6f}",
        "prove_internal_solve_s": f"{solve_s:.6f}",
        "prove_internal_prove_s": f"{prove_internal_s:.6f}",
        "external_verify_wall_s": f"{verify_wall_s:.6f}",
        "prove_plus_external_verify_wall_s": f"{prove_wall_s + verify_wall_s:.6f}",
        "self_check_retry_cpu": str("retrying once with CPU" in prove_text).lower(),
        "phase_reports": str(len(phases)),
    })

writer = csv.DictWriter(sys.stdout, fieldnames=list(rows[0]))
writer.writeheader()
writer.writerows(rows)
PY

printf 'CUDA validation artifacts: %s\n' "$results_dir"
