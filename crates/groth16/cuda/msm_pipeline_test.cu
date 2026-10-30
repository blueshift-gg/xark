#include <cuda_runtime.h>

#include <cstdint>
#include <cstdio>
#include <cstdlib>

#include "msm_accumulate.cuh"
#include "msm_buckets.cuh"
#include "msm_digits.cuh"
#include "msm_plan.hpp"

namespace {

using namespace xark_cuda;
constexpr unsigned kThreads = 256;

__global__ void extract_digits(const std::uint64_t *limbs_soa,
                               std::uint16_t *digits, std::size_t scalar_count,
                               std::size_t total_digits) {
  const std::size_t index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= total_digits)
    return;
  const unsigned window = static_cast<unsigned>(index / scalar_count);
  const std::size_t scalar = index % scalar_count;
  digits[index] =
      xark_cuda::extract_digit(limbs_soa, scalar_count, scalar, window);
}

__global__ void count_buckets(const std::uint16_t *digits, unsigned *counts,
                              std::size_t scalar_count,
                              std::size_t total_digits) {
  const std::size_t index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= total_digits)
    return;
  const unsigned digit = digits[index];
  if (xark_cuda::is_active_digit(digit)) {
    const unsigned window = static_cast<unsigned>(index / scalar_count);
    atomicAdd(&counts[window * xark_cuda::kBucketCount + digit], 1u);
  }
}

__global__ void prefix_buckets(const unsigned *counts, unsigned *offsets,
                               unsigned *cursors) {
  const unsigned window = blockIdx.x * blockDim.x + threadIdx.x;
  if (window >= xark_cuda::kWindowCount)
    return;
  const std::size_t count_base = window * xark_cuda::kBucketCount;
  const std::size_t offset_base = window * (xark_cuda::kBucketCount + 1);
  offsets[offset_base] = 0;
  for (unsigned bucket = 0; bucket < xark_cuda::kBucketCount; ++bucket) {
    offsets[offset_base + bucket + 1] =
        offsets[offset_base + bucket] + counts[count_base + bucket];
    cursors[count_base + bucket] = offsets[offset_base + bucket];
  }
}

__global__ void scatter_indices(const std::uint16_t *digits, unsigned *cursors,
                                unsigned *indices, std::size_t scalar_count,
                                std::size_t total_digits) {
  const std::size_t index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= total_digits)
    return;
  const unsigned bucket = digits[index];
  if (!xark_cuda::is_active_digit(bucket))
    return;
  const unsigned window = static_cast<unsigned>(index / scalar_count);
  const unsigned scalar = static_cast<unsigned>(index % scalar_count);
  const std::size_t count_base = window * xark_cuda::kBucketCount;
  const unsigned slot = atomicAdd(&cursors[count_base + bucket], 1u);
  indices[window * scalar_count + slot] = scalar;
}

__global__ void
accumulate_buckets(const G1Affine *points, const unsigned *offsets,
                   const unsigned *indices, G1Jacobian *bucket_sums,
                   std::size_t scalar_count, std::size_t total_buckets) {
  const std::size_t index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= total_buckets)
    return;
  const unsigned window =
      static_cast<unsigned>(index / xark_cuda::kBucketCount);
  const unsigned bucket =
      static_cast<unsigned>(index % xark_cuda::kBucketCount);
  const std::size_t offset_base = window * (xark_cuda::kBucketCount + 1);
  const std::size_t index_base = window * scalar_count;
  const unsigned begin = offsets[offset_base + bucket];
  const unsigned end = offsets[offset_base + bucket + 1];
  bucket_sums[index] =
      xark_cuda::g1_accumulate_bucket(points, indices + index_base, begin, end);
}

__global__ void reduce_windows(const G1Jacobian *bucket_sums,
                               G1Jacobian *window_sums) {
  const unsigned window = blockIdx.x * blockDim.x + threadIdx.x;
  if (window >= xark_cuda::kWindowCount)
    return;
  window_sums[window] = xark_cuda::g1_reduce_buckets(
      bucket_sums + window * xark_cuda::kBucketCount, xark_cuda::kBucketCount);
}

__global__ void combine_windows(const G1Jacobian *window_sums,
                                G1Jacobian *result) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    *result = xark_cuda::g1_combine_windows(
        window_sums, xark_cuda::kWindowCount, xark_cuda::kWindowBits);
  }
}

void check(cudaError_t error, const char *operation) {
  if (error != cudaSuccess) {
    std::fprintf(stderr, "%s: %s\n", operation, cudaGetErrorString(error));
    std::exit(1);
  }
}

G1Affine make_point(const std::uint32_t x[8], const std::uint32_t y[8]) {
  G1Affine point{};
  if (!g1_from_canonical_checked(x, y, false, &point)) {
    std::fprintf(stderr, "invalid canonical G1 point fixture\n");
    std::exit(1);
  }
  return point;
}

bool equal(const std::uint32_t actual[8], const std::uint32_t expected[8]) {
  for (unsigned i = 0; i < 8; ++i) {
    if (actual[i] != expected[i])
      return false;
  }
  return true;
}

} // namespace

int main() {
  int device_count = 0;
  const cudaError_t device_status = cudaGetDeviceCount(&device_count);
  if (device_status != cudaSuccess || device_count == 0) {
    std::fprintf(stderr, "CUDA device required: %s\n",
                 cudaGetErrorString(device_status));
    return 77;
  }

  constexpr std::size_t scalar_count = 3;
  const MsmPlan plan = make_msm_plan(scalar_count, kThreads);
  if (!plan.valid()) {
    std::fprintf(stderr, "invalid MSM allocation plan: %u\n",
                 static_cast<unsigned>(plan.error));
    return 1;
  }
  const std::size_t total_digits = plan.total_digits;
  const std::size_t bucket_count = plan.bucket_count;
  const std::size_t offset_count = plan.offset_count;
  const std::uint32_t g_x[8] = {1, 0, 0, 0, 0, 0, 0, 0};
  const std::uint32_t g_y[8] = {2, 0, 0, 0, 0, 0, 0, 0};
  const std::uint32_t two_g_x[8] = {0x6d87cfd3u, 0xd3c208c1u, 0x16871ca8u,
                                    0xd97816a9u, 0x68181585u, 0x9b85045bu,
                                    0x2e131a02u, 0x030644e7u};
  const std::uint32_t two_g_y[8] = {0x5a18a2c4u, 0xff3ebf7au, 0xe3538fc7u,
                                    0x68a6a449u, 0xb2ae9c0au, 0xe7845f96u,
                                    0x0e0a7c92u, 0x15ed738cu};
  const std::uint32_t three_g_x[8] = {0x1915abf0u, 0xf2d35596u, 0x15b8e679u,
                                      0x9315d847u, 0xb1b6bd15u, 0xf40232bcu,
                                      0xc56bea3fu, 0x0769bf9au};
  const std::uint32_t three_g_y[8] = {0xd9fe2261u, 0xcdf1ff3du, 0x0b9c5b57u,
                                      0x319e63b4u, 0x8d086475u, 0x554fdb7cu,
                                      0xe0489429u, 0x2ab799beu};
  const G1Affine points[scalar_count] = {make_point(g_x, g_y),
                                         make_point(two_g_x, two_g_y),
                                         make_point(three_g_x, three_g_y)};
  const std::uint64_t scalar_limbs_soa[4 * scalar_count] = {1, 2, 3, 0, 0, 0,
                                                            0, 0, 0, 0, 0, 0};
  if (!are_canonical_scalars_soa(scalar_limbs_soa, scalar_count)) {
    std::fprintf(stderr, "noncanonical BN254 Fr fixture scalar\n");
    return 1;
  }

  std::uint64_t *device_scalars = nullptr;
  std::uint16_t *device_digits = nullptr;
  unsigned *device_counts = nullptr;
  unsigned *device_offsets = nullptr;
  unsigned *device_cursors = nullptr;
  unsigned *device_indices = nullptr;
  G1Affine *device_points = nullptr;
  G1Jacobian *device_bucket_sums = nullptr;
  G1Jacobian *device_window_sums = nullptr;
  G1Jacobian *device_result = nullptr;
  check(cudaMalloc(&device_scalars, sizeof(scalar_limbs_soa)),
        "allocate scalar limbs");
  check(cudaMalloc(&device_digits, total_digits * sizeof(std::uint16_t)),
        "allocate digits");
  check(cudaMalloc(&device_counts, bucket_count * sizeof(unsigned)),
        "allocate bucket counts");
  check(cudaMalloc(&device_offsets, offset_count * sizeof(unsigned)),
        "allocate bucket offsets");
  check(cudaMalloc(&device_cursors, bucket_count * sizeof(unsigned)),
        "allocate bucket cursors");
  check(cudaMalloc(&device_indices, total_digits * sizeof(unsigned)),
        "allocate point indices");
  check(cudaMalloc(&device_points, sizeof(points)), "allocate points");
  check(cudaMalloc(&device_bucket_sums, bucket_count * sizeof(G1Jacobian)),
        "allocate bucket sums");
  check(cudaMalloc(&device_window_sums, kWindowCount * sizeof(G1Jacobian)),
        "allocate window sums");
  check(cudaMalloc(&device_result, sizeof(G1Jacobian)), "allocate result");
  check(cudaMemcpy(device_scalars, scalar_limbs_soa, sizeof(scalar_limbs_soa),
                   cudaMemcpyHostToDevice),
        "copy scalars");
  check(
      cudaMemcpy(device_points, points, sizeof(points), cudaMemcpyHostToDevice),
      "copy points");
  check(cudaMemset(device_counts, 0, bucket_count * sizeof(unsigned)),
        "clear bucket counts");

  const unsigned digit_blocks = plan.digit_blocks;
  extract_digits<<<digit_blocks, kThreads>>>(device_scalars, device_digits,
                                             scalar_count, total_digits);
  check(cudaGetLastError(), "launch digit extraction");
  count_buckets<<<digit_blocks, kThreads>>>(device_digits, device_counts,
                                            scalar_count, total_digits);
  check(cudaGetLastError(), "launch bucket counts");
  prefix_buckets<<<1, kWindowCount>>>(device_counts, device_offsets,
                                      device_cursors);
  check(cudaGetLastError(), "launch bucket prefix");
  scatter_indices<<<digit_blocks, kThreads>>>(device_digits, device_cursors,
                                              device_indices, scalar_count,
                                              total_digits);
  check(cudaGetLastError(), "launch bucket scatter");
  const unsigned bucket_blocks = plan.bucket_blocks;
  accumulate_buckets<<<bucket_blocks, kThreads>>>(
      device_points, device_offsets, device_indices, device_bucket_sums,
      scalar_count, bucket_count);
  check(cudaGetLastError(), "launch point accumulation");
  reduce_windows<<<1, kWindowCount>>>(device_bucket_sums, device_window_sums);
  check(cudaGetLastError(), "launch weighted bucket reduction");
  combine_windows<<<1, 1>>>(device_window_sums, device_result);
  check(cudaGetLastError(), "launch window recomposition");

  G1Jacobian result{};
  check(cudaMemcpy(&result, device_result, sizeof(result),
                   cudaMemcpyDeviceToHost),
        "copy MSM result");
  check(cudaFree(device_result), "free result");
  check(cudaFree(device_window_sums), "free window sums");
  check(cudaFree(device_bucket_sums), "free bucket sums");
  check(cudaFree(device_points), "free points");
  check(cudaFree(device_indices), "free point indices");
  check(cudaFree(device_cursors), "free bucket cursors");
  check(cudaFree(device_offsets), "free bucket offsets");
  check(cudaFree(device_counts), "free bucket counts");
  check(cudaFree(device_digits), "free digits");
  check(cudaFree(device_scalars), "free scalar limbs");

  const G1Affine affine = g1_to_affine(result);
  const Fq actual_x = to_canonical(affine.x);
  const Fq actual_y = to_canonical(affine.y);
  const std::uint32_t expected_x[8] = {0x4e53cf66u, 0xb5a49bd8u, 0xca57c37fu,
                                       0x617bffd1u, 0xf46eff9du, 0x5d1cd2b1u,
                                       0x7880144bu, 0x15bf2bb1u};
  const std::uint32_t expected_y[8] = {0x93d1355fu, 0x624c1689u, 0x36598dd7u,
                                       0x2a212ee0u, 0x5e36f2eau, 0x83deb32bu,
                                       0x9ce0d170u, 0x049c797fu};
  if (affine.infinity || !equal(actual_x.limbs, expected_x) ||
      !equal(actual_y.limbs, expected_y)) {
    std::fprintf(stderr, "windowed CUDA MSM differs from 14G\n");
    return 1;
  }
  std::puts("passed end-to-end CUDA BN254 MSM: 3 points, 24 windows");
  return 0;
}
