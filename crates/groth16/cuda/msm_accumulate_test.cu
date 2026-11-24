#include <cuda_runtime.h>

#include <cstdint>
#include <cstdio>
#include <cstdlib>

#include "msm_accumulate.cuh"

namespace {

using namespace xark_cuda;

__global__ void accumulate_buckets(const G1Affine *points,
                                   const std::uint32_t *offsets,
                                   const std::uint32_t *indices,
                                   G1Jacobian *buckets,
                                   std::uint32_t bucket_count) {
  const std::uint32_t bucket = blockIdx.x * blockDim.x + threadIdx.x;
  if (bucket >= bucket_count)
    return;
  buckets[bucket] = g1_accumulate_bucket(points, indices, offsets[bucket],
                                         offsets[bucket + 1]);
}

__global__ void reduce_buckets(const G1Jacobian *buckets,
                               std::uint32_t bucket_count,
                               G1Jacobian *results) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    const G1Jacobian window_sum = g1_reduce_buckets(buckets, bucket_count);
    const G1Jacobian windows[2] = {window_sum, window_sum};
    results[0] = window_sum;
    results[1] = g1_combine_windows(windows, 2, 11);
  }
}

void check(cudaError_t error, const char *operation) {
  if (error != cudaSuccess) {
    std::fprintf(stderr, "%s: %s\n", operation, cudaGetErrorString(error));
    std::exit(1);
  }
}

G1Affine make_point(const std::uint32_t x[8], const std::uint32_t y[8]) {
  return G1Affine{from_canonical(x), from_canonical(y), false};
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
  constexpr std::uint32_t bucket_count = 4;
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
  const G1Affine points[3] = {make_point(g_x, g_y),
                              make_point(two_g_x, two_g_y),
                              make_point(three_g_x, three_g_y)};
  const std::uint32_t offsets[bucket_count + 1] = {0, 0, 1, 2, 3};
  const std::uint32_t indices[3] = {0, 1, 2};

  G1Affine *device_points = nullptr;
  std::uint32_t *device_offsets = nullptr;
  std::uint32_t *device_indices = nullptr;
  G1Jacobian *device_buckets = nullptr;
  G1Jacobian *device_result = nullptr;
  check(cudaMalloc(&device_points, sizeof(points)), "allocate points");
  check(cudaMalloc(&device_offsets, sizeof(offsets)), "allocate offsets");
  check(cudaMalloc(&device_indices, sizeof(indices)), "allocate indices");
  check(cudaMalloc(&device_buckets, bucket_count * sizeof(G1Jacobian)),
        "allocate bucket sums");
  check(cudaMalloc(&device_result, 2 * sizeof(G1Jacobian)), "allocate results");
  check(
      cudaMemcpy(device_points, points, sizeof(points), cudaMemcpyHostToDevice),
      "copy points");
  check(cudaMemcpy(device_offsets, offsets, sizeof(offsets),
                   cudaMemcpyHostToDevice),
        "copy offsets");
  check(cudaMemcpy(device_indices, indices, sizeof(indices),
                   cudaMemcpyHostToDevice),
        "copy indices");

  accumulate_buckets<<<1, 32>>>(device_points, device_offsets, device_indices,
                                device_buckets, bucket_count);
  check(cudaGetLastError(), "launch bucket accumulation");
  reduce_buckets<<<1, 1>>>(device_buckets, bucket_count, device_result);
  check(cudaGetLastError(), "launch weighted bucket reduction");

  G1Jacobian buckets[bucket_count]{};
  G1Jacobian results[2]{};
  check(cudaMemcpy(buckets, device_buckets, sizeof(buckets),
                   cudaMemcpyDeviceToHost),
        "copy bucket sums");
  check(cudaMemcpy(results, device_result, sizeof(results),
                   cudaMemcpyDeviceToHost),
        "copy reduced results");
  check(cudaFree(device_result), "free result");
  check(cudaFree(device_buckets), "free bucket sums");
  check(cudaFree(device_indices), "free indices");
  check(cudaFree(device_offsets), "free offsets");
  check(cudaFree(device_points), "free points");

  if (!g1_is_infinity(buckets[0])) {
    std::fprintf(stderr, "zero-digit bucket should be empty\n");
    return 1;
  }
  const G1Affine affine = g1_to_affine(results[0]);
  const std::uint32_t expected_x[8] = {0x4e53cf66u, 0xb5a49bd8u, 0xca57c37fu,
                                       0x617bffd1u, 0xf46eff9du, 0x5d1cd2b1u,
                                       0x7880144bu, 0x15bf2bb1u};
  const std::uint32_t expected_y[8] = {0x93d1355fu, 0x624c1689u, 0x36598dd7u,
                                       0x2a212ee0u, 0x5e36f2eau, 0x83deb32bu,
                                       0x9ce0d170u, 0x049c797fu};
  const Fq actual_x = to_canonical(affine.x);
  const Fq actual_y = to_canonical(affine.y);
  if (affine.infinity || !equal(actual_x.limbs, expected_x) ||
      !equal(actual_y.limbs, expected_y)) {
    std::fprintf(stderr, "weighted bucket reduction differs from 14G\n");
    return 1;
  }
  const G1Affine combined = g1_to_affine(results[1]);
  const Fq combined_x = to_canonical(combined.x);
  const Fq combined_y = to_canonical(combined.y);
  const std::uint32_t expected_combined_x[8] = {
      0x07025dacu, 0xecdb322cu, 0xfa0dfbadu, 0x7f69464eu,
      0x1c2a360au, 0x668f58b9u, 0x40143912u, 0x152ee83au};
  const std::uint32_t expected_combined_y[8] = {
      0x5864f603u, 0x3b88647du, 0x36256198u, 0x38314848u,
      0x0b994725u, 0x5b7b16b5u, 0x52d3bf51u, 0x121c4effu};
  if (combined.infinity || !equal(combined_x.limbs, expected_combined_x) ||
      !equal(combined_y.limbs, expected_combined_y)) {
    std::fprintf(stderr, "window recomposition differs from 28686G\n");
    return 1;
  }
  std::puts("passed CUDA BN254 bucket accumulation and two-window reduction");
  return 0;
}
