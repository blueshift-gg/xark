#pragma once

#include <cstdint>

#include "bn254_g1.cuh"

#if defined(__CUDACC__)
#define XARK_MSM_HD __host__ __device__
#else
#define XARK_MSM_HD
#endif

namespace xark_cuda {

// Sum the points listed in one CSR bucket. Inputs must already be validated
// affine BN254 G1 points and offsets must describe a valid index range.
XARK_MSM_HD inline G1Jacobian
g1_accumulate_bucket(const G1Affine *points, const std::uint32_t *point_indices,
                     std::uint32_t begin, std::uint32_t end) {
  G1Jacobian sum = g1_infinity();
  for (std::uint32_t slot = begin; slot < end; ++slot) {
    sum = g1_add_mixed(sum, points[point_indices[slot]]);
  }
  return sum;
}

// Descending running sums turn bucket b into b * bucket[b]. Bucket zero is
// intentionally ignored because zero digits do not enter a CSR bucket.
XARK_MSM_HD inline G1Jacobian g1_reduce_buckets(const G1Jacobian *buckets,
                                                std::uint32_t bucket_count) {
  G1Jacobian running = g1_infinity();
  G1Jacobian result = g1_infinity();
  for (std::uint32_t bucket = bucket_count; bucket > 1; --bucket) {
    running = g1_add_jacobian(running, buckets[bucket - 1]);
    result = g1_add_jacobian(result, running);
  }
  return result;
}

// Recompose window sums in scalar order: MSM = Σ window_sum[w] * 2^(w*b).
XARK_MSM_HD inline G1Jacobian g1_combine_windows(const G1Jacobian *window_sums,
                                                 std::uint32_t window_count,
                                                 std::uint32_t window_bits) {
  G1Jacobian result = g1_infinity();
  for (std::uint32_t window = window_count; window > 0; --window) {
    for (std::uint32_t bit = 0; bit < window_bits; ++bit) {
      result = g1_double(result);
    }
    result = g1_add_jacobian(result, window_sums[window - 1]);
  }
  return result;
}

} // namespace xark_cuda

#undef XARK_MSM_HD
