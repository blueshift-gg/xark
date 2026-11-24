#pragma once

#include <cstdint>
#include <limits>
#include <stdexcept>
#include <vector>

#include "msm_buckets.cuh"

namespace xark_cuda_test {

struct BucketCsr {
  std::vector<unsigned> offsets;
  std::vector<unsigned> point_indices;
};

inline BucketCsr bucketize_reference(const std::vector<std::uint16_t>& digits,
                                     std::size_t scalar_count) {
  if (scalar_count == 0 || scalar_count > std::numeric_limits<unsigned>::max()) {
    throw std::invalid_argument("scalar_count is out of range");
  }
  if (scalar_count > std::numeric_limits<std::size_t>::max() /
                         xark_cuda::kWindowCount) {
    throw std::invalid_argument("digit buffer size overflows");
  }
  if (digits.size() != scalar_count * xark_cuda::kWindowCount) {
    throw std::invalid_argument("digit buffer has the wrong size");
  }

  const std::size_t counts_size =
      xark_cuda::kWindowCount * xark_cuda::kBucketCount;
  const std::size_t offsets_size =
      xark_cuda::kWindowCount * (xark_cuda::kBucketCount + 1);
  std::vector<unsigned> counts(counts_size, 0);
  BucketCsr result{std::vector<unsigned>(offsets_size, 0),
                   std::vector<unsigned>(digits.size(), 0)};

  for (unsigned window = 0; window < xark_cuda::kWindowCount; ++window) {
    for (std::size_t scalar = 0; scalar < scalar_count; ++scalar) {
      const unsigned digit = digits[window * scalar_count + scalar];
      if (digit > xark_cuda::kMaxBucket) {
        throw std::invalid_argument("digit exceeds the bucket range");
      }
      if (xark_cuda::is_active_digit(static_cast<std::uint16_t>(digit))) {
        ++counts[window * xark_cuda::kBucketCount + digit];
      }
    }
  }

  for (unsigned window = 0; window < xark_cuda::kWindowCount; ++window) {
    const std::size_t count_base = window * xark_cuda::kBucketCount;
    const std::size_t offset_base = window * (xark_cuda::kBucketCount + 1);
    for (unsigned bucket = 0; bucket < xark_cuda::kBucketCount; ++bucket) {
      result.offsets[offset_base + bucket + 1] =
          result.offsets[offset_base + bucket] + counts[count_base + bucket];
      counts[count_base + bucket] = result.offsets[offset_base + bucket];
    }
    for (std::size_t scalar = 0; scalar < scalar_count; ++scalar) {
      const unsigned bucket = digits[window * scalar_count + scalar];
      if (bucket == 0) continue;
      const unsigned slot = counts[count_base + bucket]++;
      result.point_indices[window * scalar_count + slot] =
          static_cast<unsigned>(scalar);
    }
  }
  return result;
}

}  // namespace xark_cuda_test
