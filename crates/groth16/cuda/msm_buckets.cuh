#pragma once

#include <cstdint>

#include "msm_digits.cuh"

namespace xark_cuda {

constexpr unsigned kBucketCount = 1u << kWindowBits;
constexpr unsigned kMaxBucket = kBucketCount - 1;

#if defined(__CUDACC__)
__host__ __device__
#endif
inline bool is_active_digit(std::uint16_t digit) { return digit != 0; }

}  // namespace xark_cuda
