#pragma once

#include <cstddef>
#include <cstdint>

#if defined(__CUDACC__)
#define XARK_CUDA_HD __host__ __device__
#else
#define XARK_CUDA_HD
#endif

namespace xark_cuda {

constexpr unsigned kWindowBits = 11;
constexpr unsigned kWindowCount = (256 + kWindowBits - 1) / kWindowBits;
constexpr std::uint16_t kDigitMask = (1u << kWindowBits) - 1;

XARK_CUDA_HD inline std::uint16_t extract_digit(const std::uint64_t* limbs_soa,
                                                std::size_t scalar_count,
                                                std::size_t scalar,
                                                unsigned window) {
  const unsigned bit = window * kWindowBits;
  const unsigned limb = bit / 64;
  const unsigned shift = bit % 64;

  std::uint64_t value = limbs_soa[limb * scalar_count + scalar] >> shift;
  if (shift != 0 && limb + 1 < 4) {
    value |= limbs_soa[(limb + 1) * scalar_count + scalar] << (64 - shift);
  }
  return static_cast<std::uint16_t>(value & kDigitMask);
}

}  // namespace xark_cuda

#undef XARK_CUDA_HD
