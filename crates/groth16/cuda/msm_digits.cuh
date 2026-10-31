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

XARK_CUDA_HD inline std::uint64_t scalar_modulus_limb(unsigned index) {
  switch (index) {
  case 0:
    return 0x43e1f593f0000001ULL;
  case 1:
    return 0x2833e84879b97091ULL;
  case 2:
    return 0xb85045b68181585dULL;
  case 3:
    return 0x30644e72e131a029ULL;
  default:
    return 0;
  }
}

XARK_CUDA_HD inline bool is_canonical_scalar(const std::uint64_t limbs[4]) {
  if (limbs == nullptr) {
    return false;
  }
  for (int i = 3; i >= 0; --i) {
    const std::uint64_t modulus = scalar_modulus_limb(i);
    if (limbs[i] < modulus) {
      return true;
    }
    if (limbs[i] > modulus) {
      return false;
    }
  }
  return false;
}

XARK_CUDA_HD inline bool
are_canonical_scalars_soa(const std::uint64_t *limbs_soa,
                          std::size_t scalar_count) {
  if (scalar_count > static_cast<std::size_t>(-1) / 4) {
    return false;
  }
  if (scalar_count != 0 && limbs_soa == nullptr) {
    return false;
  }
  for (std::size_t scalar = 0; scalar < scalar_count; ++scalar) {
    const std::uint64_t limbs[4] = {limbs_soa[scalar],
                                    limbs_soa[scalar_count + scalar],
                                    limbs_soa[2 * scalar_count + scalar],
                                    limbs_soa[3 * scalar_count + scalar]};
    if (!is_canonical_scalar(limbs)) {
      return false;
    }
  }
  return true;
}

XARK_CUDA_HD inline std::uint16_t extract_digit(const std::uint64_t *limbs_soa,
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

} // namespace xark_cuda

#undef XARK_CUDA_HD
