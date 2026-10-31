#include <array>
#include <cstdint>
#include <cstdio>
#include <vector>

#include "msm_digits.cuh"
#include "msm_digits_test_vectors.hpp"

namespace {

std::uint16_t reference_digit(const std::array<std::uint64_t, 4>& scalar,
                              unsigned window) {
  std::uint16_t digit = 0;
  for (unsigned bit = 0; bit < xark_cuda::kWindowBits; ++bit) {
    const unsigned source_bit = window * xark_cuda::kWindowBits + bit;
    if (source_bit < 256 &&
        ((scalar[source_bit / 64] >> (source_bit % 64)) & 1u) != 0) {
      digit |= static_cast<std::uint16_t>(1u << bit);
    }
  }
  return digit;
}

}  // namespace

int main() {
  const auto scalars = xark_cuda_test::scalars();
  std::vector<std::uint64_t> limbs_soa(4 * scalars.size());
  for (std::size_t scalar = 0; scalar < scalars.size(); ++scalar) {
    for (std::size_t limb = 0; limb < 4; ++limb) {
      limbs_soa[limb * scalars.size() + scalar] = scalars[scalar][limb];
    }
  }

  for (std::size_t scalar = 0; scalar < scalars.size(); ++scalar) {
    for (unsigned window = 0; window < xark_cuda::kWindowCount; ++window) {
      const auto got = xark_cuda::extract_digit(limbs_soa.data(), scalars.size(),
                                                scalar, window);
      const auto expected = reference_digit(scalars[scalar], window);
      if (got != expected) {
        std::fprintf(stderr,
                     "digit mismatch: scalar=%zu window=%u got=%u expected=%u\n",
                     scalar, window, got, expected);
        return 1;
      }
    }
  }

  std::printf("passed host digit check: %zu scalars x %u windows\n",
              scalars.size(), xark_cuda::kWindowCount);
  return 0;
}
