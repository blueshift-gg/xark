#pragma once

#include <array>
#include <cstdint>
#include <limits>
#include <vector>

namespace xark_cuda_test {

inline std::vector<std::array<std::uint64_t, 4>> scalars() {
  std::vector<std::array<std::uint64_t, 4>> values = {
      {0, 0, 0, 0},
      {1, 0, 0, 0},
      {std::numeric_limits<std::uint64_t>::max(),
       std::numeric_limits<std::uint64_t>::max(),
       std::numeric_limits<std::uint64_t>::max(),
       std::numeric_limits<std::uint64_t>::max()},
      {0x0123456789abcdefULL, 0xfedcba9876543210ULL,
       0xaaaaaaaa55555555ULL, 0x8000000000000001ULL},
  };
  for (const unsigned bit : {10u, 11u, 63u, 64u, 65u, 127u, 128u, 191u,
                             192u, 252u, 253u, 254u, 255u}) {
    std::array<std::uint64_t, 4> scalar{};
    scalar[bit / 64] = std::uint64_t{1} << (bit % 64);
    values.push_back(scalar);
  }

  std::uint64_t state = 0x9e3779b97f4a7c15ULL;
  for (unsigned i = 0; i < 1024; ++i) {
    std::array<std::uint64_t, 4> scalar{};
    for (auto& limb : scalar) {
      state ^= state << 13;
      state ^= state >> 7;
      state ^= state << 17;
      limb = state;
    }
    values.push_back(scalar);
  }
  return values;
}

}  // namespace xark_cuda_test
