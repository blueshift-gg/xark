#include <cstdint>
#include <iostream>
#include <string>

#include "msm_digits.cuh"

int main() {
  const std::uint64_t valid_soa[8] = {
      1, 0x43e1f593f0000000ULL, 0, 0x2833e84879b97091ULL,
      0, 0xb85045b68181585dULL, 0, 0x30644e72e131a029ULL};
  const std::uint64_t invalid_soa[8] = {
      1, 0x43e1f593f0000001ULL, 0, 0x2833e84879b97091ULL,
      0, 0xb85045b68181585dULL, 0, 0x30644e72e131a029ULL};
  if (!xark_cuda::are_canonical_scalars_soa(valid_soa, 2) ||
      xark_cuda::are_canonical_scalars_soa(invalid_soa, 2) ||
      xark_cuda::are_canonical_scalars_soa(nullptr, 1) ||
      !xark_cuda::are_canonical_scalars_soa(nullptr, 0) ||
      xark_cuda::are_canonical_scalars_soa(
          valid_soa, static_cast<std::size_t>(-1) / 4 + 1)) {
    std::cerr << "structure-of-arrays scalar validation failed\n";
    return 2;
  }

  std::string hex;
  while (std::cin >> hex) {
    if (hex.size() != 64) {
      std::cout << "0\n";
      continue;
    }
    std::uint64_t limbs[4]{};
    bool parsed_all = true;
    for (unsigned i = 0; i < 4; ++i) {
      const std::size_t offset = 48 - 16 * i;
      try {
        std::size_t parsed = 0;
        const std::string word = hex.substr(offset, 16);
        limbs[i] = std::stoull(word, &parsed, 16);
        parsed_all &= parsed == word.size();
      } catch (...) {
        parsed_all = false;
      }
    }
    std::cout << (parsed_all && xark_cuda::is_canonical_scalar(limbs) ? 1 : 0)
              << '\n';
  }
}
