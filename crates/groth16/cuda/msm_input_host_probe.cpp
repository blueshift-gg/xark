#include <cstdint>
#include <iomanip>
#include <iostream>
#include <string>

#include "bn254_g1.cuh"

namespace {

bool parse_canonical(const std::string &hex, std::uint32_t limbs[8]) {
  if (hex.size() != 64) {
    return false;
  }
  for (unsigned i = 0; i < 8; ++i) {
    const std::size_t offset = 56 - 8 * i;
    try {
      std::size_t parsed = 0;
      const std::string word = hex.substr(offset, 8);
      const auto value = std::stoul(word, &parsed, 16);
      if (parsed != word.size()) {
        return false;
      }
      limbs[i] = static_cast<std::uint32_t>(value);
    } catch (...) {
      return false;
    }
  }
  return true;
}

void print_hex(const std::uint32_t limbs[8]) {
  for (int i = 7; i >= 0; --i) {
    std::cout << std::hex << std::nouppercase << std::setfill('0')
              << std::setw(8) << limbs[i];
  }
}

} // namespace

int main() {
  const std::uint32_t zero[8]{};
  xark_cuda::G1Affine ignored{};
  if (xark_cuda::g1_from_canonical_checked(nullptr, zero, false, &ignored) ||
      xark_cuda::g1_from_canonical_checked(zero, nullptr, false, &ignored) ||
      xark_cuda::g1_from_canonical_checked(zero, zero, false, nullptr)) {
    std::cerr << "checked G1 conversion accepted a null argument\n";
    return 2;
  }

  unsigned infinity = 0;
  std::string x_hex;
  std::string y_hex;
  while (std::cin >> infinity >> x_hex >> y_hex) {
    std::uint32_t x[8]{};
    std::uint32_t y[8]{};
    if (infinity > 1 || !parse_canonical(x_hex, x) ||
        !parse_canonical(y_hex, y)) {
      std::cout << "0\n";
      continue;
    }

    xark_cuda::G1Affine point{};
    if (!xark_cuda::g1_from_canonical_checked(x, y, infinity != 0, &point)) {
      std::cout << "0\n";
      continue;
    }
    std::cout << "1 ";
    const auto x_canonical = xark_cuda::to_canonical(point.x);
    print_hex(x_canonical.limbs);
    std::cout << ' ';
    const auto y_canonical = xark_cuda::to_canonical(point.y);
    print_hex(y_canonical.limbs);
    std::cout << '\n';
  }
}
