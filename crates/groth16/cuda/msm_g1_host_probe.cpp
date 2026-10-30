#include <cstdint>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <string>

#include "bn254_g1.cuh"

namespace {

xark_cuda::Fq parse_hex(const std::string& hex) {
  if (hex.size() != 64) throw std::runtime_error("expected 256-bit hex input");
  std::uint32_t canonical[8]{};
  for (unsigned i = 0; i < 8; ++i) {
    const std::size_t offset = 56 - 8 * i;
    canonical[i] = static_cast<std::uint32_t>(
        std::stoul(hex.substr(offset, 8), nullptr, 16));
  }
  if (!xark_cuda::is_canonical(canonical)) {
    throw std::runtime_error("noncanonical Fq coordinate");
  }
  return xark_cuda::from_canonical(canonical);
}

void print_hex(xark_cuda::Fq value) {
  const auto canonical = xark_cuda::to_canonical(value);
  for (int i = 7; i >= 0; --i) {
    std::cout << std::hex << std::nouppercase << std::setfill('0') << std::setw(8)
              << canonical.limbs[i];
  }
}

}  // namespace

int main() {
  try {
  unsigned operation;
  unsigned left_infinity;
  unsigned right_infinity;
  std::string lx;
  std::string ly;
  std::string rx;
  std::string ry;
  while (std::cin >> operation >> left_infinity >> lx >> ly >> right_infinity >> rx >> ry) {
    const xark_cuda::G1Affine left{parse_hex(lx), parse_hex(ly), left_infinity != 0};
    const xark_cuda::G1Affine right{parse_hex(rx), parse_hex(ry), right_infinity != 0};
    auto projective = xark_cuda::g1_from_affine(left);
    if (operation == 1) {
      projective = xark_cuda::g1_double(projective);
    } else if (operation == 0) {
      projective = xark_cuda::g1_add_mixed(projective, right);
    } else if (operation == 2) {
      const auto scalar = xark_cuda::to_canonical(right.x);
      projective = xark_cuda::g1_infinity();
      for (int bit = 253; bit >= 0; --bit) {
        projective = xark_cuda::g1_double(projective);
        if (((scalar.limbs[bit / 32] >> (bit % 32)) & 1u) != 0) {
          projective = xark_cuda::g1_add_mixed(projective, left);
        }
      }
    } else {
      throw std::runtime_error("unknown operation");
    }
    const auto affine = xark_cuda::g1_to_affine(projective);
    std::cout << (affine.infinity ? 1 : 0) << ' ';
    print_hex(affine.x);
    std::cout << ' ';
    print_hex(affine.y);
    std::cout << '\n';
  }
  } catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 2;
  }
}
