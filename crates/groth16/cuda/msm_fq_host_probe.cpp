#include <cstdint>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>

#include "bn254_fq.cuh"

namespace {

xark_cuda::Fq parse_hex(const std::string& hex) {
  if (hex.size() != 64) throw std::runtime_error("expected 256-bit hex input");
  std::uint32_t limbs[8]{};
  for (unsigned i = 0; i < 8; ++i) {
    const std::size_t offset = 56 - 8 * i;
    limbs[i] = static_cast<std::uint32_t>(
        std::stoul(hex.substr(offset, 8), nullptr, 16));
  }
  if (!xark_cuda::is_canonical(limbs)) {
    throw std::runtime_error("noncanonical Fq input");
  }
  return xark_cuda::from_canonical(limbs);
}

void print_hex(xark_cuda::Fq value) {
  for (int i = 7; i >= 0; --i) {
    std::cout << std::hex << std::nouppercase << std::setfill('0') << std::setw(8)
              << value.limbs[i];
  }
}

}  // namespace

int main() {
  try {
  std::string a_hex;
  std::string b_hex;
  while (std::cin >> a_hex >> b_hex) {
    const auto a = parse_hex(a_hex);
    const auto b = parse_hex(b_hex);
    print_hex(xark_cuda::to_canonical(xark_cuda::add(a, b)));
    std::cout << ' ';
    print_hex(xark_cuda::to_canonical(xark_cuda::subtract(a, b)));
    std::cout << ' ';
    print_hex(xark_cuda::to_canonical(xark_cuda::montgomery_multiply(a, b)));
    std::cout << '\n';
  }
  } catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 2;
  }
}
