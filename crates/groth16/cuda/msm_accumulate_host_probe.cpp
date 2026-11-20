#include <cstdint>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

#include "msm_accumulate.cuh"

namespace {

xark_cuda::Fq parse_hex(const std::string &hex) {
  if (hex.size() != 64)
    throw std::runtime_error("expected 256-bit hex input");
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
    std::cout << std::hex << std::nouppercase << std::setfill('0')
              << std::setw(8) << canonical.limbs[i];
  }
}

} // namespace

int main() {
  try {
    std::size_t point_count;
    std::uint32_t window_count;
    std::uint32_t bucket_count;
    while (std::cin >> point_count >> window_count >> bucket_count) {
      std::vector<xark_cuda::G1Affine> points;
      points.reserve(point_count);
      for (std::size_t i = 0; i < point_count; ++i) {
        unsigned infinity;
        std::string x;
        std::string y;
        std::cin >> infinity >> x >> y;
        points.push_back({parse_hex(x), parse_hex(y), infinity != 0});
      }

      std::vector<xark_cuda::G1Jacobian> window_sums(window_count);
      for (std::uint32_t window = 0; window < window_count; ++window) {
        std::vector<std::uint32_t> offsets(bucket_count + 1);
        for (auto &offset : offsets)
          std::cin >> offset;
        if (!std::cin || offsets.front() != 0) {
          throw std::runtime_error("invalid CSR start offset");
        }
        for (std::size_t i = 1; i < offsets.size(); ++i) {
          if (offsets[i] < offsets[i - 1]) {
            throw std::runtime_error("nonmonotonic CSR offsets");
          }
        }
        const std::size_t member_count = offsets.back();
        std::vector<std::uint32_t> indices(member_count);
        for (auto &index : indices)
          std::cin >> index;
        if (!std::cin)
          throw std::runtime_error("incomplete CSR indices");
        for (const auto index : indices) {
          if (index >= point_count) {
            throw std::runtime_error("point index out of range");
          }
        }

        std::vector<xark_cuda::G1Jacobian> buckets(bucket_count);
        for (std::uint32_t bucket = 0; bucket < bucket_count; ++bucket) {
          buckets[bucket] = xark_cuda::g1_accumulate_bucket(
              points.data(), indices.data(), offsets[bucket],
              offsets[bucket + 1]);
        }
        window_sums[window] =
            xark_cuda::g1_reduce_buckets(buckets.data(), bucket_count);
      }

      const auto combined =
          xark_cuda::g1_combine_windows(window_sums.data(), window_count, 11);
      const auto result = xark_cuda::g1_to_affine(combined);
      std::cout << (result.infinity ? 1 : 0) << ' ';
      print_hex(result.x);
      std::cout << ' ';
      print_hex(result.y);
      std::cout << '\n';
    }
  } catch (const std::exception &error) {
    std::cerr << error.what() << '\n';
    return 2;
  }
}
