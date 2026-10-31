#include <cstdint>
#include <cstdio>
#include <stdexcept>
#include <vector>

#include "msm_bucket_reference.hpp"

namespace {

constexpr std::size_t kScalarCount = 64;

std::vector<std::uint16_t> mixed_digits() {
  std::vector<std::uint16_t> digits(kScalarCount * xark_cuda::kWindowCount);
  for (unsigned window = 0; window < xark_cuda::kWindowCount; ++window) {
    for (std::size_t scalar = 0; scalar < kScalarCount; ++scalar) {
      unsigned digit = 0;
      if (scalar < 20) {
        digit = 1;
      } else if (scalar < 31) {
        digit = xark_cuda::kMaxBucket;
      } else if (scalar % 4 != 0) {
        digit = 2 + static_cast<unsigned>((scalar + window) % 5);
      }
      digits[window * kScalarCount + scalar] =
          static_cast<std::uint16_t>(digit);
    }
  }
  return digits;
}

bool check_membership(const std::vector<std::uint16_t>& digits,
                      const xark_cuda_test::BucketCsr& csr) {
  for (unsigned window = 0; window < xark_cuda::kWindowCount; ++window) {
    const std::size_t offset_base = window * (xark_cuda::kBucketCount + 1);
    std::vector<bool> seen(kScalarCount, false);
    if (csr.offsets[offset_base] != 0) return false;
    for (unsigned bucket = 0; bucket < xark_cuda::kBucketCount; ++bucket) {
      const unsigned begin = csr.offsets[offset_base + bucket];
      const unsigned end = csr.offsets[offset_base + bucket + 1];
      if (begin > end || end > kScalarCount) return false;
      for (unsigned slot = begin; slot < end; ++slot) {
        const unsigned scalar =
            csr.point_indices[window * kScalarCount + slot];
        if (scalar >= kScalarCount || seen[scalar] || bucket == 0 ||
            digits[window * kScalarCount + scalar] != bucket) {
          return false;
        }
        seen[scalar] = true;
      }
    }
    for (std::size_t scalar = 0; scalar < kScalarCount; ++scalar) {
      if (seen[scalar] != (digits[window * kScalarCount + scalar] != 0)) {
        return false;
      }
    }
  }
  return true;
}

}  // namespace

int main() {
  std::vector<std::uint16_t> zeros(kScalarCount * xark_cuda::kWindowCount, 0);
  const auto empty = xark_cuda_test::bucketize_reference(zeros, kScalarCount);
  if (!check_membership(zeros, empty) ||
      empty.offsets.back() != 0) {
    std::fprintf(stderr, "zero-digit CSR check failed\n");
    return 1;
  }

  const auto mixed = mixed_digits();
  const auto csr = xark_cuda_test::bucketize_reference(mixed, kScalarCount);
  if (!check_membership(mixed, csr)) {
    std::fprintf(stderr, "mixed-digit CSR membership check failed\n");
    return 1;
  }

  try {
    auto invalid = mixed;
    invalid[0] = static_cast<std::uint16_t>(xark_cuda::kBucketCount);
    (void)xark_cuda_test::bucketize_reference(invalid, kScalarCount);
    std::fprintf(stderr, "out-of-range digit was accepted\n");
    return 1;
  } catch (const std::invalid_argument&) {
  }

  std::printf("passed host bucket reference: %zu scalars x %u windows\n",
              kScalarCount, xark_cuda::kWindowCount);
  return 0;
}
