#include "msm_plan.hpp"

#include <cstdint>
#include <cstdio>
#include <limits>

namespace {

using namespace xark_cuda;

bool expect(bool condition, const char *message) {
  if (!condition) {
    std::fprintf(stderr, "%s\n", message);
    return false;
  }
  return true;
}

} // namespace

int main() {
  bool passed = true;

  const MsmPlan empty = make_msm_plan(0);
  passed &= expect(empty.valid() && empty.empty(), "empty plan is invalid");
  passed &= expect(empty.device_bytes == 0 && empty.digit_blocks == 0 &&
                       empty.bucket_blocks == 0,
                   "empty plan reserves buffers or launches blocks");

  const MsmPlan one = make_msm_plan(1);
  const std::size_t expected_bytes =
      sizeof(G1Affine) + 4 * sizeof(std::uint64_t) +
      kWindowCount * sizeof(std::uint16_t) +
      2 * kWindowCount * kBucketCount * sizeof(unsigned) +
      kWindowCount * (kBucketCount + 1) * sizeof(unsigned) +
      kWindowCount * sizeof(unsigned) +
      kWindowCount * kBucketCount * sizeof(G1Jacobian) +
      kWindowCount * sizeof(G1Jacobian) + sizeof(G1Jacobian);
  passed &= expect(one.valid(), "single-scalar plan is invalid");
  passed &= expect(one.total_digits == kWindowCount,
                   "single-scalar digit count is wrong");
  passed &= expect(one.bucket_count == kWindowCount * kBucketCount,
                   "bucket count is wrong");
  passed &= expect(one.offset_count == kWindowCount * (kBucketCount + 1),
                   "offset count is wrong");
  passed &= expect(one.digit_blocks == 1, "digit launch size is wrong");
  passed &= expect(one.bucket_blocks == (one.bucket_count + 255) / 256,
                   "bucket launch size is wrong");
  passed &= expect(one.device_bytes == expected_bytes,
                   "device buffer byte count is wrong");

  const MsmPlan invalid_block_size = make_msm_plan(1, 0);
  passed &= expect(invalid_block_size.error == MsmPlanError::too_many_blocks,
                   "zero thread block size was accepted");

  if (sizeof(std::size_t) > sizeof(std::uint32_t)) {
    const MsmPlan too_many = make_msm_plan(
        static_cast<std::size_t>(std::numeric_limits<std::uint32_t>::max()) +
        1);
    passed &= expect(too_many.error == MsmPlanError::too_many_scalars,
                     "32-bit CSR index limit was not enforced");
  } else {
    const MsmPlan overflow =
        make_msm_plan(std::numeric_limits<std::uint32_t>::max());
    passed &= expect(overflow.error == MsmPlanError::size_overflow,
                     "32-bit size_t digit count overflow was not rejected");
  }

  std::size_t value = 0;
  passed &=
      expect(!checked_add(std::numeric_limits<std::size_t>::max(), 1, &value),
             "checked addition accepted overflow");
  passed &= expect(
      !checked_multiply(std::numeric_limits<std::size_t>::max(), 2, &value),
      "checked multiplication accepted overflow");
  passed &= expect(!checked_add(1, 2, nullptr),
                   "checked addition accepted a null output");

  if (!passed) {
    return 1;
  }
  std::puts("passed checked MSM shape planning");
  return 0;
}
