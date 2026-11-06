#pragma once

#include <cstddef>
#include <cstdint>
#include <limits>

#include "bn254_g1.cuh"
#include "msm_buckets.cuh"

namespace xark_cuda {

enum class MsmPlanError {
  none,
  too_many_scalars,
  size_overflow,
  too_many_blocks,
};

struct MsmPlan {
  MsmPlanError error;
  std::size_t scalar_count;
  std::size_t total_digits;
  std::size_t bucket_count;
  std::size_t offset_count;
  unsigned digit_blocks;
  unsigned bucket_blocks;
  std::size_t device_bytes;

  bool valid() const { return error == MsmPlanError::none; }
  bool empty() const { return valid() && scalar_count == 0; }
};

inline bool checked_add(std::size_t left, std::size_t right,
                        std::size_t *result) {
  if (result == nullptr) {
    return false;
  }
  if (left > std::numeric_limits<std::size_t>::max() - right) {
    return false;
  }
  *result = left + right;
  return true;
}

inline bool checked_multiply(std::size_t left, std::size_t right,
                             std::size_t *result) {
  if (result == nullptr) {
    return false;
  }
  if (right != 0 && left > std::numeric_limits<std::size_t>::max() / right) {
    return false;
  }
  *result = left * right;
  return true;
}

inline MsmPlan make_msm_plan(std::size_t scalar_count,
                             unsigned threads_per_block = 256) {
  MsmPlan plan{MsmPlanError::none, scalar_count, 0, 0, 0, 0, 0, 0};
  if (scalar_count > std::numeric_limits<std::uint32_t>::max()) {
    plan.error = MsmPlanError::too_many_scalars;
    return plan;
  }
  if (threads_per_block == 0) {
    plan.error = MsmPlanError::too_many_blocks;
    return plan;
  }
  if (scalar_count == 0) {
    return plan;
  }

  if (!checked_multiply(scalar_count, kWindowCount, &plan.total_digits) ||
      !checked_multiply(kWindowCount, kBucketCount, &plan.bucket_count) ||
      !checked_multiply(kWindowCount, kBucketCount + 1, &plan.offset_count)) {
    plan.error = MsmPlanError::size_overflow;
    return plan;
  }

  std::size_t scalar_limb_count = 0;
  if (!checked_multiply(scalar_count, 4, &scalar_limb_count)) {
    plan.error = MsmPlanError::size_overflow;
    return plan;
  }

  std::size_t rounded_digits = 0;
  std::size_t rounded_buckets = 0;
  if (!checked_add(plan.total_digits, threads_per_block - 1, &rounded_digits) ||
      !checked_add(plan.bucket_count, threads_per_block - 1,
                   &rounded_buckets)) {
    plan.error = MsmPlanError::size_overflow;
    return plan;
  }
  const std::size_t digit_blocks = rounded_digits / threads_per_block;
  const std::size_t bucket_blocks = rounded_buckets / threads_per_block;
  if (digit_blocks > std::numeric_limits<unsigned>::max() ||
      bucket_blocks > std::numeric_limits<unsigned>::max()) {
    plan.error = MsmPlanError::too_many_blocks;
    return plan;
  }
  plan.digit_blocks = static_cast<unsigned>(digit_blocks);
  plan.bucket_blocks = static_cast<unsigned>(bucket_blocks);

  const std::size_t element_counts[] = {
      scalar_count,      // affine points
      scalar_limb_count, // scalar limbs in structure-of-arrays
      plan.total_digits, // scalar digits
      plan.bucket_count, // counts
      plan.offset_count, // CSR offsets
      plan.bucket_count, // scatter cursors
      plan.total_digits, // CSR point indices
      plan.bucket_count, // bucket sums
      kWindowCount,      // window sums
      1,                 // final result
  };
  const std::size_t element_sizes[] = {
      sizeof(G1Affine),   sizeof(std::uint64_t), sizeof(std::uint16_t),
      sizeof(unsigned),   sizeof(unsigned),      sizeof(unsigned),
      sizeof(unsigned),   sizeof(G1Jacobian),    sizeof(G1Jacobian),
      sizeof(G1Jacobian),
  };
  for (std::size_t i = 0;
       i < sizeof(element_counts) / sizeof(element_counts[0]); ++i) {
    std::size_t allocation_bytes = 0;
    if (!checked_multiply(element_counts[i], element_sizes[i],
                          &allocation_bytes) ||
        !checked_add(plan.device_bytes, allocation_bytes, &plan.device_bytes)) {
      plan.error = MsmPlanError::size_overflow;
      return plan;
    }
  }

  return plan;
}

} // namespace xark_cuda
