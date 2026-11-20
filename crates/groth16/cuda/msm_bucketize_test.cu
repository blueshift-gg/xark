#include <cuda_runtime.h>

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

#include "msm_buckets.cuh"
#include "msm_bucket_reference.hpp"

namespace {

constexpr unsigned kThreads = 256;

__global__ void count_buckets(const std::uint16_t* digits, unsigned* counts,
                              std::size_t scalar_count,
                              std::size_t total_digits) {
  const std::size_t index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= total_digits) return;
  const unsigned digit = digits[index];
  if (xark_cuda::is_active_digit(digit)) {
    const unsigned window = static_cast<unsigned>(index / scalar_count);
    atomicAdd(&counts[window * xark_cuda::kBucketCount + digit], 1u);
  }
}

__global__ void prefix_buckets(const unsigned* counts, unsigned* offsets,
                               unsigned* cursors) {
  const unsigned window = blockIdx.x * blockDim.x + threadIdx.x;
  if (window >= xark_cuda::kWindowCount) return;
  const std::size_t count_base = window * xark_cuda::kBucketCount;
  const std::size_t offset_base = window * (xark_cuda::kBucketCount + 1);
  offsets[offset_base] = 0;
  for (unsigned bucket = 0; bucket < xark_cuda::kBucketCount; ++bucket) {
    offsets[offset_base + bucket + 1] =
        offsets[offset_base + bucket] + counts[count_base + bucket];
    cursors[count_base + bucket] = offsets[offset_base + bucket];
  }
}

__global__ void scatter_indices(const std::uint16_t* digits,
                                unsigned* cursors, unsigned* indices,
                                std::size_t scalar_count,
                                std::size_t total_digits) {
  const std::size_t index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= total_digits) return;
  const unsigned bucket = digits[index];
  if (!xark_cuda::is_active_digit(bucket)) return;
  const unsigned window = static_cast<unsigned>(index / scalar_count);
  const unsigned scalar = static_cast<unsigned>(index % scalar_count);
  const std::size_t count_base = window * xark_cuda::kBucketCount;
  const unsigned slot = atomicAdd(&cursors[count_base + bucket], 1u);
  indices[window * scalar_count + slot] = scalar;
}

void check(cudaError_t status, const char* operation) {
  if (status != cudaSuccess) {
    std::fprintf(stderr, "%s: %s\n", operation, cudaGetErrorString(status));
    std::exit(1);
  }
}

}  // namespace

int main() {
  int device_count = 0;
  const cudaError_t device_status = cudaGetDeviceCount(&device_count);
  if (device_status != cudaSuccess || device_count == 0) {
    std::fprintf(stderr, "CUDA device required: %s\n",
                 cudaGetErrorString(device_status));
    return 77;
  }

  constexpr std::size_t scalar_count = 1024;
  constexpr std::size_t total_digits = scalar_count * xark_cuda::kWindowCount;
  constexpr std::size_t count_size =
      xark_cuda::kWindowCount * xark_cuda::kBucketCount;
  constexpr std::size_t offset_size =
      xark_cuda::kWindowCount * (xark_cuda::kBucketCount + 1);
  std::vector<std::uint16_t> digits(total_digits);
  for (unsigned window = 0; window < xark_cuda::kWindowCount; ++window) {
    for (unsigned scalar = 0; scalar < scalar_count; ++scalar) {
      unsigned digit = 0;
      if (scalar < 512) {
        digit = 1;
      } else if (scalar < 768) {
        digit = xark_cuda::kMaxBucket;
      } else if (scalar % 3 != 0) {
        digit = 2 + ((scalar / 5 + window * 7) % 31);
      }
      digits[window * scalar_count + scalar] =
          static_cast<std::uint16_t>(digit);
    }
  }

  std::uint16_t* device_digits = nullptr;
  unsigned* device_counts = nullptr;
  unsigned* device_offsets = nullptr;
  unsigned* device_cursors = nullptr;
  unsigned* device_indices = nullptr;
  check(cudaMalloc(reinterpret_cast<void**>(&device_digits),
                   total_digits * sizeof(std::uint16_t)), "allocate digits");
  check(cudaMalloc(reinterpret_cast<void**>(&device_counts),
                   count_size * sizeof(unsigned)), "allocate counts");
  check(cudaMalloc(reinterpret_cast<void**>(&device_offsets),
                   offset_size * sizeof(unsigned)), "allocate offsets");
  check(cudaMalloc(reinterpret_cast<void**>(&device_cursors),
                   count_size * sizeof(unsigned)), "allocate cursors");
  check(cudaMalloc(reinterpret_cast<void**>(&device_indices),
                   total_digits * sizeof(unsigned)), "allocate indices");
  check(cudaMemcpy(device_digits, digits.data(),
                   total_digits * sizeof(std::uint16_t), cudaMemcpyHostToDevice),
        "copy digits");
  check(cudaMemset(device_counts, 0, count_size * sizeof(unsigned)),
        "clear counts");

  const unsigned blocks = static_cast<unsigned>(
      (total_digits + kThreads - 1) / kThreads);
  count_buckets<<<blocks, kThreads>>>(device_digits, device_counts,
                                     scalar_count, total_digits);
  check(cudaGetLastError(), "launch count_buckets");
  prefix_buckets<<<1, xark_cuda::kWindowCount>>>(device_counts, device_offsets,
                                                device_cursors);
  check(cudaGetLastError(), "launch prefix_buckets");
  scatter_indices<<<blocks, kThreads>>>(device_digits, device_cursors,
                                        device_indices, scalar_count,
                                        total_digits);
  check(cudaGetLastError(), "launch scatter_indices");
  check(cudaDeviceSynchronize(), "synchronize bucketization");

  std::vector<unsigned> offsets(offset_size);
  std::vector<unsigned> indices(total_digits);
  check(cudaMemcpy(offsets.data(), device_offsets,
                   offset_size * sizeof(unsigned), cudaMemcpyDeviceToHost),
        "copy offsets");
  check(cudaMemcpy(indices.data(), device_indices,
                   total_digits * sizeof(unsigned), cudaMemcpyDeviceToHost),
        "copy indices");

  const auto expected = xark_cuda_test::bucketize_reference(digits, scalar_count);
  if (offsets != expected.offsets) {
    std::fprintf(stderr, "bucket offsets differ from host reference\n");
    return 1;
  }

  for (unsigned window = 0; window < xark_cuda::kWindowCount; ++window) {
    const std::size_t offset_base = window * (xark_cuda::kBucketCount + 1);
    unsigned expected_offset = 0;
    for (unsigned bucket = 0; bucket < xark_cuda::kBucketCount; ++bucket) {
      if (offsets[offset_base + bucket + 1] > scalar_count) {
        std::fprintf(stderr, "bucket offset exceeds window capacity\n");
        return 1;
      }
      const unsigned end = offsets[offset_base + bucket + 1];
      std::vector<unsigned> actual;
      for (unsigned slot = offsets[offset_base + bucket]; slot < end; ++slot) {
        actual.push_back(indices[window * scalar_count + slot]);
      }
      std::sort(actual.begin(), actual.end());
      std::vector<unsigned> expected_members;
      for (unsigned slot = expected.offsets[offset_base + bucket];
           slot < expected.offsets[offset_base + bucket + 1]; ++slot) {
        expected_members.push_back(
            expected.point_indices[window * scalar_count + slot]);
      }
      if (actual != expected_members) {
        std::fprintf(stderr, "bucket members differ: window=%u bucket=%u\n",
                     window, bucket);
        return 1;
      }
      expected_offset += static_cast<unsigned>(expected_members.size());
      if (end != expected_offset) {
        std::fprintf(stderr, "bucket end differs from expected count\n");
        return 1;
      }
    }
  }

  check(cudaFree(device_indices), "free indices");
  check(cudaFree(device_cursors), "free cursors");
  check(cudaFree(device_offsets), "free offsets");
  check(cudaFree(device_counts), "free counts");
  check(cudaFree(device_digits), "free digits");
  std::printf("passed bucketization: %zu scalars x %u windows\n", scalar_count,
              xark_cuda::kWindowCount);
  return 0;
}
