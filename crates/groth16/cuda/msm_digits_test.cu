#include <cuda_runtime.h>

#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

#include "msm_digits.cuh"
#include "msm_digits_test_vectors.hpp"

namespace {

constexpr unsigned kThreads = 256;

__global__ void extract_digits(const std::uint64_t* limbs_soa,
                               std::uint16_t* digits,
                               std::size_t scalar_count,
                               std::size_t total_digits) {
  const std::size_t index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= total_digits) return;

  const unsigned window = static_cast<unsigned>(index / scalar_count);
  const std::size_t scalar = index % scalar_count;
  digits[index] =
      xark_cuda::extract_digit(limbs_soa, scalar_count, scalar, window);
}

void check(cudaError_t status, const char* operation) {
  if (status != cudaSuccess) {
    std::fprintf(stderr, "%s: %s\n", operation, cudaGetErrorString(status));
    std::exit(1);
  }
}

std::uint16_t cpu_digit(const std::array<std::uint64_t, 4>& scalar,
                        unsigned window) {
  std::uint16_t digit = 0;
  for (unsigned bit = 0; bit < xark_cuda::kWindowBits; ++bit) {
    const unsigned source_bit = window * xark_cuda::kWindowBits + bit;
    const unsigned limb = source_bit / 64;
    if (limb < scalar.size() &&
        ((scalar[limb] >> (source_bit % 64)) & 1u) != 0) {
      digit |= static_cast<std::uint16_t>(1u << bit);
    }
  }
  return digit;
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

  const auto scalars = xark_cuda_test::scalars();
  const std::size_t scalar_count = scalars.size();
  const std::size_t total_digits = scalar_count * xark_cuda::kWindowCount;
  std::vector<std::uint64_t> limbs_soa(4 * scalar_count);
  for (std::size_t scalar = 0; scalar < scalar_count; ++scalar) {
    for (std::size_t limb = 0; limb < 4; ++limb) {
      limbs_soa[limb * scalar_count + scalar] = scalars[scalar][limb];
    }
  }

  std::uint64_t* device_limbs = nullptr;
  std::uint16_t* device_digits = nullptr;
  check(cudaMalloc(reinterpret_cast<void**>(&device_limbs),
                   limbs_soa.size() * sizeof(std::uint64_t)),
        "cudaMalloc limbs");
  check(cudaMalloc(reinterpret_cast<void**>(&device_digits),
                   total_digits * sizeof(std::uint16_t)),
        "cudaMalloc digits");
  check(cudaMemcpy(device_limbs, limbs_soa.data(),
                   limbs_soa.size() * sizeof(std::uint64_t),
                   cudaMemcpyHostToDevice),
        "copy limbs to device");

  const unsigned blocks = static_cast<unsigned>(
      (total_digits + kThreads - 1) / kThreads);
  extract_digits<<<blocks, kThreads>>>(device_limbs, device_digits,
                                       scalar_count, total_digits);
  check(cudaGetLastError(), "launch extract_digits");
  check(cudaDeviceSynchronize(), "synchronize extract_digits");

  std::vector<std::uint16_t> digits(total_digits);
  check(cudaMemcpy(digits.data(), device_digits,
                   total_digits * sizeof(std::uint16_t),
                   cudaMemcpyDeviceToHost),
        "copy digits to host");

  for (std::size_t scalar = 0; scalar < scalar_count; ++scalar) {
    for (unsigned window = 0; window < xark_cuda::kWindowCount; ++window) {
      const auto got = digits[window * scalar_count + scalar];
      const auto expected = cpu_digit(scalars[scalar], window);
      if (got != expected) {
        std::fprintf(stderr,
                     "digit mismatch: scalar=%zu window=%u got=%u expected=%u\n",
                     scalar, window, got, expected);
        cudaFree(device_digits);
        cudaFree(device_limbs);
        return 1;
      }
    }
  }

  check(cudaFree(device_digits), "cudaFree digits");
  check(cudaFree(device_limbs), "cudaFree limbs");
  std::printf("passed: %zu scalars x %u windows\n", scalar_count,
              xark_cuda::kWindowCount);
  return 0;
}
