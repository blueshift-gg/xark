#include <cuda_runtime.h>

#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <limits>
#include <vector>

namespace {

constexpr unsigned kWindowBits = 11;
constexpr unsigned kWindowCount = (256 + kWindowBits - 1) / kWindowBits;
constexpr unsigned kThreads = 256;
constexpr std::uint16_t kDigitMask = (1u << kWindowBits) - 1;

__global__ void extract_digits(const std::uint64_t* limbs_soa,
                               std::uint16_t* digits,
                               std::size_t scalar_count,
                               std::size_t total_digits) {
  const std::size_t index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= total_digits) return;

  const unsigned window = static_cast<unsigned>(index / scalar_count);
  const std::size_t scalar = index % scalar_count;
  const unsigned bit = window * kWindowBits;
  const unsigned limb = bit / 64;
  const unsigned shift = bit % 64;

  std::uint64_t value = limbs_soa[limb * scalar_count + scalar] >> shift;
  if (shift != 0 && limb + 1 < 4) {
    value |= limbs_soa[(limb + 1) * scalar_count + scalar] << (64 - shift);
  }
  digits[index] = static_cast<std::uint16_t>(value & kDigitMask);
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
  for (unsigned bit = 0; bit < kWindowBits; ++bit) {
    const unsigned source_bit = window * kWindowBits + bit;
    const unsigned limb = source_bit / 64;
    if (limb < scalar.size() &&
        ((scalar[limb] >> (source_bit % 64)) & 1u) != 0) {
      digit |= static_cast<std::uint16_t>(1u << bit);
    }
  }
  return digit;
}

std::vector<std::array<std::uint64_t, 4>> test_scalars() {
  std::vector<std::array<std::uint64_t, 4>> values = {
      {0, 0, 0, 0},
      {1, 0, 0, 0},
      {std::numeric_limits<std::uint64_t>::max(),
       std::numeric_limits<std::uint64_t>::max(),
       std::numeric_limits<std::uint64_t>::max(),
       std::numeric_limits<std::uint64_t>::max()},
      {0x0123456789abcdefULL, 0xfedcba9876543210ULL,
       0xaaaaaaaa55555555ULL, 0x8000000000000001ULL},
  };
  for (const unsigned bit : {63u, 64u, 127u, 128u, 191u, 192u, 253u, 254u,
                             255u}) {
    std::array<std::uint64_t, 4> scalar{};
    scalar[bit / 64] = std::uint64_t{1} << (bit % 64);
    values.push_back(scalar);
  }

  std::uint64_t state = 0x9e3779b97f4a7c15ULL;
  for (unsigned i = 0; i < 1024; ++i) {
    std::array<std::uint64_t, 4> scalar{};
    for (auto& limb : scalar) {
      state ^= state << 13;
      state ^= state >> 7;
      state ^= state << 17;
      limb = state;
    }
    values.push_back(scalar);
  }
  return values;
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

  const auto scalars = test_scalars();
  const std::size_t scalar_count = scalars.size();
  const std::size_t total_digits = scalar_count * kWindowCount;
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
    for (unsigned window = 0; window < kWindowCount; ++window) {
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
              kWindowCount);
  return 0;
}
