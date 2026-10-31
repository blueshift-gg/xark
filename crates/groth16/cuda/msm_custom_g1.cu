#include <cuda_runtime.h>

#include <cstddef>
#include <cstdint>
#include <limits>
#include <new>

#include "msm_accumulate.cuh"
#include "msm_buckets.cuh"
#include "msm_digits.cuh"
#include "msm_plan.hpp"

namespace {

using namespace xark_cuda;
constexpr unsigned kThreads = 256;
constexpr std::size_t kPointWords = 17;

__global__ void extract_digits(const std::uint64_t *limbs_soa,
                               std::uint16_t *digits,
                               std::size_t scalar_count,
                               std::size_t total_digits) {
  const std::size_t index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= total_digits) return;
  const unsigned window = static_cast<unsigned>(index / scalar_count);
  const std::size_t scalar = index % scalar_count;
  digits[index] = xark_cuda::extract_digit(limbs_soa, scalar_count, scalar, window);
}

__global__ void count_buckets(const std::uint16_t *digits, unsigned *counts,
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

__global__ void prefix_buckets(const unsigned *counts, unsigned *offsets,
                               unsigned *cursors) {
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

__global__ void scatter_indices(const std::uint16_t *digits, unsigned *cursors,
                                unsigned *indices,
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

__global__ void accumulate_buckets(const G1Affine *points,
                                   const unsigned *offsets,
                                   const unsigned *indices,
                                   G1Jacobian *bucket_sums,
                                   std::size_t scalar_count,
                                   std::size_t total_buckets) {
  const std::size_t index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index >= total_buckets) return;
  const unsigned window =
      static_cast<unsigned>(index / xark_cuda::kBucketCount);
  const unsigned bucket =
      static_cast<unsigned>(index % xark_cuda::kBucketCount);
  const std::size_t offset_base = window * (xark_cuda::kBucketCount + 1);
  const std::size_t index_base = window * scalar_count;
  bucket_sums[index] = xark_cuda::g1_accumulate_bucket(
      points, indices + index_base, offsets[offset_base + bucket],
      offsets[offset_base + bucket + 1]);
}

__global__ void reduce_windows(const G1Jacobian *bucket_sums,
                               G1Jacobian *window_sums) {
  const unsigned window = blockIdx.x * blockDim.x + threadIdx.x;
  if (window >= xark_cuda::kWindowCount) return;
  window_sums[window] = xark_cuda::g1_reduce_buckets(
      bucket_sums + window * xark_cuda::kBucketCount,
      xark_cuda::kBucketCount);
}

__global__ void combine_windows(const G1Jacobian *window_sums,
                                G1Affine *result) {
  if (blockIdx.x != 0 || threadIdx.x != 0) return;
  const G1Jacobian sum = xark_cuda::g1_combine_windows(
      window_sums, xark_cuda::kWindowCount, xark_cuda::kWindowBits);
  *result = xark_cuda::g1_to_affine(sum);
}

template <typename T> class DeviceBuffer {
 public:
  DeviceBuffer() = default;
  DeviceBuffer(const DeviceBuffer &) = delete;
  DeviceBuffer &operator=(const DeviceBuffer &) = delete;
  ~DeviceBuffer() {
    if (data_ != nullptr) cudaFree(data_);
  }

  bool allocate(std::size_t count) {
    if (count == 0) return true;
    if (count > std::numeric_limits<std::size_t>::max() / sizeof(T)) {
      return false;
    }
    return cudaMalloc(reinterpret_cast<void **>(&data_), count * sizeof(T)) ==
           cudaSuccess;
  }

  T *get() const { return data_; }

 private:
  T *data_ = nullptr;
};

bool valid_points(const std::uint32_t *words, std::size_t count,
                  G1Affine *points) {
  for (std::size_t point = 0; point < count; ++point) {
    const std::uint32_t *entry = words + point * kPointWords;
    if (entry[16] > 1 ||
        !xark_cuda::g1_from_canonical_checked(entry, entry + 8, entry[16] != 0,
                                               &points[point])) {
      return false;
    }
  }
  return true;
}

bool launch_pipeline(const MsmPlan &plan, const G1Affine *host_points,
                     const std::uint64_t *host_scalars,
                     std::uint32_t scalar_count,
                     std::uint32_t *result_words) {
  DeviceBuffer<G1Affine> points;
  DeviceBuffer<std::uint64_t> scalars;
  DeviceBuffer<std::uint16_t> digits;
  DeviceBuffer<unsigned> counts;
  DeviceBuffer<unsigned> offsets;
  DeviceBuffer<unsigned> cursors;
  DeviceBuffer<unsigned> indices;
  DeviceBuffer<G1Jacobian> bucket_sums;
  DeviceBuffer<G1Jacobian> window_sums;
  DeviceBuffer<G1Affine> result;

  if (!points.allocate(scalar_count) ||
      !scalars.allocate(static_cast<std::size_t>(scalar_count) * 4) ||
      !digits.allocate(plan.total_digits) ||
      !counts.allocate(plan.bucket_count) ||
      !offsets.allocate(plan.offset_count) ||
      !cursors.allocate(plan.bucket_count) ||
      !indices.allocate(plan.total_digits) ||
      !bucket_sums.allocate(plan.bucket_count) ||
      !window_sums.allocate(kWindowCount) || !result.allocate(1)) {
    return false;
  }

  if (cudaMemcpy(points.get(), host_points,
                 static_cast<std::size_t>(scalar_count) * sizeof(G1Affine),
                 cudaMemcpyHostToDevice) != cudaSuccess ||
      cudaMemcpy(scalars.get(), host_scalars,
                 static_cast<std::size_t>(scalar_count) * 4 * sizeof(std::uint64_t),
                 cudaMemcpyHostToDevice) != cudaSuccess ||
      cudaMemset(counts.get(), 0, plan.bucket_count * sizeof(unsigned)) !=
          cudaSuccess) {
    return false;
  }

  extract_digits<<<plan.digit_blocks, kThreads>>>(
      scalars.get(), digits.get(), scalar_count, plan.total_digits);
  if (cudaGetLastError() != cudaSuccess) return false;
  count_buckets<<<plan.digit_blocks, kThreads>>>(
      digits.get(), counts.get(), scalar_count, plan.total_digits);
  if (cudaGetLastError() != cudaSuccess) return false;
  prefix_buckets<<<(kWindowCount + 127) / 128, 128>>>(
      counts.get(), offsets.get(), cursors.get());
  if (cudaGetLastError() != cudaSuccess) return false;
  scatter_indices<<<plan.digit_blocks, kThreads>>>(
      digits.get(), cursors.get(), indices.get(), scalar_count,
      plan.total_digits);
  if (cudaGetLastError() != cudaSuccess) return false;
  accumulate_buckets<<<plan.bucket_blocks, kThreads>>>(
      points.get(), offsets.get(), indices.get(), bucket_sums.get(),
      scalar_count, plan.bucket_count);
  if (cudaGetLastError() != cudaSuccess) return false;
  reduce_windows<<<1, kWindowCount>>>(bucket_sums.get(), window_sums.get());
  if (cudaGetLastError() != cudaSuccess) return false;
  combine_windows<<<1, 1>>>(window_sums.get(), result.get());
  if (cudaGetLastError() != cudaSuccess) return false;

  G1Affine host_result{};
  if (cudaMemcpy(&host_result, result.get(), sizeof(host_result),
                 cudaMemcpyDeviceToHost) != cudaSuccess) {
    return false;
  }

  if (host_result.infinity) {
    for (unsigned i = 0; i < 16; ++i) result_words[i] = 0;
    result_words[16] = 1;
    return true;
  }
  const Fq x = xark_cuda::to_canonical(host_result.x);
  const Fq y = xark_cuda::to_canonical(host_result.y);
  for (unsigned i = 0; i < 8; ++i) {
    result_words[i] = x.limbs[i];
    result_words[8 + i] = y.limbs[i];
  }
  result_words[16] = 0;
  return true;
}

} // namespace

// Returns 0 on success, 1 for invalid host input, 2 without a CUDA device,
// 3 for invalid curve/scalar data, and 4 for an allocation or CUDA failure.
extern "C" bool xark_cuda_device_available() noexcept {
  int device_count = 0;
  return cudaGetDeviceCount(&device_count) == cudaSuccess && device_count > 0 &&
         cudaSetDevice(0) == cudaSuccess;
}

extern "C" int xark_cuda_msm_g1(const std::uint32_t *point_words,
                                const std::uint64_t *scalar_limbs_soa,
                                std::size_t scalar_count,
                                std::uint32_t *result_words) noexcept {
  if (result_words == nullptr ||
      scalar_count > std::numeric_limits<std::uint32_t>::max() ||
      scalar_count > std::numeric_limits<std::size_t>::max() / kPointWords ||
      scalar_count >
          std::numeric_limits<std::size_t>::max() / sizeof(G1Affine) ||
      (scalar_count != 0 &&
       (point_words == nullptr || scalar_limbs_soa == nullptr))) {
    return 1;
  }
  for (unsigned i = 0; i < 17; ++i) result_words[i] = 0;
  if (scalar_count == 0) {
    result_words[16] = 1;
    return 0;
  }

  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count == 0) {
    return 2;
  }
  if (cudaSetDevice(0) != cudaSuccess) return 2;
  if (!xark_cuda::are_canonical_scalars_soa(scalar_limbs_soa, scalar_count)) {
    return 3;
  }
  const xark_cuda::MsmPlan plan = xark_cuda::make_msm_plan(scalar_count, kThreads);
  if (!plan.valid()) return 1;

  G1Affine *host_points = new (std::nothrow) G1Affine[scalar_count];
  if (host_points == nullptr) return 4;
  const bool points_ok = valid_points(point_words, scalar_count, host_points);
  if (!points_ok) {
    delete[] host_points;
    return 3;
  }
  const bool succeeded =
      launch_pipeline(plan, host_points, scalar_limbs_soa,
                      static_cast<std::uint32_t>(scalar_count), result_words);
  delete[] host_points;
  return succeeded ? 0 : 4;
}
