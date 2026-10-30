#include <cuda_runtime.h>

#include <cstdint>
#include <cstdio>
#include <cstdlib>

#include "bn254_g1.cuh"

namespace {

using namespace xark_cuda;

struct G1Output {
  std::uint32_t x[8];
  std::uint32_t y[8];
  std::uint32_t infinity;
};

__global__ void g1_arithmetic_kernel(G1Output* output) {
  if (threadIdx.x != 0 || blockIdx.x != 0) return;

  const std::uint32_t generator_x[8] = {1, 0, 0, 0, 0, 0, 0, 0};
  const std::uint32_t generator_y[8] = {2, 0, 0, 0, 0, 0, 0, 0};
  const std::uint32_t negative_y[8] = {
      0xd87cfd45u, 0x3c208c16u, 0x6871ca8du, 0x97816a91u,
      0x8181585du, 0xb85045b6u, 0xe131a029u, 0x30644e72u};
  const G1Affine generator{from_canonical(generator_x),
                           from_canonical(generator_y), false};
  const G1Affine inverse{from_canonical(generator_x),
                         from_canonical(negative_y), false};

  const G1Affine doubled = g1_to_affine(g1_double(g1_from_affine(generator)));
  const G1Affine added =
      g1_to_affine(g1_add_mixed(g1_from_affine(generator), generator));
  const G1Affine cancelled =
      g1_to_affine(g1_add_mixed(g1_from_affine(generator), inverse));
  const G1Affine results[3] = {doubled, added, cancelled};
  for (unsigned point = 0; point < 3; ++point) {
    const Fq x = to_canonical(results[point].x);
    const Fq y = to_canonical(results[point].y);
    for (unsigned limb = 0; limb < 8; ++limb) {
      output[point].x[limb] = x.limbs[limb];
      output[point].y[limb] = y.limbs[limb];
    }
    output[point].infinity = results[point].infinity ? 1u : 0u;
  }
}

void check_cuda(cudaError_t error, const char* operation) {
  if (error != cudaSuccess) {
    std::fprintf(stderr, "%s: %s\n", operation, cudaGetErrorString(error));
    std::exit(1);
  }
}

bool equal(const std::uint32_t actual[8], const std::uint32_t expected[8]) {
  for (unsigned i = 0; i < 8; ++i) {
    if (actual[i] != expected[i]) return false;
  }
  return true;
}

}  // namespace

int main() {
  G1Output* device_output = nullptr;
  check_cuda(cudaMalloc(&device_output, 3 * sizeof(G1Output)), "cudaMalloc");
  g1_arithmetic_kernel<<<1, 1>>>(device_output);
  check_cuda(cudaGetLastError(), "g1_arithmetic_kernel launch");
  G1Output output[3]{};
  check_cuda(cudaMemcpy(output, device_output, sizeof(output),
                        cudaMemcpyDeviceToHost),
             "copy G1 results");
  check_cuda(cudaFree(device_output), "cudaFree");

  const std::uint32_t doubled_x[8] = {
      0x6d87cfd3u, 0xd3c208c1u, 0x16871ca8u, 0xd97816a9u,
      0x68181585u, 0x9b85045bu, 0x2e131a02u, 0x030644e7u};
  const std::uint32_t doubled_y[8] = {
      0x5a18a2c4u, 0xff3ebf7au, 0xe3538fc7u, 0x68a6a449u,
      0xb2ae9c0au, 0xe7845f96u, 0x0e0a7c92u, 0x15ed738cu};
  for (unsigned point = 0; point < 2; ++point) {
    if (output[point].infinity != 0 || !equal(output[point].x, doubled_x) ||
        !equal(output[point].y, doubled_y)) {
      std::fprintf(stderr, "G1 double/mixed-add result %u mismatch\n", point);
      return 1;
    }
  }
  if (output[2].infinity != 1) {
    std::fprintf(stderr, "G1 point cancellation did not return infinity\n");
    return 1;
  }
  std::puts("passed CUDA BN254 G1 double, mixed add, and cancellation");
  return 0;
}
