// The quotient's coset transforms over BN254 Fr on CUDA: the OpenCL device's
// fft.cl (radix-2 Stockham passes, natural order in and out) and its host
// sequence in fft.rs.
//
// Elements are 8 Montgomery words (R = 2^256, as arkworks). Twiddles and coset
// factors are tables built by the caller once per domain size and kept on the
// device for the life of the process.

#include <cuda_runtime.h>

#include <cstddef>
#include <cstdint>
#include <map>
#include <mutex>

namespace {

using u32 = std::uint32_t;
using u64 = std::uint64_t;

struct Fr {
  u32 limb[8];
};

__device__ __forceinline__ u32 fr_p(int i) {
  switch (i) {
    case 0: return 0xf0000001u;
    case 1: return 0x43e1f593u;
    case 2: return 0x79b97091u;
    case 3: return 0x2833e848u;
    case 4: return 0x8181585du;
    case 5: return 0xb85045b6u;
    case 6: return 0xe131a029u;
    default: return 0x30644e72u;
  }
}

constexpr u32 kFrInv = 0xefffffffu;  // -r^-1 mod 2^32

// out = a*b + c + carry (low word), carry = high word.
#define XARK_FR_MAC(a, b, c, carry, out) \
  do {                                   \
    u32 lo_ = (a) * (b);                 \
    u32 hi_ = __umulhi((a), (b));        \
    lo_ += (c);                          \
    hi_ += (lo_ < (c));                  \
    lo_ += (carry);                      \
    hi_ += (lo_ < (carry));              \
    (out) = lo_;                         \
    (carry) = hi_;                       \
  } while (0)

// CIOS Montgomery multiplication, R = 2^256, r < 2^254.
__device__ __forceinline__ Fr fr_mul(const Fr &a, const Fr &b) {
  u32 t[10];
#pragma unroll
  for (int i = 0; i < 10; ++i) t[i] = 0;
#pragma unroll
  for (int i = 0; i < 8; ++i) {
    u32 carry = 0;
#pragma unroll
    for (int j = 0; j < 8; ++j) XARK_FR_MAC(a.limb[j], b.limb[i], t[j], carry, t[j]);
    u32 sum = t[8] + carry;
    t[9] = (sum < carry);
    t[8] = sum;
    const u32 m = t[0] * kFrInv;
    // m·r₀ + t₀ is 0 mod 2^32 by the choice of m: only its carry is kept.
    const u32 low = m * fr_p(0) + t[0];
    carry = __umulhi(m, fr_p(0)) + (low < t[0]);
#pragma unroll
    for (int j = 1; j < 8; ++j) XARK_FR_MAC(m, fr_p(j), t[j], carry, t[j - 1]);
    sum = t[8] + carry;
    t[7] = sum;
    t[8] = t[9] + (sum < carry);
  }
  Fr out, reduced;
  u32 borrow = 0;
#pragma unroll
  for (int i = 0; i < 8; ++i) {
    out.limb[i] = t[i];
    const u32 d = t[i] - fr_p(i);
    reduced.limb[i] = d - borrow;
    borrow = (t[i] < fr_p(i)) | (d < borrow);
  }
  return (t[8] != 0 || borrow == 0) ? reduced : out;
}

__device__ __forceinline__ Fr fr_add(const Fr &a, const Fr &b) {
  Fr out, reduced;
  u32 carry = 0, borrow = 0;
#pragma unroll
  for (int i = 0; i < 8; ++i) {
    const u32 s1 = a.limb[i] + b.limb[i];
    const u32 s2 = s1 + carry;
    carry = (s1 < a.limb[i]) | (s2 < s1);
    out.limb[i] = s2;
  }
#pragma unroll
  for (int i = 0; i < 8; ++i) {
    const u32 d = out.limb[i] - fr_p(i);
    reduced.limb[i] = d - borrow;
    borrow = (out.limb[i] < fr_p(i)) | (d < borrow);
  }
  return (carry || !borrow) ? reduced : out;
}

__device__ __forceinline__ Fr fr_sub(const Fr &a, const Fr &b) {
  Fr out, fixed;
  u32 borrow = 0, carry = 0;
#pragma unroll
  for (int i = 0; i < 8; ++i) {
    const u32 d = a.limb[i] - b.limb[i];
    out.limb[i] = d - borrow;
    borrow = (a.limb[i] < b.limb[i]) | (d < borrow);
  }
#pragma unroll
  for (int i = 0; i < 8; ++i) {
    const u32 s1 = out.limb[i] + fr_p(i);
    const u32 s2 = s1 + carry;
    carry = (s1 < out.limb[i]) | (s2 < s1);
    fixed.limb[i] = s2;
  }
  return borrow ? fixed : out;
}

__device__ __forceinline__ Fr load_fr(const u32 *v, const std::size_t i) {
  Fr out;
#pragma unroll
  for (int l = 0; l < 8; ++l) out.limb[l] = v[i * 8 + l];
  return out;
}

__device__ __forceinline__ void store_fr(u32 *v, const std::size_t i, const Fr &x) {
#pragma unroll
  for (int l = 0; l < 8; ++l) v[i * 8 + l] = x.limb[l];
}

// buf[i] *= factors[i].
__global__ void fr_scale(u32 *buf, const u32 *factors, const u32 count) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= count) return;
  store_fr(buf, i, fr_mul(load_fr(buf, i), load_fr(factors, i)));
}

// buf[i] *= factor[0]: the inverse DFT's 1/n, where no coset factor rides along.
__global__ void fr_scale_one(u32 *buf, const u32 *factor, const u32 count) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= count) return;
  store_fr(buf, i, fr_mul(load_fr(buf, i), load_fr(factor, 0)));
}

// One Stockham pass; `p` doubles each pass from 1 to n/2 (= halfn), tw[j] = ω^j.
__global__ void fr_fft_radix2(const u32 *x, u32 *y, const u32 *tw, const u32 p,
                              const u32 halfn) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= halfn) return;
  const u32 k = i & (p - 1u);
  const Fr u0 = load_fr(x, i);
  Fr u1 = load_fr(x, i + halfn);
  if (k != 0) u1 = fr_mul(u1, load_fr(tw, static_cast<std::size_t>(k) * (halfn / p)));
  const u32 j = (i << 1) - k;
  store_fr(y, j, fr_add(u0, u1));
  store_fr(y, j + p, fr_sub(u0, u1));
}

// Natural (n2 rows × n1 columns) → T-layout: out[k1·n2 + k2] = in[k1 + n1·k2].
__global__ void fr_transpose(const u32 *in, u32 *out, const u32 n1, const u32 n2) {
  const u32 o = blockIdx.x * blockDim.x + threadIdx.x;
  if (o >= n1 * n2) return;
  const u32 k1 = o / n2, k2 = o % n2;
  store_fr(out, o, load_fr(in, static_cast<std::size_t>(k1) + static_cast<std::size_t>(n1) * k2));
}

constexpr unsigned kThreads = 256;

unsigned blocks_for(std::size_t items) {
  return static_cast<unsigned>((items + kThreads - 1) / kThreads);
}

struct Tables {
  u32 *forward = nullptr;     // ω^j, j < n/2
  u32 *inverse = nullptr;     // ω^-j, j < n/2
  u32 *to_coset = nullptr;    // (1/n)·g^i, i < n
  u32 *from_coset = nullptr;  // (1/n)·g^-i, i < n
  u32 *n_inv = nullptr;       // 1/n
};

struct State {
  std::mutex mutex;
  std::map<std::size_t, Tables> tables;
  u32 *a = nullptr;
  u32 *b = nullptr;
  std::size_t elements = 0;
};

State &state() {
  static State *s = new State();  // never freed: the driver releases it at exit
  return *s;
}

bool upload(u32 **dst, const u64 *src, std::size_t elements) {
  const std::size_t bytes = elements * 32;
  if (cudaMalloc(dst, bytes) != cudaSuccess) return false;
  return cudaMemcpy(*dst, src, bytes, cudaMemcpyHostToDevice) == cudaSuccess;
}

// log₂ n Stockham passes ping-ponging between `buffers`; returns the index
// holding the result.
int passes(u32 *const buffers[2], int current, const u32 *twiddles, std::size_t n) {
  const u32 half = static_cast<u32>(n / 2);
  for (u32 p = 1; p <= half; p <<= 1) {
    fr_fft_radix2<<<blocks_for(half), kThreads>>>(buffers[current], buffers[1 - current], twiddles,
                                                  p, half);
    current = 1 - current;
  }
  return current;
}

}  // namespace

// Keeps the tables for domain size `n` on the device (each an array of 4-limb
// Montgomery elements: forward and inverse n/2, the coset factors n, n_inv 1).
// Returns 0, 1 for invalid arguments or 4 for a CUDA failure.
extern "C" int xark_cuda_fft_tables(std::size_t n, const std::uint64_t *forward,
                                    const std::uint64_t *inverse, const std::uint64_t *to_coset,
                                    const std::uint64_t *from_coset,
                                    const std::uint64_t *n_inv) noexcept {
  if (n < 2 || (n & (n - 1)) != 0 || n > 0xffffffffu || forward == nullptr ||
      inverse == nullptr || to_coset == nullptr || from_coset == nullptr || n_inv == nullptr) {
    return 1;
  }
  State &s = state();
  std::lock_guard<std::mutex> lock(s.mutex);
  if (s.tables.count(n) != 0) return 0;
  Tables t;
  if (!upload(&t.forward, forward, n / 2) || !upload(&t.inverse, inverse, n / 2) ||
      !upload(&t.to_coset, to_coset, n) || !upload(&t.from_coset, from_coset, n) ||
      !upload(&t.n_inv, n_inv, 1)) {
    return 4;
  }
  s.tables[n] = t;
  return 0;
}

// `data` (n elements of 4 Montgomery limbs, natural order) through one of the
// quotient's transforms, in place: kind 0 evaluations → coset evaluations
// (natural order), 1 coset evaluations → coefficients in T-layout, 2
// evaluations → coefficients in T-layout. `n1 × n2 = n` is the domain's
// four-step shape. Returns 0, 1 for invalid arguments or missing tables, 4 for
// a CUDA failure.
extern "C" int xark_cuda_fft(std::size_t n, std::size_t n1, std::size_t n2, int kind,
                             std::uint64_t *data) noexcept {
  if (n < 2 || (n & (n - 1)) != 0 || n > 0xffffffffu || n1 * n2 != n || data == nullptr ||
      kind < 0 || kind > 2) {
    return 1;
  }
  State &s = state();
  std::lock_guard<std::mutex> lock(s.mutex);
  const auto found = s.tables.find(n);
  if (found == s.tables.end()) return 1;
  const Tables &t = found->second;
  if (s.elements < n) {
    if (s.a != nullptr) cudaFree(s.a);
    if (s.b != nullptr) cudaFree(s.b);
    s.a = s.b = nullptr;
    s.elements = 0;
    if (cudaMalloc(&s.a, n * 32) != cudaSuccess || cudaMalloc(&s.b, n * 32) != cudaSuccess) {
      return 4;
    }
    s.elements = n;
  }
  u32 *const buffers[2] = {s.a, s.b};
  if (cudaMemcpy(buffers[0], data, n * 32, cudaMemcpyHostToDevice) != cudaSuccess) return 4;
  int current = passes(buffers, 0, t.inverse, n);
  const u32 count = static_cast<u32>(n);
  if (kind == 2) {
    fr_scale_one<<<blocks_for(n), kThreads>>>(buffers[current], t.n_inv, count);
  } else {
    fr_scale<<<blocks_for(n), kThreads>>>(buffers[current], kind == 0 ? t.to_coset : t.from_coset,
                                          count);
  }
  if (kind == 0) {
    current = passes(buffers, current, t.forward, n);
  } else if (n1 > 1) {
    fr_transpose<<<blocks_for(n), kThreads>>>(buffers[current], buffers[1 - current],
                                              static_cast<u32>(n1), static_cast<u32>(n2));
    current = 1 - current;
  }
  if (cudaGetLastError() != cudaSuccess) return 4;
  if (cudaMemcpy(data, buffers[current], n * 32, cudaMemcpyDeviceToHost) != cudaSuccess) return 4;
  return 0;
}
