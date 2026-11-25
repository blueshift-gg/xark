// Sorted-bucket MSM for BN254 G1: the OpenCL device's pipeline
// (crates/groth16-opencl/kernels/msm_sorted.cl, with the field and curve code of
// msm_pointwise.cl) on CUDA.
//
// Points: 16 Montgomery words per point (x then y) and a flag word (0 = point,
// 1 = infinity). Scalars: 4 little-endian u64 limbs per scalar. Digits are
// signed, `bits` wide, in [-2^(bits-1), 2^(bits-1)); bucket `b` of window `w`
// holds the points whose digit has magnitude `b + 1`, so a window has
// B = 2^(bits-1) buckets. `status` collects bit 1 (invalid point) and bit 2
// (non-canonical scalar); the host declines the MSM when it is non-zero.
//
// Work per stage scales with the input: one thread per point (prepare, digits,
// scatter), per segment of at most `seg_len` points (segment sums), per bucket
// (fold) and per range of `span` buckets (window reduce). The caller combines
// the windows × ranges partial sums.

#include <cuda_runtime.h>

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <limits>
#include <mutex>
#include <vector>

namespace {

using u32 = std::uint32_t;
using u64 = std::uint64_t;

struct Fq {
  u32 limb[8];
};
struct G1Affine {
  Fq x;
  Fq y;
};
struct G1Jacobian {
  Fq x;
  Fq y;
  Fq z;
};

// Constants by value so the unrolled loops fold them into immediates.
__device__ __forceinline__ u32 fq_p(int i) {
  switch (i) {
    case 0: return 0xd87cfd47u;
    case 1: return 0x3c208c16u;
    case 2: return 0x6871ca8du;
    case 3: return 0x97816a91u;
    case 4: return 0x8181585du;
    case 5: return 0xb85045b6u;
    case 6: return 0xe131a029u;
    default: return 0x30644e72u;
  }
}

__device__ __forceinline__ u32 fq_r2(int i) {
  switch (i) {
    case 0: return 0x538afa89u;
    case 1: return 0xf32cfc5bu;
    case 2: return 0xd44501fbu;
    case 3: return 0xb5e71911u;
    case 4: return 0x0a417ff6u;
    case 5: return 0x47ab1effu;
    case 6: return 0xcab8351fu;
    default: return 0x06d89f71u;
  }
}

__device__ __forceinline__ u32 fq_one_word(int i) {
  switch (i) {
    case 0: return 0xc58f0d9du;
    case 1: return 0xd35d438du;
    case 2: return 0xf5c70b3du;
    case 3: return 0x0a78eb28u;
    case 4: return 0x7879462cu;
    case 5: return 0x666ea36fu;
    case 6: return 0x9a07df2fu;
    default: return 0x0e0a77c1u;
  }
}

__device__ __forceinline__ u64 fr_modulus(int i) {
  switch (i) {
    case 0: return 0x43e1f593f0000001ULL;
    case 1: return 0x2833e84879b97091ULL;
    case 2: return 0xb85045b68181585dULL;
    default: return 0x30644e72e131a029ULL;
  }
}

constexpr u32 kFqInv = 0xe4866389u;  // -P^-1 mod 2^32

__device__ __forceinline__ int fq_compare(const Fq &a, const Fq &b) {
#pragma unroll
  for (int i = 7; i >= 0; --i) {
    if (a.limb[i] < b.limb[i]) return -1;
    if (a.limb[i] > b.limb[i]) return 1;
  }
  return 0;
}

// out = a*b + c + carry (low word), carry = high word; never overflows 64 bits.
#define XARK_MAC(a, b, c, carry, out)  \
  do {                                 \
    u32 lo_ = (a) * (b);               \
    u32 hi_ = __umulhi((a), (b));      \
    lo_ += (c);                        \
    hi_ += (lo_ < (c));                \
    lo_ += (carry);                    \
    hi_ += (lo_ < (carry));            \
    (out) = lo_;                       \
    (carry) = hi_;                     \
  } while (0)

// CIOS Montgomery multiplication, R = 2^256, P < 2^255.
__device__ __forceinline__ Fq fq_mul(const Fq &a, const Fq &b) {
  u32 t[10];
#pragma unroll
  for (int i = 0; i < 10; ++i) t[i] = 0;
#pragma unroll
  for (int i = 0; i < 8; ++i) {
    u32 carry = 0;
#pragma unroll
    for (int j = 0; j < 8; ++j) XARK_MAC(a.limb[j], b.limb[i], t[j], carry, t[j]);
    u32 sum = t[8] + carry;
    t[9] = (sum < carry);
    t[8] = sum;
    const u32 m = t[0] * kFqInv;
    // m·p₀ + t₀ is 0 mod 2^32 by the choice of m: only its carry is kept.
    const u32 low = m * fq_p(0) + t[0];
    carry = __umulhi(m, fq_p(0)) + (low < t[0]);
#pragma unroll
    for (int j = 1; j < 8; ++j) XARK_MAC(m, fq_p(j), t[j], carry, t[j - 1]);
    sum = t[8] + carry;
    t[7] = sum;
    t[8] = t[9] + (sum < carry);
  }
  Fq out;
#pragma unroll
  for (int i = 0; i < 8; ++i) out.limb[i] = t[i];
  // t < 2p; subtract p once if needed (t[8] holds any carry past 2^256).
  u32 reduced[8], borrow = 0;
#pragma unroll
  for (int i = 0; i < 8; ++i) {
    const u32 d = out.limb[i] - fq_p(i);
    const u32 d2 = d - borrow;
    borrow = (out.limb[i] < fq_p(i)) | (d < borrow);
    reduced[i] = d2;
  }
  if (t[8] != 0 || borrow == 0) {
#pragma unroll
    for (int i = 0; i < 8; ++i) out.limb[i] = reduced[i];
  }
  return out;
}

__device__ __forceinline__ Fq fq_add(const Fq &a, const Fq &b) {
  Fq out, reduced;
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
    const u32 d = out.limb[i] - fq_p(i);
    reduced.limb[i] = d - borrow;
    borrow = (out.limb[i] < fq_p(i)) | (d < borrow);
  }
  return (carry || !borrow) ? reduced : out;
}

__device__ __forceinline__ Fq fq_sub(const Fq &a, const Fq &b) {
  Fq out, fixed;
  u32 borrow = 0, carry = 0;
#pragma unroll
  for (int i = 0; i < 8; ++i) {
    const u32 d = a.limb[i] - b.limb[i];
    out.limb[i] = d - borrow;
    borrow = (a.limb[i] < b.limb[i]) | (d < borrow);
  }
#pragma unroll
  for (int i = 0; i < 8; ++i) {
    const u32 s1 = out.limb[i] + fq_p(i);
    const u32 s2 = s1 + carry;
    carry = (s1 < out.limb[i]) | (s2 < s1);
    fixed.limb[i] = s2;
  }
  return borrow ? fixed : out;
}

__device__ __forceinline__ Fq fq_zero_value() {
  Fq out;
#pragma unroll
  for (int i = 0; i < 8; ++i) out.limb[i] = 0;
  return out;
}

__device__ __forceinline__ Fq fq_one() {
  Fq out;
#pragma unroll
  for (int i = 0; i < 8; ++i) out.limb[i] = fq_one_word(i);
  return out;
}

__device__ __forceinline__ bool fq_is_zero(const Fq &a) {
  u32 bits = 0;
#pragma unroll
  for (int i = 0; i < 8; ++i) bits |= a.limb[i];
  return bits == 0;
}

__device__ __forceinline__ Fq fq_double(const Fq &a) { return fq_add(a, a); }
__device__ __forceinline__ Fq fq_square(const Fq &a) { return fq_mul(a, a); }

__device__ __forceinline__ Fq fq_from_canonical(const Fq &a) {
  Fq r2;
#pragma unroll
  for (int i = 0; i < 8; ++i) r2.limb[i] = fq_r2(i);
  return fq_mul(a, r2);
}

__device__ __forceinline__ G1Jacobian g1_infinity() {
  G1Jacobian out;
  out.x = fq_zero_value();
  out.y = fq_one();
  out.z = fq_zero_value();
  return out;
}

__device__ __forceinline__ bool g1_is_infinity(const G1Jacobian &p) { return fq_is_zero(p.z); }

__device__ __noinline__ G1Jacobian g1_double(const G1Jacobian &p) {
  if (g1_is_infinity(p) || fq_is_zero(p.y)) return g1_infinity();
  const Fq a = fq_square(p.x), b = fq_square(p.y), c = fq_square(b);
  const Fq d = fq_double(fq_sub(fq_sub(fq_square(fq_add(p.x, b)), a), c));
  const Fq e = fq_add(fq_add(a, a), a), f = fq_square(e);
  const Fq x3 = fq_sub(f, fq_double(d));
  const Fq eight_c = fq_double(fq_double(fq_double(c)));
  const Fq y3 = fq_sub(fq_mul(e, fq_sub(d, x3)), eight_c);
  const Fq z3 = fq_double(fq_mul(p.y, p.z));
  return G1Jacobian{x3, y3, z3};
}

// `right` is never the point at infinity: callers skip those.
__device__ __forceinline__ G1Jacobian g1_add_mixed(const G1Jacobian &left, const G1Affine &right) {
  if (g1_is_infinity(left)) return G1Jacobian{right.x, right.y, fq_one()};
  const Fq z1z1 = fq_square(left.z);
  const Fq u2 = fq_mul(right.x, z1z1);
  const Fq s2 = fq_mul(right.y, fq_mul(left.z, z1z1));
  const Fq h = fq_sub(u2, left.x), hh = fq_square(h);
  const Fq i = fq_double(fq_double(hh)), j = fq_mul(h, i);
  const Fq r = fq_double(fq_sub(s2, left.y)), v = fq_mul(left.x, i);
  if (fq_is_zero(h)) return fq_is_zero(r) ? g1_double(left) : g1_infinity();
  const Fq x3 = fq_sub(fq_sub(fq_square(r), j), fq_double(v));
  const Fq y3 = fq_sub(fq_mul(r, fq_sub(v, x3)), fq_double(fq_mul(left.y, j)));
  const Fq z3 = fq_sub(fq_sub(fq_square(fq_add(left.z, h)), z1z1), hh);
  return G1Jacobian{x3, y3, z3};
}

__device__ __forceinline__ G1Jacobian g1_add_jacobian(const G1Jacobian &left,
                                                      const G1Jacobian &right) {
  if (g1_is_infinity(left)) return right;
  if (g1_is_infinity(right)) return left;
  const Fq z1z1 = fq_square(left.z), z2z2 = fq_square(right.z);
  const Fq u1 = fq_mul(left.x, z2z2), u2 = fq_mul(right.x, z1z1);
  const Fq s1 = fq_mul(left.y, fq_mul(right.z, z2z2));
  const Fq s2 = fq_mul(right.y, fq_mul(left.z, z1z1));
  const Fq h = fq_sub(u2, u1), r0 = fq_sub(s2, s1);
  if (fq_is_zero(h)) return fq_is_zero(r0) ? g1_double(left) : g1_infinity();
  const Fq i = fq_square(fq_double(h)), j = fq_mul(h, i), r = fq_double(r0);
  const Fq v = fq_mul(u1, i);
  const Fq x3 = fq_sub(fq_sub(fq_square(r), j), fq_double(v));
  const Fq y3 = fq_sub(fq_mul(r, fq_sub(v, x3)), fq_double(fq_mul(s1, j)));
  const Fq z3 = fq_mul(fq_sub(fq_sub(fq_square(fq_add(left.z, right.z)), z1z1), z2z2), h);
  return G1Jacobian{x3, y3, z3};
}

__device__ __forceinline__ void store_bucket_point(u32 *output, const std::size_t slot,
                                                   const G1Jacobian &point) {
  const std::size_t base = slot * 24;
#pragma unroll
  for (int l = 0; l < 8; ++l) {
    output[base + l] = point.x.limb[l];
    output[base + 8 + l] = point.y.limb[l];
    output[base + 16 + l] = point.z.limb[l];
  }
}

__device__ __forceinline__ G1Jacobian load_bucket_point(const u32 *input, const std::size_t slot) {
  const std::size_t base = slot * 24;
  G1Jacobian point;
#pragma unroll
  for (int l = 0; l < 8; ++l) {
    point.x.limb[l] = input[base + l];
    point.y.limb[l] = input[base + 8 + l];
    point.z.limb[l] = input[base + 16 + l];
  }
  return point;
}

// Uncompressed arkworks encoding: x then y, canonical little-endian; the top
// two bits of y carry the flags (bit 6 of the last byte = infinity).
__global__ void msm_prepare_uncompressed(const u32 *raw, const u32 count, u32 *points,
                                         u32 *flags, u32 *status) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= count) return;
  const std::size_t base = static_cast<std::size_t>(i) * 16;
  Fq x, y, p;
#pragma unroll
  for (int l = 0; l < 8; ++l) {
    x.limb[l] = raw[base + l];
    y.limb[l] = raw[base + 8 + l];
    p.limb[l] = fq_p(l);
  }
  const u32 infinity = (y.limb[7] >> 30) & 1u;
  y.limb[7] &= 0x3fffffffu;
  u32 any = 0;
#pragma unroll
  for (int l = 0; l < 8; ++l) any |= x.limb[l] | y.limb[l];
  if (infinity) {
    flags[i] = 1;
    if (any) atomicOr(status, 1u);
    return;
  }
  flags[i] = 0;
  if (fq_compare(x, p) >= 0 || fq_compare(y, p) >= 0) {
    atomicOr(status, 1u);
    return;
  }
  const Fq xm = fq_from_canonical(x), ym = fq_from_canonical(y);
  const Fq three = fq_add(fq_add(fq_one(), fq_one()), fq_one());
  if (fq_compare(fq_square(ym), fq_add(fq_mul(fq_square(xm), xm), three)) != 0) {
    atomicOr(status, 1u);
    return;
  }
#pragma unroll
  for (int l = 0; l < 8; ++l) {
    points[base + l] = xm.limb[l];
    points[base + 8 + l] = ym.limb[l];
  }
}

__global__ void msm_signed_digits(const u64 *scalars, const u32 count, const u32 bits,
                                  const u32 windows, const u32 *flags, short *digits,
                                  u32 *counts, u32 *status) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= count) return;
  u64 s[4];
#pragma unroll
  for (int l = 0; l < 4; ++l) s[l] = scalars[static_cast<std::size_t>(i) * 4 + l];
  int canonical = 0;
#pragma unroll
  for (int l = 3; l >= 0; --l) {
    if (s[l] < fr_modulus(l)) {
      canonical = 1;
      break;
    }
    if (s[l] > fr_modulus(l)) break;
  }
  if (!canonical) atomicOr(status, 2u);
  const int skip = !canonical || flags[i] != 0;
  const u32 buckets = 1u << (bits - 1);
  const int full = 1 << bits;
  const u64 mask = (1ULL << bits) - 1ULL;
  int carry = 0;
  for (u32 w = 0; w < windows; ++w) {
    const u32 bit = w * bits, limb = bit / 64u, shift = bit % 64u;
    u64 v = limb < 4u ? s[limb] >> shift : 0ULL;
    if (shift + bits > 64u && limb + 1u < 4u) v |= s[limb + 1u] << (64u - shift);
    int d = static_cast<int>(v & mask) + carry;
    carry = d >= static_cast<int>(buckets);
    if (carry) d -= full;
    if (skip) d = 0;
    digits[static_cast<std::size_t>(w) * count + i] = static_cast<short>(d);
    if (d != 0) atomicAdd(&counts[static_cast<std::size_t>(w) * buckets + static_cast<u32>(abs(d)) - 1u], 1u);
  }
}

// `cursor` starts as each bucket's offset into `order` and ends as its end.
// The top bit of an `order` entry marks a negated point.
__global__ void msm_scatter(const short *digits, const u32 count, const u32 bits,
                            const u32 windows, u32 *cursor, u32 *order) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= count) return;
  const u32 buckets = 1u << (bits - 1);
  for (u32 w = 0; w < windows; ++w) {
    const int d = digits[static_cast<std::size_t>(w) * count + i];
    if (d == 0) continue;
    const u32 pos = atomicAdd(&cursor[static_cast<std::size_t>(w) * buckets + static_cast<u32>(abs(d)) - 1u], 1u);
    order[pos] = i | (d < 0 ? 0x80000000u : 0u);
  }
}

// `segments` holds (lo, hi, slot) per segment, longest first: the threads of a
// warp run in lockstep, so neighbours of equal length waste no lanes.
__global__ void msm_segment_sums(const u32 *points, const u32 *order, const u32 *segments,
                                 const u32 segment_count, u32 *partials) {
  const u32 t = blockIdx.x * blockDim.x + threadIdx.x;
  if (t >= segment_count) return;
  const u32 lo = segments[3 * t], hi = segments[3 * t + 1], segment = segments[3 * t + 2];
  const Fq zero = fq_zero_value();
  G1Jacobian sum = g1_infinity();
  for (u32 i = lo; i < hi; ++i) {
    const u32 entry = order[i];
    const std::size_t base = static_cast<std::size_t>(entry & 0x7fffffffu) * 16;
    G1Affine point;
#pragma unroll
    for (int l = 0; l < 8; ++l) {
      point.x.limb[l] = points[base + l];
      point.y.limb[l] = points[base + 8 + l];
    }
    if (entry >> 31) point.y = fq_sub(zero, point.y);
    sum = g1_add_mixed(sum, point);
  }
  store_bucket_point(partials, segment, sum);
}

__global__ void msm_bucket_fold(const u32 *partials, const u32 *bucket_segments,
                                const u32 bucket_count, u32 *buckets) {
  const u32 k = blockIdx.x * blockDim.x + threadIdx.x;
  if (k >= bucket_count) return;
  G1Jacobian sum = g1_infinity();
  for (u32 s = bucket_segments[k]; s < bucket_segments[k + 1]; ++s) {
    sum = g1_add_jacobian(sum, load_bucket_point(partials, s));
  }
  store_bucket_point(buckets, k, sum);
}

// One thread per `span` buckets of a window: Σ (b + 1)·bucket_b over its range,
// as the running-sum trick plus `lo`·(range sum).
__global__ void msm_window_reduce(const u32 *buckets, const u32 bucket_count, const u32 span,
                                  const u32 ranges, const u32 windows, u32 *out) {
  const u32 t = blockIdx.x * blockDim.x + threadIdx.x;
  if (t >= windows * ranges) return;
  const u32 w = t / ranges, r = t % ranges;
  const u32 lo = r * span, hi = min(lo + span, bucket_count);
  const std::size_t base = static_cast<std::size_t>(w) * bucket_count;
  G1Jacobian running = g1_infinity(), weighted = g1_infinity();
  for (int b = static_cast<int>(hi) - 1; b >= static_cast<int>(lo); --b) {
    running = g1_add_jacobian(running, load_bucket_point(buckets, base + static_cast<u32>(b)));
    weighted = g1_add_jacobian(weighted, running);
  }
  G1Jacobian scaled = g1_infinity();
  for (int bit = 20; bit >= 0; --bit) {
    scaled = g1_double(scaled);
    if ((lo >> bit) & 1u) scaled = g1_add_jacobian(scaled, running);
  }
  store_bucket_point(out, t, g1_add_jacobian(weighted, scaled));
}

// ---- host side ------------------------------------------------------------

constexpr unsigned kThreads = 256;

unsigned blocks_for(std::size_t items) {
  return static_cast<unsigned>((items + kThreads - 1) / kThreads);
}

// Device buffers kept from call to call (like the OpenCL device's pool), grown
// when a larger MSM needs more.
struct Buffer {
  void *ptr = nullptr;
  std::size_t bytes = 0;

  bool ensure(std::size_t need) {
    if (need == 0) need = 1;
    if (need <= bytes) return true;
    if (ptr != nullptr) cudaFree(ptr);
    ptr = nullptr;
    bytes = 0;
    if (cudaMalloc(&ptr, need) != cudaSuccess) return false;
    bytes = need;
    return true;
  }
  template <typename T> T *as() const { return static_cast<T *>(ptr); }
};

struct Pool {
  std::mutex mutex;
  Buffer raw, points, flags, scalars, digits, counts, cursor, order, segments, partials,
      fold[2], fold_bounds, bucket_segments, bucket_points, out, status;
};

Pool &pool() {
  static Pool *p = new Pool();  // never freed: the driver releases it at exit
  return *p;
}

struct Profile {
  bool on = std::getenv("XARK_CUDA_PROFILE") != nullptr;
  std::chrono::steady_clock::time_point start = std::chrono::steady_clock::now(), lap = start;
  void mark(const char *stage) {
    if (!on) return;
    cudaDeviceSynchronize();
    const auto now = std::chrono::steady_clock::now();
    std::fprintf(stderr, "  cuda %s: %.2f ms\n", stage,
                 std::chrono::duration<double, std::milli>(now - lap).count());
    lap = now;
  }
};

#define XARK_TRY(expr)                    \
  do {                                    \
    if ((expr) != cudaSuccess) return 4;  \
  } while (0)
#define XARK_LAUNCHED() XARK_TRY(cudaGetLastError())

// Page-locked host buffers the Rust side fills directly, so uploads run at the
// bus's speed instead of through the driver's pageable staging (the OpenCL
// device's mapped buffers). Slot 0: points, 1: scalar limbs, 2: FFT data,
// 3: infinity flags.
struct Pinned {
  void *ptr = nullptr;
  std::size_t bytes = 0;
};
std::mutex pinned_mutex;
Pinned pinned_slots[4];

}  // namespace

// The first CUDA device's name into `name` (NUL-terminated), creating its
// context. Returns 0 on success, 2 without a CUDA device.
extern "C" int xark_cuda_device(char *name, std::size_t len) noexcept {
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count == 0) return 2;
  if (cudaSetDevice(0) != cudaSuccess || cudaFree(nullptr) != cudaSuccess) return 2;
  cudaDeviceProp prop{};
  if (cudaGetDeviceProperties(&prop, 0) != cudaSuccess) return 2;
  if (name != nullptr && len > 0) {
    std::size_t i = 0;
    for (; i + 1 < len && prop.name[i] != '\0'; ++i) name[i] = prop.name[i];
    name[i] = '\0';
  }
  return 0;
}

// A page-locked host buffer of at least `bytes` for `slot`, kept and grown from
// call to call; null if it can't be allocated. Its contents survive until the
// slot grows.
extern "C" void *xark_cuda_pinned(unsigned slot, std::size_t bytes) noexcept {
  if (slot >= 4) return nullptr;
  std::lock_guard<std::mutex> lock(pinned_mutex);
  Pinned &p = pinned_slots[slot];
  if (bytes == 0) bytes = 1;
  if (bytes <= p.bytes) return p.ptr;
  if (p.ptr != nullptr) cudaFreeHost(p.ptr);
  p.ptr = nullptr;
  p.bytes = 0;
  if (cudaMallocHost(&p.ptr, bytes) != cudaSuccess) {
    p.ptr = nullptr;
    return nullptr;
  }
  p.bytes = bytes;
  return p.ptr;
}

// Allocates the device buffers an MSM of `count` points with `bits`-bit digits
// needs, so the proof's first MSM doesn't pay for them. Returns 0 or 4.
extern "C" int xark_cuda_msm_reserve(std::size_t count, unsigned bits, unsigned seg_len,
                                     unsigned span) noexcept {
  if (count == 0 || bits < 2 || bits > 16 || seg_len == 0 || span == 0) return 1;
  const std::size_t windows = (256 + bits - 1) / bits;
  const std::size_t buckets = std::size_t{1} << (bits - 1);
  const std::size_t bucket_total = windows * buckets;
  const std::size_t reduced = windows * ((buckets + span - 1) / span);
  const std::size_t entries = windows * count;
  const std::size_t segments = bucket_total + entries / seg_len + 1;
  Pool &p = pool();
  std::lock_guard<std::mutex> lock(p.mutex);
  const bool ok = p.status.ensure(sizeof(u32)) && p.raw.ensure(count * 64) &&
                  p.points.ensure(count * 16 * sizeof(u32)) &&
                  p.flags.ensure(count * sizeof(u32)) &&
                  p.scalars.ensure(count * 4 * sizeof(u64)) &&
                  p.digits.ensure(entries * sizeof(short)) &&
                  p.counts.ensure(bucket_total * sizeof(u32)) &&
                  p.cursor.ensure(bucket_total * sizeof(u32)) &&
                  p.bucket_points.ensure(bucket_total * 24 * sizeof(u32)) &&
                  p.out.ensure(reduced * 24 * sizeof(u32)) &&
                  p.order.ensure(entries * sizeof(u32)) &&
                  p.segments.ensure(segments * 3 * sizeof(u32)) &&
                  p.partials.ensure(segments * 24 * sizeof(u32));
  return ok ? 0 : 4;
}

// Returns 0 on success, 1 for invalid arguments, 2 without a CUDA device, 3 for
// an invalid point or non-canonical scalar, 4 for an allocation or CUDA failure.
//
// mode 0: `points` is `count` uncompressed arkworks points (64 bytes each),
//         checked and converted on the device; `flags` is unused.
// mode 1: `points` is `count` × 16 Montgomery words (x then y), already
//         checked by the caller, and `flags[i]` = 1 marks the point at infinity.
// `out` receives windows × ceil(2^(bits-1) / span) Jacobian points (24 words,
// Montgomery), window-major: the caller sums each window's ranges and combines
// the windows by doubling.
extern "C" int xark_cuda_sorted_msm_g1(const void *points, const std::uint32_t *flags,
                                       int mode, const std::uint64_t *scalars,
                                       std::size_t count, unsigned bits, unsigned seg_len,
                                       unsigned span, std::uint32_t *out,
                                       std::size_t out_words) noexcept {
  if (count == 0 || count >= 0x80000000u || points == nullptr || scalars == nullptr ||
      out == nullptr || bits < 2 || bits > 16 || seg_len == 0 || span == 0 ||
      (mode == 1 && flags == nullptr) || (mode != 0 && mode != 1)) {
    return 1;
  }
  const std::size_t windows = (256 + bits - 1) / bits;
  const std::size_t buckets = std::size_t{1} << (bits - 1);
  const std::size_t bucket_total = windows * buckets;
  const std::size_t ranges = (buckets + span - 1) / span;
  const std::size_t reduced = windows * ranges;
  if (out_words != reduced * 24 || windows * count > 0xffffffffu) return 1;

  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count == 0) return 2;
  if (cudaSetDevice(0) != cudaSuccess) return 2;

  Pool &p = pool();
  std::lock_guard<std::mutex> lock(p.mutex);
  Profile profile;
  const u32 n = static_cast<u32>(count);

  if (!p.status.ensure(sizeof(u32)) || !p.points.ensure(count * 16 * sizeof(u32)) ||
      !p.flags.ensure(count * sizeof(u32)) || !p.scalars.ensure(count * 4 * sizeof(u64)) ||
      !p.digits.ensure(windows * count * sizeof(short)) ||
      !p.counts.ensure(bucket_total * sizeof(u32)) || !p.cursor.ensure(bucket_total * sizeof(u32)) ||
      !p.bucket_points.ensure(bucket_total * 24 * sizeof(u32)) ||
      !p.out.ensure(reduced * 24 * sizeof(u32))) {
    return 4;
  }
  XARK_TRY(cudaMemset(p.status.ptr, 0, sizeof(u32)));
  XARK_TRY(cudaMemcpy(p.scalars.ptr, scalars, count * 4 * sizeof(u64), cudaMemcpyHostToDevice));
  if (mode == 0) {
    if (!p.raw.ensure(count * 64)) return 4;
    XARK_TRY(cudaMemcpy(p.raw.ptr, points, count * 64, cudaMemcpyHostToDevice));
    msm_prepare_uncompressed<<<blocks_for(count), kThreads>>>(
        p.raw.as<u32>(), n, p.points.as<u32>(), p.flags.as<u32>(), p.status.as<u32>());
    XARK_LAUNCHED();
  } else {
    XARK_TRY(cudaMemcpy(p.points.ptr, points, count * 16 * sizeof(u32), cudaMemcpyHostToDevice));
    XARK_TRY(cudaMemcpy(p.flags.ptr, flags, count * sizeof(u32), cudaMemcpyHostToDevice));
  }
  profile.mark("upload+prepare");

  XARK_TRY(cudaMemset(p.counts.ptr, 0, bucket_total * sizeof(u32)));
  msm_signed_digits<<<blocks_for(count), kThreads>>>(
      p.scalars.as<u64>(), n, bits, static_cast<u32>(windows), p.flags.as<u32>(),
      p.digits.as<short>(), p.counts.as<u32>(), p.status.as<u32>());
  XARK_LAUNCHED();
  u32 status = 0;
  XARK_TRY(cudaMemcpy(&status, p.status.ptr, sizeof(u32), cudaMemcpyDeviceToHost));
  if (status != 0) return 3;
  profile.mark("digits");

  // Host scan of the histogram: bucket starts, and each bucket cut into
  // segments of at most `seg_len` entries.
  std::vector<u32> bucket_counts(bucket_total);
  XARK_TRY(cudaMemcpy(bucket_counts.data(), p.counts.ptr, bucket_total * sizeof(u32),
                      cudaMemcpyDeviceToHost));
  std::vector<u32> starts(bucket_total), bounds, bucket_segments;
  bounds.reserve(bucket_total + windows * count / seg_len + 1);
  bucket_segments.reserve(bucket_total + 1);
  u64 total = 0;
  for (std::size_t b = 0; b < bucket_total; ++b) {
    starts[b] = static_cast<u32>(total);
    bucket_segments.push_back(static_cast<u32>(bounds.size()));
    const u64 hi = total + bucket_counts[b];
    for (u64 lo = total; lo < hi; lo = (lo + seg_len < hi) ? lo + seg_len : hi) {
      bounds.push_back(static_cast<u32>(lo));
    }
    total = hi;
  }
  if (total == 0) {
    for (std::size_t i = 0; i < out_words; ++i) out[i] = 0;  // z = 0: infinity
    return 0;
  }
  const std::size_t segment_count = bounds.size();
  bucket_segments.push_back(static_cast<u32>(segment_count));
  bounds.push_back(static_cast<u32>(total));
  // Longest segments first (a counting sort by length), so a warp's threads sum
  // segments of about the same length.
  std::vector<u32> by_length(seg_len + 2, 0);
  for (std::size_t k = 0; k < segment_count; ++k) {
    ++by_length[seg_len - (bounds[k + 1] - bounds[k]) + 1];
  }
  for (std::size_t l = 1; l < by_length.size(); ++l) by_length[l] += by_length[l - 1];
  std::vector<u32> segments(segment_count * 3);
  for (std::size_t k = 0; k < segment_count; ++k) {
    u32 &at = by_length[seg_len - (bounds[k + 1] - bounds[k])];
    segments[3 * at] = bounds[k];
    segments[3 * at + 1] = bounds[k + 1];
    segments[3 * at + 2] = static_cast<u32>(k);
    ++at;
  }
  if (!p.segments.ensure(segments.size() * sizeof(u32)) ||
      !p.order.ensure(static_cast<std::size_t>(total) * sizeof(u32)) ||
      !p.partials.ensure(segment_count * 24 * sizeof(u32))) {
    return 4;
  }
  XARK_TRY(cudaMemcpy(p.segments.ptr, segments.data(), segments.size() * sizeof(u32),
                      cudaMemcpyHostToDevice));
  XARK_TRY(cudaMemcpy(p.cursor.ptr, starts.data(), bucket_total * sizeof(u32),
                      cudaMemcpyHostToDevice));
  profile.mark("host scan+upload");

  msm_scatter<<<blocks_for(count), kThreads>>>(p.digits.as<short>(), n, bits,
                                               static_cast<u32>(windows), p.cursor.as<u32>(),
                                               p.order.as<u32>());
  XARK_LAUNCHED();
  profile.mark("scatter");
  msm_segment_sums<<<blocks_for(segment_count), kThreads>>>(
      p.points.as<u32>(), p.order.as<u32>(), p.segments.as<u32>(),
      static_cast<u32>(segment_count), p.partials.as<u32>());
  XARK_LAUNCHED();
  profile.mark("segment sums");

  // Heavy buckets (a sparse witness puts most points in a few) fold in rounds
  // of at most `group` partials, so no thread runs a long serial chain; the last
  // round leaves each bucket ≤ `group` partials.
  constexpr u32 group = 16;
  const u32 *level = p.partials.as<u32>();
  int flip = 0;
  std::vector<u32> per_bucket = std::move(bucket_segments);
  for (;;) {
    bool heavy = false;
    for (std::size_t k = 0; k + 1 < per_bucket.size(); ++k) {
      if (per_bucket[k + 1] - per_bucket[k] > group) {
        heavy = true;
        break;
      }
    }
    if (!heavy) break;
    std::vector<u32> fold_bounds, next;
    next.reserve(per_bucket.size());
    for (std::size_t k = 0; k + 1 < per_bucket.size(); ++k) {
      next.push_back(static_cast<u32>(fold_bounds.size()));
      for (u32 lo = per_bucket[k]; lo < per_bucket[k + 1];
           lo = (lo + group < per_bucket[k + 1]) ? lo + group : per_bucket[k + 1]) {
        fold_bounds.push_back(lo);
      }
    }
    const u32 groups = static_cast<u32>(fold_bounds.size());
    next.push_back(groups);
    fold_bounds.push_back(per_bucket.back());
    Buffer &dst = p.fold[flip];
    if (!p.fold_bounds.ensure(fold_bounds.size() * sizeof(u32)) ||
        !dst.ensure(static_cast<std::size_t>(groups) * 24 * sizeof(u32))) {
      return 4;
    }
    XARK_TRY(cudaMemcpy(p.fold_bounds.ptr, fold_bounds.data(), fold_bounds.size() * sizeof(u32),
                        cudaMemcpyHostToDevice));
    msm_bucket_fold<<<blocks_for(groups), kThreads>>>(level, p.fold_bounds.as<u32>(), groups,
                                                      dst.as<u32>());
    XARK_LAUNCHED();
    level = dst.as<u32>();
    flip ^= 1;
    per_bucket = std::move(next);
  }
  if (!p.bucket_segments.ensure(per_bucket.size() * sizeof(u32))) return 4;
  XARK_TRY(cudaMemcpy(p.bucket_segments.ptr, per_bucket.data(), per_bucket.size() * sizeof(u32),
                      cudaMemcpyHostToDevice));
  msm_bucket_fold<<<blocks_for(bucket_total), kThreads>>>(
      level, p.bucket_segments.as<u32>(), static_cast<u32>(bucket_total),
      p.bucket_points.as<u32>());
  XARK_LAUNCHED();
  profile.mark("bucket fold");

  msm_window_reduce<<<blocks_for(reduced), kThreads>>>(
      p.bucket_points.as<u32>(), static_cast<u32>(buckets), span, static_cast<u32>(ranges),
      static_cast<u32>(windows), p.out.as<u32>());
  XARK_LAUNCHED();
  XARK_TRY(cudaMemcpy(out, p.out.ptr, reduced * 24 * sizeof(u32), cudaMemcpyDeviceToHost));
  profile.mark("window reduce");
  if (profile.on) {
    std::fprintf(stderr, "  cuda chunk: %zu points, c=%u, %llu entries, %zu segments, %.2f ms\n",
                 count, bits, static_cast<unsigned long long>(total), segment_count,
                 std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() -
                                                            profile.start)
                     .count());
  }
  return 0;
}
