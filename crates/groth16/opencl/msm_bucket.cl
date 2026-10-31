// Four-bit Pippenger-style bucket accumulation for BN254 G1.
//
// Each work item owns one (window, bucket) pair and scans the input once.
// This avoids atomics on projective points. The layout is intentionally simple
// for a first correct implementation; tuning the scan and window width needs
// measurements on actual GPU devices.
#define XARK_BUCKET_BITS 4u
#define XARK_BUCKET_WINDOWS 64u
#define XARK_BUCKET_COUNT 15u

inline uint scalar_digit_4(__global const ulong *scalars,
                           const ulong scalar_count,
                           const size_t index,
                           const uint window) {
  const uint bit = window * XARK_BUCKET_BITS;
  const uint limb = bit / 64u;
  const uint shift = bit % 64u;
  const ulong low = scalars[(size_t)limb * (size_t)scalar_count + index] >> shift;
  ulong value = low;
  if (shift > 60u && limb < 3u) {
    value |= scalars[(size_t)(limb + 1u) * (size_t)scalar_count + index]
             << (64u - shift);
  }
  return (uint)(value & 15UL);
}

inline void store_bucket_point(__global uint *output,
                               const size_t slot,
                               G1Jacobian point) {
  const size_t base = slot * 24;
  for (uint limb = 0; limb < 8; ++limb) {
    output[base + limb] = point.x.limb[limb];
    output[base + 8 + limb] = point.y.limb[limb];
    output[base + 16 + limb] = point.z.limb[limb];
  }
}

inline G1Jacobian load_bucket_point(__global const uint *input,
                                    const size_t slot) {
  const size_t base = slot * 24;
  G1Jacobian point;
  for (uint limb = 0; limb < 8; ++limb) {
    point.x.limb[limb] = input[base + limb];
    point.y.limb[limb] = input[base + 8 + limb];
    point.z.limb[limb] = input[base + 16 + limb];
  }
  return point;
}

__kernel void opencl_msm_validate_bucket_inputs(__global const uint *points,
                                                __global const ulong *scalars,
                                                const ulong scalar_count,
                                                __global uint *prepared,
                                                __global uint *valid) {
  const size_t index = get_global_id(0);
  if ((ulong)index >= scalar_count) return;
  G1Affine point;
  const int point_valid = point_from_words(points, index, &point);
  const int scalar_valid = scalar_is_canonical_words(scalars, scalar_count, index);
  valid[index] = (uint)(point_valid && scalar_valid);
  const size_t base = index * 17;
  for (uint limb = 0; limb < 8; ++limb) {
    prepared[base + limb] = point_valid ? point.x.limb[limb] : 0;
    prepared[base + 8 + limb] = point_valid ? point.y.limb[limb] : 0;
  }
  prepared[base + 16] = point_valid ? point.infinity : 1;
}

inline G1Affine load_bucket_affine(__global const uint *points, const size_t index) {
  const size_t base = index * 17;
  G1Affine point;
  for (uint limb = 0; limb < 8; ++limb) {
    point.x.limb[limb] = points[base + limb];
    point.y.limb[limb] = points[base + 8 + limb];
  }
  point.infinity = points[base + 16];
  return point;
}

__kernel void opencl_msm_buckets(__global const uint *points,
                                 __global const ulong *scalars,
                                 __global const uint *valid,
                                 const ulong scalar_count,
                                 __global uint *buckets) {
  const size_t work = get_global_id(0);
  const uint window = (uint)(work / XARK_BUCKET_COUNT);
  const uint bucket = (uint)(work % XARK_BUCKET_COUNT) + 1u;
  if (window >= XARK_BUCKET_WINDOWS) return;

  G1Jacobian sum = g1_infinity();
  for (size_t index = 0; (ulong)index < scalar_count; ++index) {
    if (valid[index] != 0 && scalar_digit_4(scalars, scalar_count, index, window) == bucket) {
      sum = g1_add_mixed(sum, load_bucket_affine(points, index));
    }
  }
  store_bucket_point(buckets, work, sum);
}

__kernel void opencl_msm_bucket_windows(__global const uint *buckets,
                                       __global uint *windows) {
  const uint window = (uint)get_global_id(0);
  if (window >= XARK_BUCKET_WINDOWS) return;
  G1Jacobian running = g1_infinity();
  G1Jacobian weighted = g1_infinity();
  for (int bucket = (int)XARK_BUCKET_COUNT; bucket >= 1; --bucket) {
    const size_t slot = (size_t)window * XARK_BUCKET_COUNT + (size_t)(bucket - 1);
    running = g1_add_jacobian(running, load_bucket_point(buckets, slot));
    weighted = g1_add_jacobian(weighted, running);
  }
  store_bucket_point(windows, window, weighted);
}

__kernel void opencl_msm_bucket_finish(__global const uint *windows,
                                       __global const uint *valid,
                                       const ulong scalar_count,
                                       __global uint *result_words) {
  if (get_global_id(0) != 0) return;
  for (uint i = 0; i < 17; ++i) result_words[i] = 0;
  for (size_t i = 0; (ulong)i < scalar_count; ++i) {
    if (valid[i] == 0) { result_words[16] = 2; return; }
  }

  G1Jacobian sum = g1_infinity();
  for (int window = (int)XARK_BUCKET_WINDOWS - 1; window >= 0; --window) {
    for (uint bit = 0; bit < XARK_BUCKET_BITS; ++bit) sum = g1_double(sum);
    sum = g1_add_jacobian(sum, load_bucket_point(windows, (size_t)window));
  }
  if (g1_is_infinity(sum)) {
    result_words[16] = 1;
    return;
  }
  Fq z_inv = fq_inverse(sum.z);
  Fq z_inv2 = fq_square(z_inv), z_inv3 = fq_mul(z_inv2, z_inv);
  Fq x = fq_to_canonical(fq_mul(sum.x, z_inv2));
  Fq y = fq_to_canonical(fq_mul(sum.y, z_inv3));
  for (uint i = 0; i < 8; ++i) {
    result_words[i] = x.limb[i];
    result_words[8 + i] = y.limb[i];
  }
}
