// Sorted-bucket MSM pipeline for BN254 G1.
//
// Points: 16 Montgomery words per point (x then y) and a flag word (0 = point,
// 1 = infinity). Scalars: 4 little-endian u64 limbs per scalar. Digits are
// signed, `bits` wide, in [-2^(bits-1), 2^(bits-1)); bucket `b` of window `w`
// holds the points whose digit has magnitude `b + 1`, so a window has
// B = 2^(bits-1) buckets. `status` collects bit 1 (invalid point) and bit 2
// (non-canonical scalar); the host declines the MSM when it is non-zero.
//
// Work per stage scales with the input: one work item per point (prepare,
// digits, scatter), per segment of at most a few dozen points (segment sums),
// per bucket (fold) and per range of buckets (window reduce).

__constant ulong XARK_FR_MODULUS[4] = {0x43e1f593f0000001UL, 0x2833e84879b97091UL,
                                       0xb85045b68181585dUL, 0x30644e72e131a029UL};

// Uncompressed arkworks encoding: x then y, canonical little-endian; the top
// two bits of y carry the flags (bit 6 of the last byte = infinity).
__kernel void msm_prepare_uncompressed(__global const uint *raw,
                                       const uint count,
                                       __global uint *points,
                                       __global uint *flags,
                                       volatile __global uint *status) {
  const uint i = get_global_id(0);
  if (i >= count) return;
  const size_t base = (size_t)i * 16;
  uint x_words[8], y_words[8];
  Fq x_canonical, y_canonical, p;
  for (uint l = 0; l < 8; ++l) {
    x_words[l] = raw[base + l];
    y_words[l] = raw[base + 8 + l];
    p.limb[l] = fq_modulus(l);
  }
  const uint infinity = (y_words[7] >> 30) & 1u;
  y_words[7] &= 0x3fffffffu;
  uint any = 0;
  for (uint l = 0; l < 8; ++l) {
    x_canonical.limb[l] = x_words[l];
    y_canonical.limb[l] = y_words[l];
    any |= x_words[l] | y_words[l];
  }
  if (infinity) {
    flags[i] = 1;
    if (any) atomic_or(status, 1u);
    return;
  }
  flags[i] = 0;
  if (fq_compare(x_canonical, p) >= 0 || fq_compare(y_canonical, p) >= 0) {
    atomic_or(status, 1u);
    return;
  }
  const Fq x = fq_from_canonical(x_words), y = fq_from_canonical(y_words);
  const Fq three = fq_add(fq_add(fq_one(), fq_one()), fq_one());
  if (fq_compare(fq_square(y), fq_add(fq_mul(fq_square(x), x), three)) != 0) {
    atomic_or(status, 1u);
    return;
  }
  for (uint l = 0; l < 8; ++l) {
    points[base + l] = x.limb[l];
    points[base + 8 + l] = y.limb[l];
  }
}

__kernel void msm_signed_digits(__global const ulong *scalars,
                                const uint count,
                                const uint bits,
                                const uint windows,
                                __global const uint *flags,
                                __global short *digits,
                                volatile __global uint *counts,
                                volatile __global uint *status) {
  const uint i = get_global_id(0);
  if (i >= count) return;
  ulong s[4];
  for (uint l = 0; l < 4; ++l) s[l] = scalars[(size_t)i * 4 + l];
  int canonical = 0;
  for (int l = 3; l >= 0; --l) {
    if (s[l] < XARK_FR_MODULUS[l]) { canonical = 1; break; }
    if (s[l] > XARK_FR_MODULUS[l]) break;
  }
  if (!canonical) atomic_or(status, 2u);
  const int skip = !canonical || flags[i] != 0;
  const uint buckets = 1u << (bits - 1);
  const int full = 1 << bits;
  const ulong mask = (1UL << bits) - 1UL;
  int carry = 0;
  for (uint w = 0; w < windows; ++w) {
    const uint bit = w * bits, limb = bit / 64u, shift = bit % 64u;
    ulong v = limb < 4u ? s[limb] >> shift : 0UL;
    if (shift + bits > 64u && limb + 1u < 4u) v |= s[limb + 1u] << (64u - shift);
    int d = (int)(v & mask) + carry;
    carry = d >= (int)buckets;
    if (carry) d -= full;
    if (skip) d = 0;
    digits[(size_t)w * count + i] = (short)d;
    if (d != 0) atomic_inc(&counts[(size_t)w * buckets + (uint)abs(d) - 1u]);
  }
}

// `cursor` starts as each bucket's offset into `order` and ends as its end.
// The top bit of an `order` entry marks a negated point.
__kernel void msm_scatter(__global const short *digits,
                          const uint count,
                          const uint bits,
                          const uint windows,
                          volatile __global uint *cursor,
                          __global uint *order) {
  const uint i = get_global_id(0);
  if (i >= count) return;
  const uint buckets = 1u << (bits - 1);
  for (uint w = 0; w < windows; ++w) {
    const int d = digits[(size_t)w * count + i];
    if (d == 0) continue;
    const uint pos = atomic_inc(&cursor[(size_t)w * buckets + (uint)abs(d) - 1u]);
    order[pos] = i | (d < 0 ? 0x80000000u : 0u);
  }
}

// `segments` holds (lo, hi, slot) per segment, longest first: the work items of
// a SIMD group run in lockstep, so neighbours of equal length waste no lanes.
__kernel void msm_segment_sums(__global const uint *points,
                               __global const uint *order,
                               __global const uint *segments,
                               const uint segment_count,
                               __global uint *partials) {
  const uint t = get_global_id(0);
  if (t >= segment_count) return;
  const uint lo = segments[3 * t], hi = segments[3 * t + 1], segment = segments[3 * t + 2];
  const Fq zero = {{0}};
  G1Jacobian sum = g1_infinity();
  for (uint i = lo; i < hi; ++i) {
    const uint entry = order[i];
    const size_t base = (size_t)(entry & 0x7fffffffu) * 16;
    G1Affine point;
    for (uint l = 0; l < 8; ++l) {
      point.x.limb[l] = points[base + l];
      point.y.limb[l] = points[base + 8 + l];
    }
    if (entry >> 31) point.y = fq_sub(zero, point.y);
    point.infinity = 0;
    sum = g1_add_mixed(sum, point);
  }
  store_bucket_point(partials, segment, sum);
}

__kernel void msm_bucket_fold(__global const uint *partials,
                              __global const uint *bucket_segments,
                              const uint bucket_count,
                              __global uint *buckets) {
  const uint k = get_global_id(0);
  if (k >= bucket_count) return;
  G1Jacobian sum = g1_infinity();
  for (uint s = bucket_segments[k]; s < bucket_segments[k + 1]; ++s) {
    sum = g1_add_jacobian(sum, load_bucket_point(partials, s));
  }
  store_bucket_point(buckets, k, sum);
}

// One work item per `span` buckets of a window: Σ (b + 1)·bucket_b over its
// range, as the running-sum trick plus `lo`·(range sum).
__kernel void msm_window_reduce(__global const uint *buckets,
                                const uint bucket_count,
                                const uint span,
                                const uint ranges,
                                const uint windows,
                                __global uint *out) {
  const uint t = get_global_id(0);
  if (t >= windows * ranges) return;
  const uint w = t / ranges, r = t % ranges;
  const uint lo = r * span, hi = min(lo + span, bucket_count);
  const size_t base = (size_t)w * bucket_count;
  G1Jacobian running = g1_infinity(), weighted = g1_infinity();
  for (int b = (int)hi - 1; b >= (int)lo; --b) {
    running = g1_add_jacobian(running, load_bucket_point(buckets, base + (uint)b));
    weighted = g1_add_jacobian(weighted, running);
  }
  G1Jacobian scaled = g1_infinity();
  for (int bit = 20; bit >= 0; --bit) {
    scaled = g1_double(scaled);
    if ((lo >> bit) & 1u) scaled = g1_add_jacobian(scaled, running);
  }
  store_bucket_point(out, t, g1_add_jacobian(weighted, scaled));
}
