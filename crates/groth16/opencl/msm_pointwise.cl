typedef struct { uint limb[8]; } Fq;
typedef struct { Fq x; Fq y; uint infinity; } G1Affine;
typedef struct { Fq x; Fq y; Fq z; } G1Jacobian;

inline uint fq_modulus(uint i) {
  const uint p[8] = {0xd87cfd47u, 0x3c208c16u, 0x6871ca8du, 0x97816a91u,
                     0x8181585du, 0xb85045b6u, 0xe131a029u, 0x30644e72u};
  return p[i];
}

inline uint fq_r2(uint i) {
  const uint r[8] = {0x538afa89u, 0xf32cfc5bu, 0xd44501fbu, 0xb5e71911u,
                     0x0a417ff6u, 0x47ab1effu, 0xcab8351fu, 0x06d89f71u};
  return r[i];
}

inline uint fq_one_word(uint i) {
  const uint r[8] = {0xc58f0d9du, 0xd35d438du, 0xf5c70b3du, 0x0a78eb28u,
                     0x7879462cu, 0x666ea36fu, 0x9a07df2fu, 0x0e0a77c1u};
  return r[i];
}

inline int fq_compare(Fq a, Fq b) {
  for (int i = 7; i >= 0; --i) {
    if (a.limb[i] < b.limb[i]) return -1;
    if (a.limb[i] > b.limb[i]) return 1;
  }
  return 0;
}

inline uint fq_sub_words(__private uint *out, Fq a, Fq b) {
  ulong borrow = 0;
  for (uint i = 0; i < 8; ++i) {
    const ulong difference = (ulong)a.limb[i] - b.limb[i] - borrow;
    out[i] = (uint)difference;
    borrow = (difference >> 63) & 1UL;
  }
  return (uint)borrow;
}

inline Fq fq_add(Fq a, Fq b) {
  Fq out;
  ulong carry = 0;
  for (uint i = 0; i < 8; ++i) {
    const ulong sum = (ulong)a.limb[i] + b.limb[i] + carry;
    out.limb[i] = (uint)sum;
    carry = sum >> 32;
  }
  Fq p;
  for (uint i = 0; i < 8; ++i) p.limb[i] = fq_modulus(i);
  if (fq_compare(out, p) >= 0) {
    uint reduced[8];
    fq_sub_words(reduced, out, p);
    for (uint i = 0; i < 8; ++i) out.limb[i] = reduced[i];
  }
  return out;
}

inline Fq fq_sub(Fq a, Fq b) {
  Fq out;
  const uint borrow = fq_sub_words(out.limb, a, b);
  if (borrow != 0) {
    ulong carry = 0;
    for (uint i = 0; i < 8; ++i) {
      const ulong sum = (ulong)out.limb[i] + fq_modulus(i) + carry;
      out.limb[i] = (uint)sum;
      carry = sum >> 32;
    }
  }
  return out;
}

inline Fq fq_mul(Fq a, Fq b) {
  uint product[17] = {0};
  for (uint i = 0; i < 8; ++i) {
    ulong carry = 0;
    for (uint j = 0; j < 8; ++j) {
      const ulong value = (ulong)a.limb[i] * b.limb[j] + product[i + j] + carry;
      product[i + j] = (uint)value;
      carry = value >> 32;
    }
    for (uint k = i + 8; k < 17; ++k) {
      const ulong value = product[k] + carry;
      product[k] = (uint)value;
      carry = value >> 32;
    }
  }
  for (uint i = 0; i < 8; ++i) {
    const uint multiplier = product[i] * 0xe4866389u;
    ulong carry = 0;
    for (uint j = 0; j < 8; ++j) {
      const ulong value = (ulong)multiplier * fq_modulus(j) + product[i + j] + carry;
      product[i + j] = (uint)value;
      carry = value >> 32;
    }
    for (uint k = i + 8; k < 17; ++k) {
      const ulong value = product[k] + carry;
      product[k] = (uint)value;
      carry = value >> 32;
    }
  }
  Fq out;
  Fq p;
  for (uint i = 0; i < 8; ++i) {
    out.limb[i] = product[i + 8];
    p.limb[i] = fq_modulus(i);
  }
  if (fq_compare(out, p) >= 0) {
    uint reduced[8];
    fq_sub_words(reduced, out, p);
    for (uint i = 0; i < 8; ++i) out.limb[i] = reduced[i];
  }
  return out;
}

inline Fq fq_from_canonical(__private const uint *words) {
  Fq a; Fq r2;
  for (uint i = 0; i < 8; ++i) { a.limb[i] = words[i]; r2.limb[i] = fq_r2(i); }
  return fq_mul(a, r2);
}

inline Fq fq_to_canonical(Fq a) {
  Fq one = {{1, 0, 0, 0, 0, 0, 0, 0}};
  return fq_mul(a, one);
}

inline int fq_zero(Fq a) {
  uint bits = 0;
  for (uint i = 0; i < 8; ++i) bits |= a.limb[i];
  return bits == 0;
}

inline Fq fq_one(void) {
  Fq out;
  for (uint i = 0; i < 8; ++i) out.limb[i] = fq_one_word(i);
  return out;
}

inline Fq fq_double(Fq a) { return fq_add(a, a); }
inline Fq fq_square(Fq a) { return fq_mul(a, a); }

inline Fq fq_inverse(Fq a) {
  const uint exponent[8] = {0xd87cfd45u, 0x3c208c16u, 0x6871ca8du, 0x97816a91u,
                            0x8181585du, 0xb85045b6u, 0xe131a029u, 0x30644e72u};
  Fq result = fq_one();
  for (int bit = 253; bit >= 0; --bit) {
    result = fq_square(result);
    if (((exponent[bit / 32] >> (bit % 32)) & 1u) != 0) result = fq_mul(result, a);
  }
  return result;
}

inline G1Jacobian g1_infinity(void) {
  G1Jacobian out; out.x = (Fq){{0}}; out.y = fq_one(); out.z = (Fq){{0}}; return out;
}

inline int g1_is_infinity(G1Jacobian p) { return fq_zero(p.z); }

inline G1Jacobian g1_double(G1Jacobian p) {
  if (g1_is_infinity(p) || fq_zero(p.y)) return g1_infinity();
  Fq a = fq_square(p.x), b = fq_square(p.y), c = fq_square(b);
  Fq d = fq_double(fq_sub(fq_sub(fq_square(fq_add(p.x, b)), a), c));
  Fq e = fq_add(fq_add(a, a), a), f = fq_square(e);
  Fq x3 = fq_sub(f, fq_double(d));
  Fq eight_c = fq_double(fq_double(fq_double(c)));
  Fq y3 = fq_sub(fq_mul(e, fq_sub(d, x3)), eight_c);
  Fq z3 = fq_double(fq_mul(p.y, p.z));
  G1Jacobian out = {x3, y3, z3}; return out;
}

inline G1Jacobian g1_from_affine(G1Affine p) {
  if (p.infinity != 0) return g1_infinity();
  G1Jacobian out = {p.x, p.y, fq_one()}; return out;
}

inline G1Jacobian g1_add_mixed(G1Jacobian left, G1Affine right) {
  if (right.infinity != 0) return left;
  if (g1_is_infinity(left)) return g1_from_affine(right);
  Fq z1z1 = fq_square(left.z);
  Fq u2 = fq_mul(right.x, z1z1);
  Fq s2 = fq_mul(right.y, fq_mul(left.z, z1z1));
  Fq h = fq_sub(u2, left.x), hh = fq_square(h);
  Fq i = fq_double(fq_double(hh)), j = fq_mul(h, i);
  Fq r = fq_double(fq_sub(s2, left.y)), v = fq_mul(left.x, i);
  if (fq_zero(h)) return fq_zero(r) ? g1_double(left) : g1_infinity();
  Fq x3 = fq_sub(fq_sub(fq_square(r), j), fq_double(v));
  Fq y3 = fq_sub(fq_mul(r, fq_sub(v, x3)), fq_double(fq_mul(left.y, j)));
  Fq z3 = fq_sub(fq_sub(fq_square(fq_add(left.z, h)), z1z1), hh);
  G1Jacobian out = {x3, y3, z3}; return out;
}

inline G1Jacobian g1_add_jacobian(G1Jacobian left, G1Jacobian right) {
  if (g1_is_infinity(left)) return right;
  if (g1_is_infinity(right)) return left;
  Fq z1z1 = fq_square(left.z), z2z2 = fq_square(right.z);
  Fq u1 = fq_mul(left.x, z2z2), u2 = fq_mul(right.x, z1z1);
  Fq s1 = fq_mul(left.y, fq_mul(right.z, z2z2));
  Fq s2 = fq_mul(right.y, fq_mul(left.z, z1z1));
  Fq h = fq_sub(u2, u1), r0 = fq_sub(s2, s1);
  if (fq_zero(h)) return fq_zero(r0) ? g1_double(left) : g1_infinity();
  Fq i = fq_square(fq_double(h)), j = fq_mul(h, i), r = fq_double(r0);
  Fq v = fq_mul(u1, i);
  Fq x3 = fq_sub(fq_sub(fq_square(r), j), fq_double(v));
  Fq y3 = fq_sub(fq_mul(r, fq_sub(v, x3)), fq_double(fq_mul(s1, j)));
  Fq z3 = fq_mul(fq_sub(fq_sub(fq_square(fq_add(left.z, right.z)), z1z1), z2z2), h);
  G1Jacobian out = {x3, y3, z3}; return out;
}

inline int scalar_is_canonical_words(__global const ulong *scalars,
                                     const ulong scalar_count, const size_t index) {
  const ulong modulus[4] = {0x43e1f593f0000001UL, 0x2833e84879b97091UL,
                            0xb85045b68181585dUL, 0x30644e72e131a029UL};
  for (int limb = 3; limb >= 0; --limb) {
    const ulong word = scalars[(size_t)limb * (size_t)scalar_count + index];
    if (word < modulus[limb]) return 1;
    if (word > modulus[limb]) return 0;
  }
  return 0;
}

inline int point_from_words(__global const uint *words, const size_t point,
                            G1Affine *out) {
  const size_t base = point * 17;
  const uint infinity = words[base + 16];
  if (infinity > 1) return 0;
  uint x_words[8], y_words[8];
  Fq x_canonical, y_canonical, p;
  for (uint i = 0; i < 8; ++i) {
    x_words[i] = words[base + i]; y_words[i] = words[base + 8 + i];
    x_canonical.limb[i] = x_words[i]; y_canonical.limb[i] = y_words[i];
    p.limb[i] = fq_modulus(i);
  }
  if (infinity != 0) {
    for (uint i = 0; i < 16; ++i) if (words[base + i] != 0) return 0;
    out->x = (Fq){{0}}; out->y = (Fq){{0}}; out->infinity = 1; return 1;
  }
  if (fq_compare(x_canonical, p) >= 0 || fq_compare(y_canonical, p) >= 0) return 0;
  Fq x = fq_from_canonical(x_words), y = fq_from_canonical(y_words);
  Fq lhs = fq_square(y);
  Fq x3 = fq_mul(fq_square(x), x);
  Fq three = fq_add(fq_add(fq_one(), fq_one()), fq_one());
  if (fq_compare(lhs, fq_add(x3, three)) != 0) return 0;
  out->x = x; out->y = y; out->infinity = 0; return 1;
}

inline G1Jacobian scalar_mul(G1Affine point, __global const ulong *scalars,
                             const ulong scalar_count, const size_t index) {
  G1Jacobian result = g1_infinity();
  for (int bit = 255; bit >= 0; --bit) {
    result = g1_double(result);
    const ulong word = scalars[(size_t)(bit / 64) * (size_t)scalar_count + index];
    if (((word >> (bit % 64)) & 1UL) != 0) result = g1_add_mixed(result, point);
  }
  return result;
}

__kernel void opencl_msm_terms(__global const uint *points,
                               __global const ulong *scalars,
                               const ulong scalar_count,
                               __global uint *terms,
                               __global uint *valid) {
  const size_t index = get_global_id(0);
  if (index >= scalar_count) return;
  G1Affine point;
  G1Jacobian term;
  if (!scalar_is_canonical_words(scalars, scalar_count, index) ||
      !point_from_words(points, index, &point)) {
    valid[index] = 0;
    term = g1_infinity();
  } else {
    valid[index] = 1;
    term = scalar_mul(point, scalars, scalar_count, index);
  }
  const size_t base = index * 24;
  for (uint i = 0; i < 8; ++i) {
    terms[base + i] = term.x.limb[i];
    terms[base + 8 + i] = term.y.limb[i];
    terms[base + 16 + i] = term.z.limb[i];
  }
}

inline G1Jacobian load_jacobian(__global const uint *terms, const size_t index) {
  const size_t base = index * 24;
  G1Jacobian point;
  for (uint limb = 0; limb < 8; ++limb) {
    point.x.limb[limb] = terms[base + limb];
    point.y.limb[limb] = terms[base + 8 + limb];
    point.z.limb[limb] = terms[base + 16 + limb];
  }
  return point;
}

inline void store_jacobian(__global uint *terms, const size_t index,
                           G1Jacobian point) {
  const size_t base = index * 24;
  for (uint limb = 0; limb < 8; ++limb) {
    terms[base + limb] = point.x.limb[limb];
    terms[base + 8 + limb] = point.y.limb[limb];
    terms[base + 16 + limb] = point.z.limb[limb];
  }
}

__kernel void opencl_msm_reduce_pairs(__global const uint *terms_in,
                                      __global const uint *valid_in,
                                      __global uint *terms_out,
                                      __global uint *valid_out,
                                      const ulong input_count) {
  const size_t output = get_global_id(0);
  const size_t left_index = output * 2;
  if ((ulong)left_index >= input_count) return;
  const size_t right_index = left_index + 1;
  G1Jacobian sum = load_jacobian(terms_in, left_index);
  uint is_valid = valid_in[left_index];
  if ((ulong)right_index < input_count) {
    sum = g1_add_jacobian(sum, load_jacobian(terms_in, right_index));
    is_valid &= valid_in[right_index];
  }
  store_jacobian(terms_out, output, sum);
  valid_out[output] = is_valid;
}

__kernel void opencl_msm_finish(__global const uint *terms,
                                __global const uint *valid,
                                __global uint *result_words) {
  if (get_global_id(0) != 0) return;
  for (uint i = 0; i < 17; ++i) result_words[i] = 0;
  if (valid[0] == 0) { result_words[16] = 2; return; }
  G1Jacobian sum = load_jacobian(terms, 0);
  if (g1_is_infinity(sum)) {
    for (uint i = 0; i < 16; ++i) result_words[i] = 0;
    result_words[16] = 1;
    return;
  }
  Fq z_inv = fq_inverse(sum.z);
  Fq z_inv2 = fq_square(z_inv), z_inv3 = fq_mul(z_inv2, z_inv);
  Fq x = fq_to_canonical(fq_mul(sum.x, z_inv2));
  Fq y = fq_to_canonical(fq_mul(sum.y, z_inv3));
  for (uint i = 0; i < 8; ++i) { result_words[i] = x.limb[i]; result_words[8 + i] = y.limb[i]; }
  result_words[16] = 0;
}
