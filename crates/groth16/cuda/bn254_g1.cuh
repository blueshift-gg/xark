#pragma once

#include "bn254_fq.cuh"

#if defined(__CUDACC__)
#define XARK_G1_HD __host__ __device__
#else
#define XARK_G1_HD
#endif

namespace xark_cuda {

struct G1Affine {
  Fq x;
  Fq y;
  bool infinity;
};

struct G1Jacobian {
  Fq x;
  Fq y;
  Fq z;
};

XARK_G1_HD inline Fq fq_zero() { return Fq{}; }

XARK_G1_HD inline Fq fq_one() {
  Fq result{};
  for (unsigned i = 0; i < 8; ++i)
    result.limbs[i] = montgomery_one_limb(i);
  return result;
}

XARK_G1_HD inline bool fq_is_zero(Fq value) {
  for (unsigned i = 0; i < 8; ++i) {
    if (value.limbs[i] != 0)
      return false;
  }
  return true;
}

XARK_G1_HD inline Fq fq_double(Fq value) { return add(value, value); }

XARK_G1_HD inline Fq fq_triple(Fq value) {
  return add(add(value, value), value);
}

XARK_G1_HD inline std::uint32_t fq_inverse_exponent_limb(unsigned index) {
  switch (index) {
  case 0:
    return 0xd87cfd45u;
  case 1:
    return 0x3c208c16u;
  case 2:
    return 0x6871ca8du;
  case 3:
    return 0x97816a91u;
  case 4:
    return 0x8181585du;
  case 5:
    return 0xb85045b6u;
  case 6:
    return 0xe131a029u;
  case 7:
    return 0x30644e72u;
  default:
    return 0;
  }
}

XARK_G1_HD inline Fq fq_square(Fq value) {
  return montgomery_multiply(value, value);
}

XARK_G1_HD inline Fq fq_inverse(Fq value) {
  Fq result = fq_one();
  for (int bit = 253; bit >= 0; --bit) {
    result = fq_square(result);
    if (((fq_inverse_exponent_limb(bit / 32) >> (bit % 32)) & 1u) != 0) {
      result = montgomery_multiply(result, value);
    }
  }
  return result;
}

XARK_G1_HD inline G1Jacobian g1_infinity() {
  return G1Jacobian{fq_zero(), fq_one(), fq_zero()};
}

XARK_G1_HD inline bool g1_is_infinity(const G1Jacobian &point) {
  return fq_is_zero(point.z);
}

XARK_G1_HD inline G1Jacobian g1_from_affine(const G1Affine &point) {
  if (point.infinity)
    return g1_infinity();
  return G1Jacobian{point.x, point.y, fq_one()};
}

XARK_G1_HD inline G1Jacobian g1_double(const G1Jacobian &point) {
  if (g1_is_infinity(point) || fq_is_zero(point.y))
    return g1_infinity();

  const Fq a = fq_square(point.x);
  const Fq b = fq_square(point.y);
  const Fq c = fq_square(b);
  const Fq x_plus_b = add(point.x, b);
  const Fq d = fq_double(subtract(subtract(fq_square(x_plus_b), a), c));
  const Fq e = fq_triple(a);
  const Fq f = fq_square(e);
  const Fq x3 = subtract(f, fq_double(d));
  const Fq eight_c = fq_double(fq_double(fq_double(c)));
  const Fq y3 = subtract(montgomery_multiply(e, subtract(d, x3)), eight_c);
  const Fq z3 = fq_double(montgomery_multiply(point.y, point.z));
  return G1Jacobian{x3, y3, z3};
}

XARK_G1_HD inline G1Jacobian g1_add_mixed(const G1Jacobian &left,
                                          const G1Affine &right) {
  if (right.infinity)
    return left;
  if (g1_is_infinity(left))
    return g1_from_affine(right);

  const Fq z1z1 = fq_square(left.z);
  const Fq u2 = montgomery_multiply(right.x, z1z1);
  const Fq s2 = montgomery_multiply(right.y, montgomery_multiply(left.z, z1z1));
  const Fq h = subtract(u2, left.x);
  const Fq hh = fq_square(h);
  const Fq i = fq_double(fq_double(hh));
  const Fq j = montgomery_multiply(h, i);
  const Fq r = fq_double(subtract(s2, left.y));
  const Fq v = montgomery_multiply(left.x, i);
  if (fq_is_zero(h)) {
    return fq_is_zero(r) ? g1_double(left) : g1_infinity();
  }

  const Fq x3 = subtract(subtract(fq_square(r), j), fq_double(v));
  const Fq y3 = subtract(montgomery_multiply(r, subtract(v, x3)),
                         fq_double(montgomery_multiply(left.y, j)));
  const Fq z3 = subtract(subtract(fq_square(add(left.z, h)), z1z1), hh);
  return G1Jacobian{x3, y3, z3};
}

XARK_G1_HD inline G1Jacobian g1_add_jacobian(const G1Jacobian &left,
                                             const G1Jacobian &right) {
  if (g1_is_infinity(left))
    return right;
  if (g1_is_infinity(right))
    return left;

  const Fq z1z1 = fq_square(left.z);
  const Fq z2z2 = fq_square(right.z);
  const Fq u1 = montgomery_multiply(left.x, z2z2);
  const Fq u2 = montgomery_multiply(right.x, z1z1);
  const Fq s1 = montgomery_multiply(left.y, montgomery_multiply(right.z, z2z2));
  const Fq s2 = montgomery_multiply(right.y, montgomery_multiply(left.z, z1z1));
  const Fq h = subtract(u2, u1);
  const Fq r0 = subtract(s2, s1);
  if (fq_is_zero(h)) {
    return fq_is_zero(r0) ? g1_double(left) : g1_infinity();
  }

  const Fq i = fq_square(fq_double(h));
  const Fq j = montgomery_multiply(h, i);
  const Fq r = fq_double(r0);
  const Fq v = montgomery_multiply(u1, i);
  const Fq x3 = subtract(subtract(fq_square(r), j), fq_double(v));
  const Fq y3 = subtract(montgomery_multiply(r, subtract(v, x3)),
                         fq_double(montgomery_multiply(s1, j)));
  const Fq z3 = montgomery_multiply(
      subtract(subtract(fq_square(add(left.z, right.z)), z1z1), z2z2), h);
  return G1Jacobian{x3, y3, z3};
}

XARK_G1_HD inline G1Affine g1_to_affine(const G1Jacobian &point) {
  if (g1_is_infinity(point))
    return G1Affine{fq_zero(), fq_zero(), true};
  const Fq z_inv = fq_inverse(point.z);
  const Fq z_inv2 = fq_square(z_inv);
  const Fq z_inv3 = montgomery_multiply(z_inv2, z_inv);
  return G1Affine{montgomery_multiply(point.x, z_inv2),
                  montgomery_multiply(point.y, z_inv3), false};
}

} // namespace xark_cuda

#undef XARK_G1_HD
