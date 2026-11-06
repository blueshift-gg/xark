#pragma once

#include <cstdint>

#if defined(__CUDACC__)
#define XARK_FQ_HD __host__ __device__
#else
#define XARK_FQ_HD
#endif

namespace xark_cuda {

struct Fq {
  std::uint32_t limbs[8];
};

// Host/device routines use value-returning accessors so NVCC does not need to
// take a device address for ordinary namespace-scope constant arrays.
XARK_FQ_HD inline std::uint32_t fq_modulus_limb(unsigned index) {
  switch (index) {
    case 0: return 0xd87cfd47u;
    case 1: return 0x3c208c16u;
    case 2: return 0x6871ca8du;
    case 3: return 0x97816a91u;
    case 4: return 0x8181585du;
    case 5: return 0xb85045b6u;
    case 6: return 0xe131a029u;
    case 7: return 0x30644e72u;
    default: return 0;
  }
}

XARK_FQ_HD inline std::uint32_t montgomery_one_limb(unsigned index) {
  switch (index) {
    case 0: return 0xc58f0d9du;
    case 1: return 0xd35d438du;
    case 2: return 0xf5c70b3du;
    case 3: return 0x0a78eb28u;
    case 4: return 0x7879462cu;
    case 5: return 0x666ea36fu;
    case 6: return 0x9a07df2fu;
    case 7: return 0x0e0a77c1u;
    default: return 0;
  }
}

XARK_FQ_HD inline std::uint32_t montgomery_r2_limb(unsigned index) {
  switch (index) {
    case 0: return 0x538afa89u;
    case 1: return 0xf32cfc5bu;
    case 2: return 0xd44501fbu;
    case 3: return 0xb5e71911u;
    case 4: return 0x0a417ff6u;
    case 5: return 0x47ab1effu;
    case 6: return 0xcab8351fu;
    case 7: return 0x06d89f71u;
    default: return 0;
  }
}

XARK_FQ_HD inline std::uint32_t montgomery_n0() { return 0xe4866389u; }

XARK_FQ_HD inline int compare(const std::uint32_t* a,
                              const std::uint32_t* b) {
  for (int i = 7; i >= 0; --i) {
    if (a[i] < b[i]) return -1;
    if (a[i] > b[i]) return 1;
  }
  return 0;
}

XARK_FQ_HD inline bool is_canonical(const std::uint32_t limbs[8]) {
  std::uint32_t modulus[8];
  for (unsigned i = 0; i < 8; ++i) modulus[i] = fq_modulus_limb(i);
  return compare(limbs, modulus) < 0;
}

XARK_FQ_HD inline std::uint32_t subtract_words(std::uint32_t* out,
                                               const std::uint32_t* a,
                                               const std::uint32_t* b) {
  std::uint64_t borrow = 0;
  for (unsigned i = 0; i < 8; ++i) {
    const std::uint64_t difference =
        static_cast<std::uint64_t>(a[i]) - b[i] - borrow;
    out[i] = static_cast<std::uint32_t>(difference);
    borrow = (difference >> 63) & 1u;
  }
  return static_cast<std::uint32_t>(borrow);
}

XARK_FQ_HD inline Fq add(Fq a, Fq b) {
  Fq result{};
  std::uint64_t carry = 0;
  for (unsigned i = 0; i < 8; ++i) {
    const std::uint64_t sum = static_cast<std::uint64_t>(a.limbs[i]) +
                              b.limbs[i] + carry;
    result.limbs[i] = static_cast<std::uint32_t>(sum);
    carry = sum >> 32;
  }
  std::uint32_t modulus[8];
  for (unsigned i = 0; i < 8; ++i) modulus[i] = fq_modulus_limb(i);
  if (compare(result.limbs, modulus) >= 0) {
    std::uint32_t reduced[8];
    subtract_words(reduced, result.limbs, modulus);
    for (unsigned i = 0; i < 8; ++i) result.limbs[i] = reduced[i];
  }
  return result;
}

XARK_FQ_HD inline Fq subtract(Fq a, Fq b) {
  Fq result{};
  const std::uint32_t borrow =
      subtract_words(result.limbs, a.limbs, b.limbs);
  if (borrow != 0) {
    std::uint64_t carry = 0;
    for (unsigned i = 0; i < 8; ++i) {
      const std::uint64_t sum =
          static_cast<std::uint64_t>(result.limbs[i]) + fq_modulus_limb(i) + carry;
      result.limbs[i] = static_cast<std::uint32_t>(sum);
      carry = sum >> 32;
    }
  }
  return result;
}

XARK_FQ_HD inline Fq montgomery_multiply(Fq a, Fq b) {
  std::uint32_t product[17] = {};
  for (unsigned i = 0; i < 8; ++i) {
    std::uint64_t carry = 0;
    for (unsigned j = 0; j < 8; ++j) {
      const std::uint64_t value =
          static_cast<std::uint64_t>(a.limbs[i]) * b.limbs[j] +
          product[i + j] + carry;
      product[i + j] = static_cast<std::uint32_t>(value);
      carry = value >> 32;
    }
    for (unsigned k = i + 8; k < 17; ++k) {
      const std::uint64_t value = product[k] + carry;
      product[k] = static_cast<std::uint32_t>(value);
      carry = value >> 32;
    }
  }

  for (unsigned i = 0; i < 8; ++i) {
    const std::uint32_t multiplier = product[i] * montgomery_n0();
    std::uint64_t carry = 0;
    for (unsigned j = 0; j < 8; ++j) {
      const std::uint64_t value =
          static_cast<std::uint64_t>(multiplier) * fq_modulus_limb(j) +
          product[i + j] + carry;
      product[i + j] = static_cast<std::uint32_t>(value);
      carry = value >> 32;
    }
    for (unsigned k = i + 8; k < 17; ++k) {
      const std::uint64_t value = product[k] + carry;
      product[k] = static_cast<std::uint32_t>(value);
      carry = value >> 32;
    }
  }

  Fq result{};
  for (unsigned i = 0; i < 8; ++i) result.limbs[i] = product[i + 8];
  std::uint32_t modulus[8];
  for (unsigned i = 0; i < 8; ++i) modulus[i] = fq_modulus_limb(i);
  if (compare(result.limbs, modulus) >= 0) {
    std::uint32_t reduced[8];
    subtract_words(reduced, result.limbs, modulus);
    for (unsigned i = 0; i < 8; ++i) result.limbs[i] = reduced[i];
  }
  return result;
}

XARK_FQ_HD inline Fq from_canonical(const std::uint32_t limbs[8]) {
  // The caller must first check is_canonical(limbs). REDC is not a reduction
  // for arbitrary 256-bit inputs.
  Fq value{};
  Fq r_squared{};
  for (unsigned i = 0; i < 8; ++i) {
    value.limbs[i] = limbs[i];
    r_squared.limbs[i] = montgomery_r2_limb(i);
  }
  return montgomery_multiply(value, r_squared);
}

XARK_FQ_HD inline Fq to_canonical(Fq value) {
  Fq one{};
  one.limbs[0] = 1;
  return montgomery_multiply(value, one);
}

XARK_FQ_HD inline bool equal(Fq a, Fq b) {
  for (unsigned i = 0; i < 8; ++i) {
    if (a.limbs[i] != b.limbs[i]) return false;
  }
  return true;
}

}  // namespace xark_cuda

#undef XARK_FQ_HD
