// OpenCL counterpart to the CUDA scalar-window extraction stage.
// Input limbs are little-endian and scalar-major within each SoA limb plane:
// limbs[limb * scalar_count + scalar]. The caller must validate buffer sizes.

#define XARK_WINDOW_BITS 11u
#define XARK_WINDOW_COUNT 24u
#define XARK_DIGIT_MASK ((1u << XARK_WINDOW_BITS) - 1u)

inline ulong scalar_limb(__global const ulong *limbs,
                         const size_t scalar_count,
                         const size_t scalar,
                         const uint limb) {
  return limbs[(size_t)limb * scalar_count + scalar];
}

inline ushort extract_digit(__global const ulong *limbs,
                            const size_t scalar_count,
                            const size_t scalar,
                            const uint window) {
  const uint bit = window * XARK_WINDOW_BITS;
  const uint limb = bit / 64u;
  const uint shift = bit % 64u;
  ulong value = scalar_limb(limbs, scalar_count, scalar, limb) >> shift;
  if (shift != 0u && limb + 1u < 4u) {
    value |= scalar_limb(limbs, scalar_count, scalar, limb + 1u) << (64u - shift);
  }
  return (ushort)(value & XARK_DIGIT_MASK);
}

inline int scalar_is_canonical(__global const ulong *limbs,
                               const size_t scalar_count,
                               const size_t scalar) {
  const ulong modulus[4] = {
      0x43e1f593f0000001UL,
      0x2833e84879b97091UL,
      0xb85045b68181585dUL,
      0x30644e72e131a029UL,
  };
  for (int limb = 3; limb >= 0; --limb) {
    const ulong value = scalar_limb(limbs, scalar_count, scalar, (uint)limb);
    if (value < modulus[limb]) return 1;
    if (value > modulus[limb]) return 0;
  }
  return 0;
}

__kernel void extract_msm_digits(__global const ulong *limbs,
                                 const ulong scalar_count,
                                 __global ushort *digits) {
  const size_t scalar = get_global_id(0);
  const size_t window = get_global_id(1);
  if (scalar >= scalar_count || window >= XARK_WINDOW_COUNT) return;
  digits[window * scalar_count + scalar] =
      extract_digit(limbs, scalar_count, scalar, (uint)window);
}

__kernel void validate_msm_scalars(__global const ulong *limbs,
                                   const ulong scalar_count,
                                   __global uint *valid) {
  const size_t scalar = get_global_id(0);
  if (scalar >= scalar_count) return;
  valid[scalar] = (uint)scalar_is_canonical(limbs, scalar_count, scalar);
}
