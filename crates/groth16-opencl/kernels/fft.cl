// Radix-2 Stockham FFT over BN254 Fr, natural order in and out.
//
// Elements are 8 Montgomery words (R = 2^256, as arkworks). Twiddles and coset
// factors are tables built on the host.
__constant uint XARK_FR_P[8] = {0xf0000001u, 0x43e1f593u, 0x79b97091u, 0x2833e848u,
                                0x8181585du, 0xb85045b6u, 0xe131a029u, 0x30644e72u};

inline Fq fr_mul(Fq a, Fq b) { return mont_mul(a, b, XARK_FR_P, 0xefffffffu); }
inline Fq fr_add(Fq a, Fq b) { return mod_add(a, b, XARK_FR_P); }
inline Fq fr_sub(Fq a, Fq b) { return mod_sub(a, b, XARK_FR_P); }

inline Fq load_fr(__global const uint *v, const size_t i) {
  Fq out;
  for (uint l = 0; l < 8; ++l) out.limb[l] = v[i * 8 + l];
  return out;
}

inline void store_fr(__global uint *v, const size_t i, const Fq x) {
  for (uint l = 0; l < 8; ++l) v[i * 8 + l] = x.limb[l];
}

// buf[i] *= factors[i].
__kernel void fr_scale(__global uint *buf, __global const uint *factors, const uint count) {
  const uint i = get_global_id(0);
  if (i >= count) return;
  store_fr(buf, i, fr_mul(load_fr(buf, i), load_fr(factors, i)));
}

// `buf[i] *= factor[0]`: the inverse DFT's 1/n, where no coset factor rides along.
__kernel void fr_scale_one(__global uint *buf, __global const uint *factor, const uint count) {
  const uint i = get_global_id(0);
  if (i >= count) return;
  store_fr(buf, i, fr_mul(load_fr(buf, i), load_fr(factor, 0)));
}

// One Stockham pass; `p` doubles each pass from 1 to n/2 (= halfn), `tw[j]` = ω^j.
__kernel void fr_fft_radix2(__global const uint *x, __global uint *y,
                            __global const uint *tw, const uint p, const uint halfn) {
  const uint i = get_global_id(0);
  if (i >= halfn) return;
  const uint k = i & (p - 1u);
  const Fq u0 = load_fr(x, i);
  Fq u1 = load_fr(x, i + halfn);
  if (k != 0) u1 = fr_mul(u1, load_fr(tw, (size_t)k * (halfn / p)));
  const uint j = (i << 1) - k;
  store_fr(y, j, fr_add(u0, u1));
  store_fr(y, j + p, fr_sub(u0, u1));
}

// Natural (n2 rows × n1 columns) → T-layout: out[k1·n2 + k2] = in[k1 + n1·k2].
__kernel void fr_transpose(__global const uint *in, __global uint *out,
                           const uint n1, const uint n2) {
  const uint o = get_global_id(0);
  if (o >= n1 * n2) return;
  const uint k1 = o / n2, k2 = o % n2;
  store_fr(out, o, load_fr(in, (size_t)k1 + (size_t)n1 * k2));
}
