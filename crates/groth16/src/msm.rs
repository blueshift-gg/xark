//! Multi-scalar multiplication (`Σ sᵢ·Pᵢ`).
//!
//! * [`naive_msm`] — textbook double-and-add over each scalar's integer bits. Slow,
//!   obviously correct, and convention-free: the independent oracle the fast path
//!   is tested against (alongside arkworks).
//! * [`msm`] — our Pippenger: scalars are partitioned by magnitude (zero / ±1 /
//!   ≤16 / ≤32 / ≤64 / ≤128 / full bits, using `r − s` for "small negative"
//!   values), and each class runs a signed-digit (Booth) bucket method with
//!   `2^(c−1)` buckets, parallel over `windows × point-slices`. Witness vectors are
//!   dominated by bits and small limbs, so most points never see a full-width scalar.
//! * [`StreamingMsm`] — the accumulator the prover folds chunk MSMs into. An MSM is
//!   an associative, commutative sum, so a vector split at *any* seams sums to the
//!   same point; the chunk is dropped as soon as it is folded.

use ark_bn254::Fr;
use ark_ec::CurveGroup;
use ark_ff::{BigInteger, One, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use rayon::prelude::*;

/// A scalar in canonical (non-Montgomery) integer form.
pub type Scalar = <Fr as PrimeField>::BigInt;

/// Short-Weierstrass groups: affine coordinates for batch-affine accumulation.
pub trait SwCurve: CurveGroup<ScalarField = Fr> {
    /// `(x, y)`, or `None` for the point at infinity.
    fn xy(a: &Self::Affine) -> Option<(Self::BaseField, Self::BaseField)>;
    /// The affine point `(x, y)` (on the curve by construction).
    fn from_xy(x: Self::BaseField, y: Self::BaseField) -> Self::Affine;
    /// The curve's `a` coefficient (for the doubling slope `(3x² + a)/2y`).
    fn coeff_a() -> Self::BaseField;
}

impl<P: ark_ec::short_weierstrass::SWCurveConfig<ScalarField = Fr>> SwCurve
    for ark_ec::short_weierstrass::Projective<P>
{
    #[inline(always)]
    fn xy(a: &Self::Affine) -> Option<(P::BaseField, P::BaseField)> {
        use ark_ec::AffineRepr;
        (!a.is_zero()).then_some((a.x, a.y))
    }
    #[inline(always)]
    fn from_xy(x: P::BaseField, y: P::BaseField) -> Self::Affine {
        ark_ec::short_weierstrass::Affine::new_unchecked(x, y)
    }
    fn coeff_a() -> P::BaseField {
        P::COEFF_A
    }
}

/// Accumulate buckets in affine coordinates with batched inversions (default
/// on); a switch so `examples/bench_kernels.rs` and `bench_prove.rs` can compare
/// against XYZZ accumulation.
pub static BATCH_AFFINE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(true);

/// Additions per shared inversion.
const BATCH: usize = 512;

/// Affine buckets filled by batch-affine additions: each `(bucket, point)` addition
/// costs ~5M+1S (vs 8M+2S for an XYZZ mixed add); one field inversion is shared
/// by a whole batch (Montgomery's trick). A bucket may appear once per batch; a
/// conflicting addition goes into that bucket's XYZZ side accumulator instead (the
/// plain path's cost), so skewed digit distributions never stall on deferrals.
struct AffineBuckets<G: SwCurve> {
    x: Vec<G::BaseField>,
    y: Vec<G::BaseField>,
    used: Vec<bool>,
    /// `stamp[b] == epoch` ⇔ bucket `b` is already in the current batch.
    stamp: Vec<u32>,
    epoch: u32,
    batch: Vec<(u32, G::BaseField, G::BaseField)>,
    side: Vec<G::Bucket>,
    den: Vec<G::BaseField>,
    pre: Vec<G::BaseField>,
}

impl<G: SwCurve> AffineBuckets<G> {
    fn new(nb: usize) -> Self {
        AffineBuckets {
            x: vec![G::BaseField::zero(); nb],
            y: vec![G::BaseField::zero(); nb],
            used: vec![false; nb],
            stamp: vec![0; nb],
            epoch: 1,
            batch: Vec::with_capacity(BATCH),
            side: vec![G::ZERO_BUCKET; nb],
            den: Vec::with_capacity(BATCH),
            pre: Vec::with_capacity(BATCH),
        }
    }

    #[inline(always)]
    fn add(&mut self, b: u32, p: &G::Affine, px: G::BaseField, py: G::BaseField, neg: bool) {
        let bi = b as usize;
        if !self.used[bi] {
            self.x[bi] = px;
            self.y[bi] = py;
            self.used[bi] = true;
        } else if self.stamp[bi] == self.epoch {
            if neg {
                self.side[bi] -= p;
            } else {
                self.side[bi] += p;
            }
        } else {
            self.stamp[bi] = self.epoch;
            self.batch.push((b, px, py));
            if self.batch.len() == BATCH {
                self.flush();
            }
        }
    }

    fn flush(&mut self) {
        use ark_ff::{AdditiveGroup, Field};
        let one = G::BaseField::one();
        self.den.clear();
        self.pre.clear();
        let mut acc = one;
        for &(b, px, py) in &self.batch {
            let (x1, y1) = (self.x[b as usize], self.y[b as usize]);
            let d = if x1 != px {
                px - x1
            } else if y1 == py && !y1.is_zero() {
                y1.double() // doubling
            } else {
                one // P + (−P) = ∞ (or a 2-torsion point): no inverse needed
            };
            self.pre.push(acc);
            self.den.push(d);
            acc *= d;
        }
        let mut inv = acc.inverse().expect("nonzero batch denominator");
        for i in (0..self.batch.len()).rev() {
            let (b, px, py) = self.batch[i];
            let bi = b as usize;
            let inv_i = inv * self.pre[i];
            inv *= self.den[i];
            let (x1, y1) = (self.x[bi], self.y[bi]);
            let lambda = if x1 != px {
                (py - y1) * inv_i
            } else if y1 == py && !y1.is_zero() {
                (x1.square().double() + x1.square() + G::coeff_a()) * inv_i
            } else {
                self.used[bi] = false;
                continue;
            };
            let x3 = lambda.square() - x1 - px;
            self.y[bi] = lambda * (x1 - x3) - y1;
            self.x[bi] = x3;
        }
        self.batch.clear();
        self.epoch = self.epoch.wrapping_add(1).max(1);
    }

    /// Finish the last batch; each bucket is its affine part plus its side sum.
    #[allow(clippy::type_complexity)]
    fn finish(
        mut self,
    ) -> (
        Vec<G::BaseField>,
        Vec<G::BaseField>,
        Vec<bool>,
        Vec<G::Bucket>,
    ) {
        self.flush();
        (self.x, self.y, self.used, self.side)
    }
}

/// Σ sᵢ·Pᵢ by plain double-and-add, MSB first, over all 256 bits of each scalar's
/// integer value. Pairs beyond the shorter input are ignored.
pub fn naive_msm<G: CurveGroup>(bases: &[G::Affine], scalars: &[Scalar]) -> G {
    let mut acc = G::zero();
    for (p, s) in bases.iter().zip(scalars) {
        let mut term = G::zero();
        for i in (0..256).rev() {
            term.double_in_place();
            if s.get_bit(i) {
                term += p;
            }
        }
        acc += term;
    }
    acc
}

/// Canonical (compressed affine) encoding of a point — compare points through
/// this, never through raw projective coordinates, which differ for equal points.
pub fn canonical_bytes<G: CurveGroup>(p: &G) -> Vec<u8> {
    let mut out = Vec::new();
    p.into_affine()
        .serialize_compressed(&mut out)
        .expect("serializing to a Vec cannot fail");
    out
}

/// Whether two group elements are the same point (compared in normalized form).
pub fn same_point<G: CurveGroup>(a: &G, b: &G) -> bool {
    canonical_bytes(a) == canonical_bytes(b)
}

/// Fold-as-you-go MSM: feed `(bases, scalars)` chunks in any order and at any
/// seams; [`finish`](Self::finish) returns the same point as one MSM over the
/// concatenation.
pub struct StreamingMsm<G: SwCurve> {
    acc: G,
    terms: usize,
}

impl<G: SwCurve> Default for StreamingMsm<G> {
    fn default() -> Self {
        Self::new()
    }
}

impl<G: SwCurve> StreamingMsm<G> {
    pub fn new() -> Self {
        Self {
            acc: G::zero(),
            terms: 0,
        }
    }

    /// Fold one chunk. Only `min(bases.len(), scalars.len())` pairs are used.
    pub fn feed(&mut self, bases: &[G::Affine], scalars: &[Scalar]) {
        self.acc += msm::<G>(bases, scalars);
        self.terms += bases.len().min(scalars.len());
    }

    /// Pairs folded so far.
    pub fn terms(&self) -> usize {
        self.terms
    }

    pub fn finish(self) -> G {
        self.acc
    }
}

/// Bits `[pos, pos+len)` of `s` (zero past bit 255). `len < 64`.
#[inline(always)]
fn bits_at(s: &Scalar, pos: usize, len: usize) -> u64 {
    let limbs = s.as_ref();
    let (q, r) = (pos / 64, pos % 64);
    if q >= limbs.len() {
        return 0;
    }
    let mut v = limbs[q] >> r;
    if r + len > 64 && q + 1 < limbs.len() {
        v |= limbs[q + 1] << (64 - r);
    }
    v & ((1u64 << len) - 1)
}

/// Booth (signed) digit `w` of width `c`: `v + b₋₁ − 2^c·b_top`, in
/// `[−2^(c−1), 2^(c−1)]`. Σ_w d_w·2^(wc) = s whenever the windows cover one bit
/// past the scalar's top bit.
#[inline(always)]
fn booth_digit(s: &Scalar, w: usize, c: usize) -> i64 {
    let pos = w * c;
    let v = bits_at(s, pos, c) as i64;
    let carry = if pos == 0 {
        0
    } else {
        bits_at(s, pos - 1, 1) as i64
    };
    v + carry - (((v >> (c - 1)) & 1) << c)
}

/// Window width for `n` points of `bits`-bit magnitude, from the cost model
/// `windows(c) · (n mixed adds + 2·2^(c−1) bucket-reduction adds)` (a full
/// addition ≈ 1.4 mixed ones), minimized over `c ∈ [2, 15]` (≤ 15 keeps every
/// signed digit in an `i16`). Unlike a size-only `ln n` rule this shrinks the
/// window for narrow scalars, where fewer windows can't be bought back with more
/// buckets.
fn window_bits(n: usize, bits: usize) -> usize {
    let cost = |c: usize| (bits + 1).div_ceil(c) as f64 * (n as f64 + 1.4 * (1u64 << c) as f64);
    (2..=15)
        .min_by(|&a, &b| cost(a).total_cmp(&cost(b)))
        .unwrap()
}

/// One magnitude class: entries packed as `index | NEG` (index < 2³¹).
const NEG: u32 = 1 << 31;

#[derive(Clone, Copy)]
struct DigitPtr(*mut i16);
unsafe impl Send for DigitPtr {}
unsafe impl Sync for DigitPtr {}
impl DigitPtr {
    /// Method access, so closures capture the `Sync` wrapper, not the raw field.
    #[inline(always)]
    fn get(self) -> *mut i16 {
        self.0
    }
}

/// Signed-digit Pippenger over `entries` (point index + sign), each of whose
/// magnitude fits in `bits` bits.
fn pippenger<G: SwCurve>(
    bases: &[G::Affine],
    scalars: &[Scalar],
    entries: &[u32],
    bits: usize,
) -> G {
    let n = entries.len();
    if n == 0 {
        return G::zero();
    }
    // ≤ 15-bit windows so every signed digit (|d| ≤ 2^(c−1)) fits an i16.
    let c = window_bits(n, bits);
    let windows = (bits + 1).div_ceil(c);
    let threads = rayon::current_num_threads().max(1);
    // Split points so `windows × parts` covers the pool ~2× over, but keep slices
    // large enough that the per-task bucket reduction (2^c adds) stays amortized.
    let parts = (2 * threads)
        .div_ceil(windows)
        .min((n >> (c + 1)).max(1))
        .max(1);
    let part_len = n.div_ceil(parts);
    let modulus = Fr::MODULUS;

    // Signed digits, computed once, stored window-major (each window pass then
    // streams one contiguous i16 row) with the entry's sign folded in.
    let mut digits = vec![0i16; windows * n];
    {
        let ptr = DigitPtr(digits.as_mut_ptr());
        entries.par_chunks(4096).enumerate().for_each(|(ci, es)| {
            for (j, &e) in es.iter().enumerate() {
                let k = ci * 4096 + j;
                let s = scalars[(e & !NEG) as usize];
                let (m, neg) = if e & NEG != 0 {
                    let mut m = modulus;
                    m.sub_with_borrow(&s);
                    (m, true)
                } else {
                    (s, false)
                };
                for w in 0..windows {
                    let d = booth_digit(&m, w, c) as i16;
                    // SAFETY: (w, k) is written by exactly this task.
                    unsafe { *ptr.get().add(w * n + k) = if neg { -d } else { d } };
                }
            }
        });
    }

    // With several windows, gather this class's points contiguously once so every
    // window pass streams them sequentially instead of striding the shared array.
    let gathered: Option<Vec<G::Affine>> = (windows > 1).then(|| {
        entries
            .par_iter()
            .map(|&e| bases[(e & !NEG) as usize])
            .collect()
    });

    let sums: Vec<G> = (0..windows * parts)
        .into_par_iter()
        .map(|t| {
            let (w, part) = (t / parts, t % parts);
            let lo = part * part_len;
            let hi = n.min(lo + part_len);
            let row = &digits[w * n..(w + 1) * n];
            let base_of = |k: usize| -> &G::Affine {
                match &gathered {
                    Some(g) => &g[k],
                    None => &bases[(entries[k] & !NEG) as usize],
                }
            };
            let nb = 1usize << (c - 1);
            // Batch-affine pays off once a task has many points per bucket.
            if BATCH_AFFINE.load(std::sync::atomic::Ordering::Relaxed) && hi - lo >= 4 * nb {
                let mut ab = AffineBuckets::<G>::new(nb);
                for (k, &d) in row.iter().enumerate().take(hi).skip(lo) {
                    if d == 0 {
                        continue;
                    }
                    let p = base_of(k);
                    if let Some((x, y)) = G::xy(p) {
                        ab.add(
                            (d.unsigned_abs() - 1) as u32,
                            p,
                            x,
                            if d < 0 { -y } else { y },
                            d < 0,
                        );
                    }
                }
                let (bx, by, used, side) = ab.finish();
                let mut running = G::ZERO_BUCKET;
                let mut res = G::ZERO_BUCKET;
                for j in (0..nb).rev() {
                    if used[j] {
                        running += &G::from_xy(bx[j], by[j]);
                    }
                    running += &side[j];
                    res += &running;
                }
                return res.into();
            }
            // Buckets in the curve's MSM bucket representation (XYZZ for short
            // Weierstrass: cheaper mixed additions than Jacobian).
            let mut buckets = vec![G::ZERO_BUCKET; nb];
            for k in lo..hi {
                let d = row[k];
                if d == 0 {
                    continue;
                }
                let base = match &gathered {
                    Some(g) => &g[k],
                    None => &bases[(entries[k] & !NEG) as usize],
                };
                let bucket = &mut buckets[(d.unsigned_abs() - 1) as usize];
                if d < 0 {
                    *bucket -= base;
                } else {
                    *bucket += base;
                }
            }
            // Σ_j (j+1)·bucket[j] via the running-sum trick (2·2^(c−1) adds).
            let mut running = G::ZERO_BUCKET;
            let mut res = G::ZERO_BUCKET;
            for b in buckets.iter().rev() {
                running += b;
                res += &running;
            }
            res.into()
        })
        .collect();

    let mut total = G::zero();
    for w in (0..windows).rev() {
        for _ in 0..c {
            total.double_in_place();
        }
        for part in 0..parts {
            total += sums[w * parts + part];
        }
    }
    total
}

/// Magnitude classes (upper bit bounds); class 0 is `±1`.
const CLASS_BITS: [usize; 6] = [1, 16, 32, 64, 128, 256];

/// `Σ sᵢ·Pᵢ` over the first `min(bases.len(), scalars.len())` pairs. Scalars are
/// arbitrary 256-bit integers (values ≥ r are handled, e.g. `r·P = O`).
pub fn msm<G: SwCurve>(bases: &[G::Affine], scalars: &[Scalar]) -> G {
    let n = bases.len().min(scalars.len());
    let (bases, scalars) = (&bases[..n], &scalars[..n]);
    assert!(n < NEG as usize, "MSM chunk too large");
    let modulus = Fr::MODULUS;

    // Partition by magnitude: each entry goes to the class of min(|s|, |r−s|).
    let classify = |i: usize| -> Option<(usize, u32)> {
        let s = &scalars[i];
        if s.is_zero() {
            return None;
        }
        let pos_bits = s.num_bits() as usize;
        let (bits, neg) = if pos_bits > 128 && *s < modulus {
            let mut m = modulus;
            m.sub_with_borrow(s);
            let nb = m.num_bits() as usize;
            if nb < pos_bits {
                (nb, true)
            } else {
                (pos_bits, false)
            }
        } else {
            (pos_bits, false)
        };
        if bits == 0 {
            // s == r (≡ 0): contributes nothing.
            return None;
        }
        let class = CLASS_BITS.iter().position(|&b| bits <= b).unwrap();
        Some((class, i as u32 | if neg { NEG } else { 0 }))
    };
    let classes: [Vec<u32>; 6] = (0..n)
        .into_par_iter()
        .fold(
            || std::array::from_fn(|_| Vec::new()),
            |mut acc: [Vec<u32>; 6], i| {
                if let Some((c, e)) = classify(i) {
                    acc[c].push(e);
                }
                acc
            },
        )
        .reduce(
            || std::array::from_fn(|_| Vec::new()),
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(b) {
                    if x.is_empty() {
                        *x = y;
                    } else {
                        x.extend(y);
                    }
                }
                a
            },
        );

    // ±1: plain (signed) additions.
    let unit: G = classes[0]
        .par_chunks(4096)
        .map(|es| {
            let mut acc = G::ZERO_BUCKET;
            for &e in es {
                let p = &bases[(e & !NEG) as usize];
                if e & NEG != 0 {
                    acc -= p;
                } else {
                    acc += p;
                }
            }
            acc.into()
        })
        .sum();
    let mut total = unit;
    for (class, entries) in classes.iter().enumerate().skip(1) {
        total += pippenger::<G>(bases, scalars, entries, CLASS_BITS[class]);
    }
    total
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Zero;

    #[test]
    fn booth_digits_reconstruct_scalar() {
        use ark_ff::UniformRand;
        let mut rng = rand::thread_rng();
        for c in [3usize, 7, 11, 16] {
            for _ in 0..50 {
                let s = Fr::rand(&mut rng).into_bigint();
                let windows = 257usize.div_ceil(c);
                // Σ d_w 2^(wc) mod r == s.
                let mut acc = Fr::zero();
                let two_c = Fr::from(1u64 << c);
                for w in (0..windows).rev() {
                    acc *= two_c;
                    let d = booth_digit(&s, w, c);
                    assert!(d.unsigned_abs() <= 1 << (c - 1));
                    acc += if d < 0 {
                        -Fr::from(d.unsigned_abs())
                    } else {
                        Fr::from(d as u64)
                    };
                }
                assert_eq!(acc.into_bigint(), s);
            }
        }
    }
}
