//! Blocked (four-step) radix-2 FFT over BN254 `Fr`, with tiled data movement.
//!
//! A length-`N = N1·N2` DFT is computed on the buffer viewed as an `N1 × N2`
//! row-major matrix, as `N1` + `N2` short sub-FFTs (each ~√N, cache-resident)
//! plus one element-wise twiddle pass (Bailey's algorithm):
//!
//! * [`Domain::fft_to_t`]   natural → **T-layout**: column FFTs (twiddle fused into
//!   the column scatter), then row FFTs.
//! * [`Domain::fft_from_t`] T-layout → natural: row FFTs, then column FFTs
//!   (twiddle fused into the column gather).
//!
//! In T-layout, position `k1·N2 + k2` holds index `k1 + N1·k2` — the transpose of
//! natural order. Every pointwise step of the Groth16 quotient computation is
//! order-agnostic, so the prover alternates `…_to_t` / `…_from_t` and never
//! transposes the full vector in place; the one transpose it needs is fused into the
//! final conversion of `h` ([`Domain::t_to_natural`]), which writes a buffer the MSM
//! needs anyway. Column passes move data in `tile`-column blocks (gather → FFT →
//! scatter), so reads and writes both touch whole cache lines; `tile` is the tuning
//! knob. Inverse transforms fold the `1/N` scale into the twiddle pass for free.
//!
//! Small domains (`log N < min_blocked_log`) use one plain radix-2 FFT (`N1 = 1`,
//! where T-layout *is* natural order).
//!
//! **Smooth domains.** BN254's `Fr` also has a subgroup of order 9, so domains of
//! size `3·2^k` and `9·2^k` exist ([`smooth_size`]); a circuit just past a power of
//! two then needs a domain up to 44% smaller. Such a domain keeps the row length
//! `N2` a power of two and puts the 3-factor in the column length `N1`, whose
//! sub-FFTs gain radix-3 layers ([`mixed_fft`]); everything else is unchanged.

use ark_bn254::Fr;
use ark_ff::{FftField, Field, One, PrimeField, Zero};
use rayon::prelude::*;

/// Tuning knobs for the blocked FFT.
#[derive(Clone, Copy, Debug)]
pub struct FftConfig {
    /// Columns moved per gather/scatter block (and the transpose tile edge).
    pub tile: usize,
    /// Domains below `2^min_blocked_log` use a single plain radix-2 FFT.
    pub min_blocked_log: u32,
}

impl Default for FftConfig {
    fn default() -> Self {
        // Tile 4 measured best for the coset transform and the transpose, both
        // natively (1 and 16 threads) and in single-threaded WASM (2^16–2^22);
        // below 2^12 the vector is cache-resident and plain radix-2 is as fast.
        FftConfig {
            tile: 4,
            min_blocked_log: 12,
        }
    }
}

/// Per-direction precomputation (forward uses ω, inverse ω⁻¹).
struct Tables {
    /// `ω_{N1}^j`, `j < N1`, for [`mixed_fft`]'s radix-3 layers (empty when `N1`
    /// is a power of two).
    tw_n1: Vec<Fr>,
    /// [`stage_table`] for the radix-2 part of `N1` (the column, or its leaves).
    st_n1: Vec<Fr>,
    /// [`stage_table`] for `N2` (rows).
    st_n2: Vec<Fr>,
    /// `ω_N^c`, `c < N2` — per-column generator of the Bailey twiddle `ω_N^{r·c}`.
    col_step: Vec<Fr>,
}

/// An evaluation domain `{ω^i}` of size `N` (ω = `Fr::get_root_of_unity(N)`),
/// matching arkworks' `Radix2EvaluationDomain` for `N = 2^k` and
/// `MixedRadixEvaluationDomain` for `N = 3·2^k, 9·2^k`.
pub struct Domain {
    pub n: usize,
    pub log_n: u32,
    pub n1: usize,
    pub n2: usize,
    pub tile: usize,
    size_inv: Fr,
    fwd: Tables,
    inv: Tables,
}

fn powers(base: Fr, count: usize) -> Vec<Fr> {
    let mut out = Vec::with_capacity(count);
    let mut cur = Fr::one();
    for _ in 0..count {
        out.push(cur);
        cur *= base;
    }
    out
}

impl Tables {
    fn new(root: Fr, n1: usize, n2: usize) -> Self {
        let n = (n1 * n2) as u64;
        let root_n1 = root.pow([n / n1 as u64]);
        let root_n2 = root.pow([n / n2 as u64]);
        let odd = n1 >> n1.trailing_zeros();
        Tables {
            tw_n1: if odd > 1 {
                powers(root_n1, n1)
            } else {
                Vec::new()
            },
            st_n1: stage_table(root_n1.pow([odd as u64]), n1 / odd),
            st_n2: stage_table(root_n2, n2),
            col_step: if n1 > 1 { powers(root, n2) } else { Vec::new() },
        }
    }
}

/// Radix-2 twiddles of a length-`len` DFT (`root = ω_len`) laid out by stage: the
/// stage with half-size `m` reads `ω_{2m}^j`, `j < m`, contiguously at `[m−1, 2m−1)`.
fn stage_table(root: Fr, len: usize) -> Vec<Fr> {
    let half = powers(root, len / 2);
    let mut out = Vec::with_capacity(len);
    let mut m = 1;
    while m < len {
        out.extend((0..m).map(|j| half[j * (len / (2 * m))]));
        m *= 2;
    }
    out
}

/// `i` bit-reversed in `log` bits.
fn bitrev(i: usize, log: u32) -> usize {
    i.reverse_bits().checked_shr(usize::BITS - log).unwrap_or(0)
}

/// In-place bit-reversal permutation.
fn bitrev_permute(a: &mut [Fr]) {
    let log = a.len().trailing_zeros();
    for i in 0..a.len() {
        let j = bitrev(i, log);
        if i < j {
            a.swap(i, j);
        }
    }
}

/// In-place radix-2 DFT, natural order in and out; `st` is the
/// [`stage_table`] for `a.len()`.
fn radix2_fft(a: &mut [Fr], st: &[Fr]) {
    bitrev_permute(a);
    dit(a, st);
}

/// In-place radix-2 DIF DFT, natural order in, **bit-reversed** out (`st`: the
/// [`stage_table`] for `a.len()`), so [`dit`] or [`bitrev`] reads it unpermuted.
fn dif(a: &mut [Fr], st: &[Fr]) {
    let mut m = a.len() / 2;
    while m >= 1 {
        let tw = &st[m - 1..2 * m - 1];
        for block in a.chunks_exact_mut(2 * m) {
            let (lo, hi) = block.split_at_mut(m);
            let t = hi[0];
            hi[0] = lo[0] - t;
            lo[0] += t;
            for ((x, y), w) in lo[1..].iter_mut().zip(&mut hi[1..]).zip(&tw[1..]) {
                let t = *x - *y;
                *x += *y;
                *y = t * w;
            }
        }
        m /= 2;
    }
}

/// In-place radix-2 DIT DFT, **bit-reversed** in, natural order out (`st`: the
/// [`stage_table`] for `a.len()`).
fn dit(a: &mut [Fr], st: &[Fr]) {
    let n = a.len();
    debug_assert!(n.is_power_of_two() && st.len() + 1 >= n);
    let mut m = 1;
    while m < n {
        let tw = &st[m - 1..2 * m - 1];
        for block in a.chunks_exact_mut(2 * m) {
            let (lo, hi) = block.split_at_mut(m);
            // j = 0: twiddle is 1.
            let t = hi[0];
            hi[0] = lo[0] - t;
            lo[0] += t;
            for ((x, y), w) in lo[1..].iter_mut().zip(&mut hi[1..]).zip(&tw[1..]) {
                let t = *y * w;
                *y = *x - t;
                *x += t;
            }
        }
        m *= 2;
    }
}

/// In-place DFT of length `L = 3^b·2^a`, `b ≥ 1`, natural order in and out, with
/// `ω_L^j = tw[j·s]` for `j < L`, `leaf` the `stage_table` for the radix-2
/// part of `L`, and `scratch.len() >= L`.
///
/// Radix-3 decimation in time: the three stride-3 subsequences are transformed
/// (recursively) into `scratch`, then combined — `X[k + i·L/3] = Σ_j ω_3^{ij}·
/// ω_L^{jk}·F_j[k]` — with 4 multiplications per 3 outputs. Radix-2 leaves are
/// gathered bit-reversed, so they run `dit` with no permutation.
pub fn mixed_fft(a: &mut [Fr], tw: &[Fr], s: usize, leaf_st: &[Fr], scratch: &mut [Fr]) {
    let n = a.len();
    let m = n / 3;
    let leaf = !m.is_multiple_of(3);
    let sc = &mut scratch[..n];
    for (j2, x) in a.as_chunks::<3>().0.iter().enumerate() {
        let p = if leaf {
            bitrev(j2, m.trailing_zeros())
        } else {
            j2
        };
        sc[p] = x[0];
        sc[m + p] = x[1];
        sc[2 * m + p] = x[2];
    }
    for blk in sc.chunks_exact_mut(m) {
        if leaf {
            dit(blk, leaf_st);
        } else {
            mixed_fft(blk, tw, 3 * s, leaf_st, &mut a[..m]);
        }
    }
    // ω₃ + ω₃² = −1, so X₁,₂ = x₀ − (x₁+x₂)/2 ± (ω₃−ω₃²)/2·(x₁−x₂).
    // 1/2 = (p+1)/2, without an inversion per call.
    let half = Fr::from(Fr::MODULUS_MINUS_ONE_DIV_TWO) + Fr::one();
    let w3 = tw[m * s];
    let c = (w3 - w3.square()) * half;
    let (f0, rest) = sc.split_at(m);
    let (f1, f2) = rest.split_at(m);
    let (o0, rest) = a.split_at_mut(m);
    let (o1, o2) = rest.split_at_mut(m);
    for k in 0..m {
        let x0 = f0[k];
        let x1 = f1[k] * tw[k * s];
        let x2 = f2[k] * tw[2 * k * s];
        let sum = x1 + x2;
        let d = (x1 - x2) * c;
        let mid = x0 - sum * half;
        o0[k] = x0 + sum;
        o1[k] = mid + d;
        o2[k] = mid - d;
    }
}

/// Which evaluation domains a key may be made for.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum DomainKind {
    /// `2^k` — what arkworks, snarkjs and rapidsnark provers expect.
    #[default]
    Radix2,
    /// The smallest of `2^k`, `3·2^k`, `9·2^k` ([`smooth_size`]). Only this
    /// crate's prover (and arkworks with a mixed-radix QAP reduction) can prove
    /// against such a key; the verifier is unaffected.
    Smooth,
}

impl DomainKind {
    /// Domain size for `min_size` points.
    pub fn size(self, min_size: usize) -> usize {
        match self {
            DomainKind::Radix2 => min_size.max(1).next_power_of_two(),
            DomainKind::Smooth => smooth_size(min_size),
        }
    }
}

/// The smallest domain size `≥ min_size` of the form `2^k`, `3·2^k` or `9·2^k`
/// (arkworks' `MixedRadixEvaluationDomain` rule for BN254).
pub fn smooth_size(min_size: usize) -> usize {
    [1usize, 3, 9]
        .iter()
        .map(|&q| {
            let mut r = q;
            while r < min_size {
                r *= 2;
            }
            r
        })
        .min()
        .unwrap()
}

/// Raw pointer shared across rayon tasks that write provably disjoint elements.
#[derive(Clone, Copy)]
struct SyncPtr(*mut Fr);
unsafe impl Send for SyncPtr {}
unsafe impl Sync for SyncPtr {}
impl SyncPtr {
    #[inline(always)]
    fn get(self) -> *mut Fr {
        self.0
    }
}

/// A row-local step of a transform chain (see [`Domain::rows_kernel`]).
#[derive(Clone, Copy, Debug)]
pub enum RowStage {
    /// Length-`N2` forward FFT of the row.
    Fft,
    /// Length-`N2` inverse FFT of the row (unscaled; `1/N` lives in the column pass).
    Ifft,
    /// Multiply by a constant.
    Scale(Fr),
    /// Multiply the element holding index `i` by `gⁱ` (T-layout indexing).
    Coset(Fr),
}

/// The two column passes a coset transform chain needs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ColOp {
    /// Inverse column FFTs, then twiddle × `1/N` (first pass of `…_to_t` inverse).
    InversePost,
    /// Twiddle, then forward column FFTs (last pass of `fft_from_t`).
    ForwardPre,
}

#[derive(Clone, Copy, PartialEq)]
enum Twiddle {
    /// Multiply by `scale·ω_N^{r·c}` while gathering (before the column FFTs).
    Pre,
    /// Multiply by `scale·ω_N^{r·c}` while scattering (after the column FFTs).
    Post,
}

impl Domain {
    /// The smallest radix-2 domain with at least `min_size` points (as arkworks).
    pub fn new(min_size: usize, cfg: FftConfig) -> Option<Self> {
        Self::with_size(min_size.max(1).next_power_of_two(), cfg)
    }

    /// The domain of exactly `n` points, `n = q·2^k` with `q ∈ {1, 3, 9}`.
    pub fn with_size(n: usize, cfg: FftConfig) -> Option<Self> {
        let q = [9, 3, 1].into_iter().find(|q| n.is_multiple_of(*q))?;
        let k = (n / q).trailing_zeros();
        if n != q << k {
            return None;
        }
        let (n1, n2) = if q == 1 && k < cfg.min_blocked_log {
            (1, n)
        } else if k < cfg.min_blocked_log {
            (q, 1 << k)
        } else {
            // Rows (contiguous, radix-2) get the larger half of the 2-part.
            let r = k - k / 2;
            (q << (k / 2), 1 << r)
        };
        Self::with_split(n1, n2, cfg.tile)
    }

    /// The domain of `n1·n2` points as an `n1 × n2` four-step (`n2` a power of
    /// two; `n1 = 1` is the plain radix-2 path). Workers rebuild the coordinator's
    /// domain from its split.
    pub fn with_split(n1: usize, n2: usize, tile: usize) -> Option<Self> {
        let odd = n1.checked_shr(n1.trailing_zeros()).unwrap_or(0);
        if !n2.is_power_of_two() || ![1, 3, 9].contains(&odd) {
            return None;
        }
        let n = n1.checked_mul(n2)?;
        let omega = Fr::get_root_of_unity(n as u64)?;
        let omega_inv = omega.inverse()?;
        Some(Domain {
            n,
            log_n: n.ilog2(),
            n1,
            n2,
            tile: tile.clamp(1, n2),
            size_inv: Fr::from(n as u64).inverse()?,
            fwd: Tables::new(omega, n1, n2),
            inv: Tables::new(omega_inv, n1, n2),
        })
    }

    /// Whether this domain runs the four-step path.
    pub fn is_blocked(&self) -> bool {
        self.n1 > 1
    }

    /// Column FFTs on global columns `c0..c0+b`, the first `b` elements of each
    /// of `N1` rows at `base` (row stride `stride`): gather them column-major into
    /// `cols` (one cache-line-friendly run per row), FFT, scatter back. The Bailey twiddle
    /// `scale·ω_N^{r·c}` is applied while gathering ([`Twiddle::Pre`]) or
    /// scattering ([`Twiddle::Post`]). Radix-2 columns run [`dif`], so the scatter
    /// reads them bit-reversed.
    ///
    /// # Safety
    /// `base + r·stride .. + b` is valid for every row `r < N1`, and no one else
    /// accesses it during the call.
    unsafe fn col_tile(
        &self,
        base: *mut Fr,
        stride: usize,
        c0: usize,
        b: usize,
        cols: &mut [Fr],
        (t, tw, scale): (&Tables, Twiddle, Fr),
    ) {
        let n1 = self.n1;
        let radix2 = n1.is_power_of_two();
        let log = n1.trailing_zeros();
        let step = &t.col_step[c0..c0 + b];
        let mut cur = vec![scale; b];
        for r in 0..n1 {
            // SAFETY: row r's `b` elements, ours alone (caller contract).
            let row = unsafe { std::slice::from_raw_parts(base.add(r * stride), b) };
            for j in 0..b {
                let mut v = row[j];
                if tw == Twiddle::Pre {
                    v *= cur[j];
                    cur[j] *= step[j];
                }
                cols[j * n1 + r] = v;
            }
        }
        let mut scratch = Vec::new();
        for col in cols[..b * n1].chunks_exact_mut(n1) {
            if radix2 {
                dif(col, &t.st_n1);
            } else {
                scratch.resize(n1, Fr::zero());
                mixed_fft(col, &t.tw_n1, 1, &t.st_n1, &mut scratch);
            }
        }
        for r in 0..n1 {
            let p = if radix2 { bitrev(r, log) } else { r };
            // SAFETY: as above.
            let row = unsafe { std::slice::from_raw_parts_mut(base.add(r * stride), b) };
            for j in 0..b {
                let mut v = cols[j * n1 + p];
                if tw == Twiddle::Post {
                    v *= cur[j];
                    cur[j] *= step[j];
                }
                row[j] = v;
            }
        }
    }

    /// Column FFTs, `tile` columns per task ([`col_tile`](Self::col_tile)).
    fn col_pass(&self, buf: &mut [Fr], t: &Tables, tw: Twiddle, scale: Fr) {
        let (n1, n2, tile) = (self.n1, self.n2, self.tile);
        let ptr = SyncPtr(buf.as_mut_ptr());
        (0..n2.div_ceil(tile)).into_par_iter().for_each_init(
            || vec![Fr::zero(); n1 * tile],
            |cols, bt| {
                let (c0, b) = (bt * tile, tile.min(n2 - bt * tile));
                // SAFETY: task `bt` alone touches columns c0..c0+b of each row;
                // `buf` outlives the parallel loop.
                unsafe { self.col_tile(ptr.get().add(c0), n2, c0, b, cols, (t, tw, scale)) }
            },
        );
    }

    /// Apply `stages` to each row of `rows` (whole rows of length `N2`; the first
    /// is global row `first_row`). All row-local work of a transform chain fuses
    /// into one sweep.
    pub fn rows_kernel(&self, rows: &mut [Fr], first_row: usize, stages: &[RowStage]) {
        let n2 = self.n2;
        assert_eq!(rows.len() % n2, 0);
        // Each FFT flips the row between natural and bit-reversed order (DIF on
        // natural, DIT on bit-reversed), so a chain permutes at most once, at the
        // end. A coset stage reads its exponents in the row's current order:
        // position k2 holds index k1 + N1·k2.
        let coset_pows: Vec<Vec<Fr>> = (0..stages.len())
            .map(|i| match stages[i] {
                RowStage::Coset(g) => {
                    let mut p = powers(g.pow([self.n1 as u64]), n2);
                    let ffts = stages[..i]
                        .iter()
                        .filter(|s| matches!(s, RowStage::Fft | RowStage::Ifft));
                    if ffts.count() % 2 == 1 {
                        bitrev_permute(&mut p);
                    }
                    p
                }
                _ => Vec::new(),
            })
            .collect();
        for (i, row) in rows.chunks_exact_mut(n2).enumerate() {
            let mut rev = false;
            for (st, pows) in stages.iter().zip(&coset_pows) {
                match *st {
                    RowStage::Fft | RowStage::Ifft => {
                        let t = if matches!(st, RowStage::Fft) {
                            &self.fwd
                        } else {
                            &self.inv
                        };
                        if rev {
                            dit(row, &t.st_n2);
                        } else {
                            dif(row, &t.st_n2);
                        }
                        rev = !rev;
                    }
                    RowStage::Scale(k) => row.iter_mut().for_each(|v| *v *= k),
                    RowStage::Coset(g) => {
                        let c = g.pow([(first_row + i) as u64]);
                        for (v, p) in row.iter_mut().zip(pows) {
                            *v *= c * p;
                        }
                    }
                }
            }
            if rev {
                bitrev_permute(row);
            }
        }
    }

    /// Column kernel for a block of `b` columns starting at `c0`, given
    /// **row-major** (`N1 × b`, as a worker receives a gathered tile).
    pub fn cols_kernel(&self, block: &mut [Fr], c0: usize, op: ColOp) {
        let b = block.len() / self.n1;
        let mut cols = vec![Fr::zero(); block.len()];
        // SAFETY: `block` is exclusively borrowed and holds N1 rows of b elements.
        unsafe { self.col_tile(block.as_mut_ptr(), b, c0, b, &mut cols, self.col_op(op)) }
    }

    fn col_op(&self, op: ColOp) -> (&Tables, Twiddle, Fr) {
        match op {
            ColOp::InversePost => (&self.inv, Twiddle::Post, self.size_inv),
            ColOp::ForwardPre => (&self.fwd, Twiddle::Pre, Fr::one()),
        }
    }

    fn rows_pass(&self, buf: &mut [Fr], stages: &[RowStage]) {
        let n2 = self.n2;
        // A few rows per task keeps scheduling overhead negligible.
        let per = (1usize << 15).div_ceil(n2).max(1);
        buf.par_chunks_mut(n2 * per)
            .enumerate()
            .for_each(|(i, rows)| self.rows_kernel(rows, i * per, stages));
    }

    /// Evaluations on the domain (natural) → evaluations on the coset `g·{ωⁱ}`
    /// (natural): `iFFT → ×gⁱ → FFT` as three sweeps (column pass, one fused row
    /// pass, column pass).
    pub fn to_coset(&self, buf: &mut [Fr], g: Fr) {
        assert_eq!(buf.len(), self.n);
        if !self.is_blocked() {
            self.ifft_to_t(buf);
            self.coset_scale_t(buf, g);
            return self.fft_from_t(buf);
        }
        let (t, tw, k) = self.col_op(ColOp::InversePost);
        self.col_pass(buf, t, tw, k);
        self.rows_pass(buf, &[RowStage::Ifft, RowStage::Coset(g), RowStage::Fft]);
        let (t, tw, k) = self.col_op(ColOp::ForwardPre);
        self.col_pass(buf, t, tw, k);
    }

    /// Coset evaluations (natural) → coefficients in **T-layout**:
    /// `iFFT → ×g⁻ⁱ` as two sweeps.
    pub fn from_coset_to_t(&self, buf: &mut [Fr], g_inv: Fr) {
        assert_eq!(buf.len(), self.n);
        if !self.is_blocked() {
            self.ifft_to_t(buf);
            return self.coset_scale_t(buf, g_inv);
        }
        let (t, tw, k) = self.col_op(ColOp::InversePost);
        self.col_pass(buf, t, tw, k);
        self.rows_pass(buf, &[RowStage::Ifft, RowStage::Coset(g_inv)]);
    }

    fn scale(&self, buf: &mut [Fr], k: Fr) {
        buf.par_chunks_mut(1 << 12).for_each(|c| {
            for v in c {
                *v *= k;
            }
        });
    }

    /// DFT, natural order → T-layout.
    pub fn fft_to_t(&self, buf: &mut [Fr]) {
        assert_eq!(buf.len(), self.n);
        if !self.is_blocked() {
            return radix2_fft(buf, &self.fwd.st_n2);
        }
        self.col_pass(buf, &self.fwd, Twiddle::Post, Fr::one());
        self.rows_pass(buf, &[RowStage::Fft]);
    }

    /// DFT, T-layout → natural order.
    pub fn fft_from_t(&self, buf: &mut [Fr]) {
        assert_eq!(buf.len(), self.n);
        if !self.is_blocked() {
            return radix2_fft(buf, &self.fwd.st_n2);
        }
        self.rows_pass(buf, &[RowStage::Fft]);
        self.col_pass(buf, &self.fwd, Twiddle::Pre, Fr::one());
    }

    /// Inverse DFT (incl. `1/N`), natural order → T-layout.
    pub fn ifft_to_t(&self, buf: &mut [Fr]) {
        assert_eq!(buf.len(), self.n);
        if !self.is_blocked() {
            radix2_fft(buf, &self.inv.st_n2);
            return self.scale(buf, self.size_inv);
        }
        self.col_pass(buf, &self.inv, Twiddle::Post, self.size_inv);
        self.rows_pass(buf, &[RowStage::Ifft]);
    }

    /// Inverse DFT (incl. `1/N`), T-layout → natural order.
    pub fn ifft_from_t(&self, buf: &mut [Fr]) {
        assert_eq!(buf.len(), self.n);
        if !self.is_blocked() {
            radix2_fft(buf, &self.inv.st_n2);
            return self.scale(buf, self.size_inv);
        }
        self.rows_pass(buf, &[RowStage::Ifft]);
        self.col_pass(buf, &self.inv, Twiddle::Pre, self.size_inv);
    }

    /// Multiply the element holding index `i` by `g^i`, for a T-layout buffer.
    pub fn coset_scale_t(&self, buf: &mut [Fr], g: Fr) {
        let step = g.pow([self.n1 as u64]);
        buf.par_chunks_mut(self.n2)
            .enumerate()
            .for_each(|(k1, row)| {
                let mut cur = g.pow([k1 as u64]);
                for v in row {
                    *v *= cur;
                    cur *= step;
                }
            });
    }

    /// Reorder a T-layout vector to natural order through `f`, out of place, with a
    /// tiled transpose (reads one tile-row run per source row, writes `tile` output
    /// rows that stay cache-resident).
    pub fn t_to_natural<U: Send + Default + Clone>(
        &self,
        src: &[Fr],
        f: impl Fn(&Fr) -> U + Sync,
    ) -> Vec<U> {
        assert_eq!(src.len(), self.n);
        let mut dst = vec![U::default(); self.n];
        transpose_map(src, &mut dst, self.n1, self.n2, self.tile, f);
        dst
    }

    /// Natural-order DFT (four-step + out-of-place tiled transpose).
    pub fn fft(&self, buf: &mut Vec<Fr>) {
        self.fft_to_t(buf);
        if self.is_blocked() {
            *buf = self.t_to_natural(buf, |x| *x);
        }
    }

    /// Natural-order inverse DFT.
    pub fn ifft(&self, buf: &mut Vec<Fr>) {
        self.ifft_to_t(buf);
        if self.is_blocked() {
            *buf = self.t_to_natural(buf, |x| *x);
        }
    }
}

/// `dst[c·rows + r] = f(src[r·cols + c])` — transpose a `rows × cols` row-major
/// matrix into `cols × rows`, `tile × tile` blocks at a time, parallel over output
/// row-blocks.
pub fn transpose_map<T: Sync, U: Send>(
    src: &[T],
    dst: &mut [U],
    rows: usize,
    cols: usize,
    tile: usize,
    f: impl Fn(&T) -> U + Sync,
) {
    assert_eq!(src.len(), rows * cols);
    assert_eq!(dst.len(), rows * cols);
    let tile = tile.max(1);
    dst.par_chunks_mut(tile * rows)
        .enumerate()
        .for_each(|(bc, out)| {
            let c0 = bc * tile;
            let cn = out.len() / rows;
            for r0 in (0..rows).step_by(tile) {
                let rn = tile.min(rows - r0);
                for r in r0..r0 + rn {
                    let srow = &src[r * cols + c0..r * cols + c0 + cn];
                    for (dc, v) in srow.iter().enumerate() {
                        out[dc * rows + r] = f(v);
                    }
                }
            }
        });
}
