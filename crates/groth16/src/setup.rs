//! Streaming Groth16 key generation: the constraint system is never
//! materialized, and the proving key is written to its file vector by vector.
//!
//! * [`dev_setup`] — the trusted-dealer setup (toxic waste sampled locally),
//!   **byte-identical** to `ark-groth16`'s `circuit_specific_setup` for the same
//!   RNG: same draws, same Lagrange/vanishing evaluations, same batch
//!   multiplications. With [`DomainKind::Smooth`] it may pick a `3·2^k`/`9·2^k`
//!   domain, matching `circuit_specific_setup` with a mixed-radix QAP reduction. Each variable's QAP evaluations come from one transposed
//!   pass over the rows ([`ConstraintSource::transpose_eval`]).
//! * [`phase2_setup`] — phase 2 from a Powers-of-Tau transcript (radix-2
//!   domains only: the transcript's Lagrange bases are for `2^k` domains), byte-identical
//!   to `xark_backend::ptau::setup_from_ptau` for the same seed. Its per-variable
//!   group sums read the matrix columns from a compact column index built by
//!   streaming the rows (`nnz × 36 B`), not from a synthesized constraint system.
//!
//! Output is the standard `pk.bin` (`XKPK` header + ark-groth16's
//! `CanonicalSerialize` layout), so every existing reader loads it.

use std::io::Write;
use std::sync::atomic::{AtomicU32, Ordering};

use crate::types::VerifyingKey;
use ark_bn254::{Bn254, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::scalar_mul::BatchMulPreprocessing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, One, UniformRand, Zero};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, MixedRadixEvaluationDomain};
use ark_serialize::{CanonicalSerialize, Compress};
use rand::{RngCore, SeedableRng};
use rayon::prelude::*;

use crate::fft::DomainKind;
use crate::r1cs::{ConstraintSource, RowChunk};

/// Errors from key generation.
#[derive(Debug)]
pub enum SetupError {
    Io(std::io::Error),
    Serialize(ark_serialize::SerializationError),
    /// The circuit needs a domain larger than BN254's 2-adic subgroup.
    DomainTooLarge(usize),
}

impl std::fmt::Display for SetupError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SetupError::Io(e) => write!(f, "writing proving key: {e}"),
            SetupError::Serialize(e) => write!(f, "serializing proving key: {e}"),
            SetupError::DomainTooLarge(n) => write!(f, "no evaluation domain of size {n}"),
        }
    }
}

impl std::error::Error for SetupError {}

impl From<std::io::Error> for SetupError {
    fn from(e: std::io::Error) -> Self {
        SetupError::Io(e)
    }
}

impl From<ark_serialize::SerializationError> for SetupError {
    fn from(e: ark_serialize::SerializationError) -> Self {
        SetupError::Serialize(e)
    }
}

/// Points per chunk when computing and writing a key vector.
const CHUNK: usize = 1 << 18;

/// Writes `pk.bin` in order: header, `vk`, `β₁`, `δ₁`, then each vector as
/// `u64 len ‖ points`.
struct PkWriter<W: Write> {
    w: W,
    c: Compress,
}

impl<W: Write> PkWriter<W> {
    /// Starts with the v2 header ([`KeyFormat`](crate::pk::KeyFormat)), which
    /// records the QAP domain size.
    fn new(mut w: W, c: Compress, domain: usize) -> Result<Self, SetupError> {
        w.write_all(&crate::pk::KeyFormat::header(
            matches!(c, Compress::Yes),
            Some(domain),
        ))?;
        Ok(PkWriter { w, c })
    }
    fn put<T: CanonicalSerialize>(&mut self, v: &T) -> Result<(), SetupError> {
        v.serialize_with_mode(&mut self.w, self.c)?;
        Ok(())
    }
    /// A vector of `len` points produced chunk by chunk by `f(range)`.
    fn vec<A: CanonicalSerialize>(
        &mut self,
        len: usize,
        mut f: impl FnMut(std::ops::Range<usize>) -> Vec<A>,
    ) -> Result<(), SetupError> {
        self.put(&(len as u64))?;
        let mut i = 0;
        while i < len {
            let r = i..len.min(i + CHUNK);
            for p in f(r.clone()) {
                self.put(&p)?;
            }
            i = r.end;
        }
        Ok(())
    }
    fn finish(mut self) -> Result<(), SetupError> {
        self.w.flush()?;
        Ok(())
    }
}

/// `t` (drawn from `rng` outside the domain), `Z(t)`, the domain size and all
/// Lagrange basis values at `t` — as ark-groth16's generator computes them.
fn qap_point<D: EvaluationDomain<Fr>>(
    min: usize,
    rng: &mut impl RngCore,
) -> Result<(Fr, Fr, usize, Vec<Fr>), SetupError> {
    let domain = D::new(min).ok_or(SetupError::DomainTooLarge(min))?;
    let t = domain.sample_element_outside_domain(rng);
    let zt = domain.evaluate_vanishing_polynomial(t);
    Ok((
        t,
        zt,
        domain.size(),
        domain.evaluate_all_lagrange_coefficients(t),
    ))
}

/// Trusted-dealer Groth16 setup for `src`, streaming the proving key into `out`.
/// Byte-identical to `Groth16::<Bn254>::circuit_specific_setup` (as written by
/// `Groth16Keys::write_proving_key_mode`) for the same RNG state — with a
/// mixed-radix QAP reduction when `domain` picks a `3·2^k`/`9·2^k` size.
pub fn dev_setup<S, R, W>(
    src: &S,
    rng: &mut R,
    out: W,
    compress: Compress,
    domain: DomainKind,
) -> Result<VerifyingKey<Bn254>, SetupError>
where
    S: ConstraintSource + ?Sized,
    R: RngCore,
    W: Write,
{
    let m = src.num_constraints();
    let layout = src.layout();
    let ninst = layout.num_instance();
    let nv = layout.num_vars();
    let qap_nv = nv - 1;

    // Same draws, in the same order, as ark-groth16's generator.
    let alpha = Fr::rand(rng);
    let beta = Fr::rand(rng);
    let gamma = Fr::rand(rng);
    let delta = Fr::rand(rng);
    let g1 = G1Projective::rand(rng);
    let g2 = G2Projective::rand(rng);
    let size = domain.size(m + ninst);
    let (t, zt, m_raw, u) = if size.is_power_of_two() {
        qap_point::<GeneralEvaluationDomain<Fr>>(m + ninst, rng)?
    } else {
        qap_point::<MixedRadixEvaluationDomain<Fr>>(size, rng)?
    };

    // a_j(t), b_j(t), c_j(t) for every variable: one transposed pass with the
    // Lagrange weights, plus libsnark's instance rows on `A`.
    let (mut a, mut b, mut c) = (
        vec![Fr::zero(); nv],
        vec![Fr::zero(); nv],
        vec![Fr::zero(); nv],
    );
    a[..ninst].copy_from_slice(&u[m..m + ninst]);
    src.transpose_eval(&u[..m], [&mut a, &mut b, &mut c]);
    drop(u);

    let non_zero_a = a[..qap_nv].iter().filter(|x| !x.is_zero()).count();
    let non_zero_b = b[..qap_nv].iter().filter(|x| !x.is_zero()).count();
    let gamma_inv = gamma.inverse().unwrap();
    let delta_inv = delta.inverse().unwrap();
    let abc = |i: usize| beta * a[i] + alpha * b[i] + c[i];
    let gamma_abc: Vec<Fr> = (0..ninst).map(|i| abc(i) * gamma_inv).collect();
    let l: Vec<Fr> = (ninst..nv)
        .into_par_iter()
        .map(|i| abc(i) * delta_inv)
        .collect();
    drop(c);

    let num_scalars = non_zero_a + non_zero_b + qap_nv + m_raw + 1;
    let g1_table = BatchMulPreprocessing::new(g1, num_scalars);
    let vk = VerifyingKey::<Bn254> {
        alpha_g1: (g1 * alpha).into_affine(),
        beta_g2: (g2 * beta).into_affine(),
        gamma_g2: (g2 * gamma).into_affine(),
        delta_g2: (g2 * delta).into_affine(),
        gamma_abc_g1: g1_table.batch_mul(&gamma_abc),
    };

    let mut w = PkWriter::new(out, compress, m_raw)?;
    w.put(&vk)?;
    w.put(&(g1 * beta).into_affine())?;
    w.put(&(g1 * delta).into_affine())?;
    w.vec(nv, |r| g1_table.batch_mul(&a[r]))?;
    drop(a);
    w.vec(nv, |r| g1_table.batch_mul(&b[r]))?;
    {
        let g2_table = BatchMulPreprocessing::new(g2, non_zero_b);
        w.vec(nv, |r| g2_table.batch_mul(&b[r]))?;
    }
    drop(b);
    // h_i = zt·δ⁻¹·tⁱ, i < m_raw − 1.
    let h0 = zt * delta_inv;
    w.vec(m_raw - 1, |r| {
        let start = h0 * t.pow([r.start as u64]);
        let sc: Vec<Fr> = r
            .clone()
            .scan(start, |acc, _| {
                let v = *acc;
                *acc *= t;
                Some(v)
            })
            .collect();
        g1_table.batch_mul(&sc)
    })?;
    w.vec(nv - ninst, |r| g1_table.batch_mul(&l[r]))?;
    w.finish()?;
    Ok(vk)
}

/// The Powers-of-Tau elements phase 2 consumes (borrowed from a parsed
/// transcript; validate it first with `xark_backend::ptau::validate_for_circuit`).
pub struct PtauPowers<'a> {
    pub tau_g1: &'a [G1Affine],
    pub tau_g2: &'a [G2Affine],
    pub alpha_tau_g1: &'a [G1Affine],
    pub beta_tau_g1: &'a [G1Affine],
    pub beta_g2: G2Affine,
}

/// Compressed sparse columns of the three matrices, built by streaming rows.
struct Columns {
    /// `start[m][p]..start[m][p+1]` indexes `rows/coeffs[m]` for position `p`.
    start: [Vec<u32>; 3],
    rows: [Vec<u32>; 3],
    coeffs: [Vec<Fr>; 3],
}

impl Columns {
    fn build<S: ConstraintSource + ?Sized>(src: &S) -> Self {
        let nv = src.layout().num_vars();
        let windows = src.windows(1 << 14);
        let counts: [Vec<AtomicU32>; 3] =
            std::array::from_fn(|_| (0..nv + 1).map(|_| AtomicU32::new(0)).collect());
        let each = |f: &(dyn Fn(usize, usize, u32, Fr) + Sync)| {
            windows
                .par_iter()
                .for_each_init(RowChunk::default, |ch, w| {
                    src.expand(w, ch);
                    for i in 0..ch.rows() {
                        for m in 0..3 {
                            let (cols, ks) = ch.terms(i, m);
                            for (&c, k) in cols.iter().zip(ks) {
                                f(m, c as usize, (w.rows.start + i) as u32, *k);
                            }
                        }
                    }
                })
        };
        each(&|m, p, _, _| {
            counts[m][p + 1].fetch_add(1, Ordering::Relaxed);
        });
        let start: [Vec<u32>; 3] = std::array::from_fn(|m| {
            let mut acc = 0u32;
            counts[m]
                .iter()
                .map(|c| {
                    acc += c.load(Ordering::Relaxed);
                    acc
                })
                .collect()
        });
        let cursor: [Vec<AtomicU32>; 3] =
            std::array::from_fn(|m| start[m].iter().map(|&s| AtomicU32::new(s)).collect());
        let nnz: [usize; 3] = std::array::from_fn(|m| *start[m].last().unwrap() as usize);
        let rows: [Vec<AtomicU32>; 3] =
            std::array::from_fn(|m| (0..nnz[m]).map(|_| AtomicU32::new(0)).collect());
        let mut coeffs: [Vec<Fr>; 3] = std::array::from_fn(|m| vec![Fr::zero(); nnz[m]]);
        {
            let cptr: [SyncFr; 3] = std::array::from_fn(|m| SyncFr(coeffs[m].as_mut_ptr()));
            each(&|m, p, row, k| {
                let at = cursor[m][p].fetch_add(1, Ordering::Relaxed) as usize;
                rows[m][at].store(row, Ordering::Relaxed);
                // SAFETY: `at` is claimed exactly once via the atomic cursor.
                unsafe { *cptr[m].get().add(at) = k };
            });
        }
        let mut rows: [Vec<u32>; 3] =
            rows.map(|v| v.into_iter().map(AtomicU32::into_inner).collect());
        // The parallel fill scrambles each column's order; restore increasing rows
        // so the per-variable sums walk the Lagrange tables sequentially.
        for m in 0..3 {
            let (st, rs, ks) = (&start[m], &mut rows[m], &mut coeffs[m]);
            let mut segs: Vec<(&mut [u32], &mut [Fr])> = Vec::with_capacity(st.len());
            let (mut rr, mut kk) = (rs.as_mut_slice(), ks.as_mut_slice());
            for w in st.windows(2) {
                let len = (w[1] - w[0]) as usize;
                let (r0, r1) = rr.split_at_mut(len);
                let (k0, k1) = kk.split_at_mut(len);
                segs.push((r0, k0));
                rr = r1;
                kk = k1;
            }
            segs.par_iter_mut().for_each(|(r, k)| {
                if r.windows(2).any(|w| w[0] > w[1]) {
                    let mut idx: Vec<usize> = (0..r.len()).collect();
                    idx.sort_unstable_by_key(|&i| r[i]);
                    let (r2, k2): (Vec<u32>, Vec<Fr>) = idx.iter().map(|&i| (r[i], k[i])).unzip();
                    r.copy_from_slice(&r2);
                    k.copy_from_slice(&k2);
                }
            });
        }
        Columns {
            start,
            rows,
            coeffs,
        }
    }

    fn col(&self, m: usize, p: usize) -> impl Iterator<Item = (usize, &Fr)> {
        let r = self.start[m][p] as usize..self.start[m][p + 1] as usize;
        self.rows[m][r.clone()]
            .iter()
            .map(|&x| x as usize)
            .zip(&self.coeffs[m][r])
    }
}

#[derive(Clone, Copy)]
struct SyncFr(*mut Fr);
unsafe impl Send for SyncFr {}
unsafe impl Sync for SyncFr {}
impl SyncFr {
    fn get(self) -> *mut Fr {
        self.0
    }
}

fn sample_nonzero_fr(rng: &mut impl RngCore) -> Fr {
    loop {
        let mut bytes = [0u8; 32];
        rng.fill_bytes(&mut bytes);
        let c = Fr::from_random_bytes(&bytes).unwrap_or_else(Fr::zero);
        if !c.is_zero() {
            return c;
        }
    }
}

/// `Σ_rows coeff · λ[row]` per position for matrix `m` (±1 as plain add/sub).
fn column_sums<P: CurveGroup<ScalarField = Fr>>(
    cols: &Columns,
    m: usize,
    nv: usize,
    lambda: &[P],
) -> Vec<P> {
    let neg_one = -Fr::one();
    (0..nv)
        .into_par_iter()
        .map(|p| {
            let mut acc = P::zero();
            for (row, k) in cols.col(m, p) {
                let l = lambda[row];
                if k.is_one() {
                    acc += l;
                } else if *k == neg_one {
                    acc -= l;
                } else {
                    acc += l * *k;
                }
            }
            acc
        })
        .collect()
}

fn lagrange_g1(domain: &GeneralEvaluationDomain<Fr>, pts: &[G1Affine]) -> Vec<G1Projective> {
    let mut v: Vec<G1Projective> = pts.iter().map(|p| p.into_group()).collect();
    domain.ifft_in_place(&mut v);
    v
}

/// Phase 2 from Powers-of-Tau elements, streaming the proving key into `out`.
/// `γ, δ` come from `seed` exactly as in `xark_backend::ptau::setup_from_ptau`,
/// whose output this matches byte for byte.
pub fn phase2_setup<S, W>(
    src: &S,
    p: &PtauPowers,
    seed: &[u8; 32],
    out: W,
    compress: Compress,
) -> Result<VerifyingKey<Bn254>, SetupError>
where
    S: ConstraintSource + ?Sized,
    W: Write,
{
    let m = src.num_constraints();
    let ninst = src.layout().num_instance();
    let nv = src.layout().num_vars();
    let domain = GeneralEvaluationDomain::<Fr>::new(m + ninst)
        .ok_or(SetupError::DomainTooLarge(m + ninst))?;
    let n = domain.size();
    let cols = Columns::build(src);

    let mut rng = rand_chacha::ChaCha20Rng::from_seed(*seed);
    let gamma = sample_nonzero_fr(&mut rng);
    let delta = sample_nonzero_fr(&mut rng);
    let (gamma_inv, delta_inv) = (gamma.inverse().unwrap(), delta.inverse().unwrap());

    // combined = β·a + α·b + w per variable (each λ table built, used, dropped).
    let mut combined = {
        let lam_beta = lagrange_g1(&domain, &p.beta_tau_g1[..n]);
        let mut beta_a = column_sums(&cols, 0, nv, &lam_beta);
        for i in 0..ninst {
            beta_a[i] += lam_beta[m + i];
        }
        beta_a
    };
    {
        let lam_alpha = lagrange_g1(&domain, &p.alpha_tau_g1[..n]);
        let alpha_b = column_sums(&cols, 1, nv, &lam_alpha);
        combined
            .par_iter_mut()
            .zip(alpha_b)
            .for_each(|(x, y)| *x += y);
    }
    let lam = lagrange_g1(&domain, &p.tau_g1[..n]);
    {
        let w = column_sums(&cols, 2, nv, &lam);
        combined.par_iter_mut().zip(w).for_each(|(x, y)| *x += y);
    }
    let scale = |v: &[G1Projective], k: Fr| -> Vec<G1Affine> {
        let s: Vec<G1Projective> = v.par_iter().map(|c| *c * k).collect();
        G1Projective::normalize_batch(&s)
    };

    let g1 = G1Affine::generator();
    let g2 = G2Affine::generator();
    let vk = VerifyingKey::<Bn254> {
        alpha_g1: p.alpha_tau_g1[0],
        beta_g2: p.beta_g2,
        gamma_g2: (g2 * gamma).into_affine(),
        delta_g2: (g2 * delta).into_affine(),
        gamma_abc_g1: scale(&combined[..ninst], gamma_inv),
    };

    let mut w = PkWriter::new(out, compress, n)?;
    w.put(&vk)?;
    w.put(&p.beta_tau_g1[0])?;
    w.put(&(g1 * delta).into_affine())?;
    // A (with libsnark's instance rows), B in G1, B in G2.
    {
        let mut a = column_sums(&cols, 0, nv, &lam);
        for i in 0..ninst {
            a[i] += lam[m + i];
        }
        let a = G1Projective::normalize_batch(&a);
        w.vec(nv, |r| a[r].to_vec())?;
        let b = G1Projective::normalize_batch(&column_sums(&cols, 1, nv, &lam));
        w.vec(nv, |r| b[r].to_vec())?;
    }
    drop(lam);
    {
        let mut lam2: Vec<G2Projective> = p.tau_g2[..n].iter().map(|q| q.into_group()).collect();
        domain.ifft_in_place(&mut lam2);
        let b2 = G2Projective::normalize_batch(&column_sums(&cols, 1, nv, &lam2));
        w.vec(nv, |r| b2[r].to_vec())?;
    }
    drop(cols);
    // h_k = δ⁻¹·(τ^{n+k} − τ^k)·G1, k < n − 1.
    w.vec(n - 1, |r| {
        let v: Vec<G1Projective> = r
            .into_par_iter()
            .map(|k| (p.tau_g1[n + k].into_group() - p.tau_g1[k].into_group()) * delta_inv)
            .collect();
        G1Projective::normalize_batch(&v)
    })?;
    let l = scale(&combined[ninst..], delta_inv);
    w.vec(nv - ninst, |r| l[r].to_vec())?;
    w.finish()?;
    Ok(vk)
}
