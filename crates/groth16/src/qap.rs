//! R1CS → QAP witness map: the quotient `h = (A·B − C) / Z` coefficients,
//! bit-identical to arkworks' `LibsnarkReduction::witness_map`, computed from
//! streamed rows with the blocked FFT.
//!
//! Arkworks' domain is `num_constraints + num_instance` (rounded up to 2^k, or to
//! `3·2^k`/`9·2^k` for keys made with a smooth domain — the key's `H` length says
//! which, see [`key_domain`]): rows
//! `0..m` hold `⟨A_i,z⟩`, `⟨B_i,z⟩`, `⟨C_i,z⟩`, and `A` additionally carries the
//! instance assignment at rows `m..m+ℓ` (libsnark's input-consistency rows).
//!
//! Peak memory is two domain-sized vectors (`A`+`B`, then `AB`+`C`), or one with
//! a [`Spill`]; rows are re-streamed instead of being held.

use ark_bn254::Fr;
use ark_ff::{FftField, Field, PrimeField, Zero};
use rayon::prelude::*;

use crate::accel::{Accelerator, Local};
use crate::fft::{Domain, FftConfig};
use crate::msm::Scalar;
use crate::r1cs::{ConstraintSource, eval_rows};
use crate::spill::Spill;

/// The QAP evaluation domain for `src` (arkworks' sizing rule).
pub fn domain_for<S: ConstraintSource + ?Sized>(src: &S, cfg: FftConfig) -> Domain {
    Domain::new(src.num_constraints() + src.layout().num_instance(), cfg)
        .expect("constraint system too large for BN254's 2-adic domain")
}

/// The domain of exactly `n` points, if it is a supported shape and big enough
/// for `src`.
pub fn domain_of_size<S: ConstraintSource + ?Sized>(
    src: &S,
    n: usize,
    cfg: FftConfig,
) -> Result<Domain, String> {
    let min = src.num_constraints() + src.layout().num_instance();
    if n < min {
        return Err(format!(
            "a {n}-point QAP domain is too small for {min} rows"
        ));
    }
    Domain::with_size(n, cfg).ok_or_else(|| format!("no evaluation domain of {n} points"))
}

/// The domain a proving key with `h_len` `H` points was made for: `h_len + 1`
/// points (arkworks' layout) or `h_len`, of a supported shape and big enough
/// for `src`.
pub fn key_domain<S: ConstraintSource + ?Sized>(
    src: &S,
    h_len: usize,
    cfg: FftConfig,
) -> Result<Domain, String> {
    [h_len + 1, h_len]
        .into_iter()
        .find_map(|n| domain_of_size(src, n, cfg).ok())
        .ok_or_else(|| {
            let min = src.num_constraints() + src.layout().num_instance();
            format!("h_query has {h_len} points; no evaluation domain of that size fits {min} rows")
        })
}

/// `evals` (natural, on the domain) → evaluations on the coset `g·{ω^i}`, natural.
fn to_coset(dom: &Domain, v: &mut [Fr], accel: &mut dyn Accelerator) {
    if !accel.to_coset(dom, v) {
        dom.to_coset(v, Fr::GENERATOR);
    }
}

/// The quotient `h` in the domain's T-layout, read out in natural order one MSM
/// chunk at a time ([`chunk`](Self::chunk)) — so `h` is never copied into a
/// second, natural-order vector.
pub struct Quotient {
    t: Vec<Fr>,
    n1: usize,
    n2: usize,
}

impl Quotient {
    pub fn len(&self) -> usize {
        self.t.len()
    }

    pub fn is_empty(&self) -> bool {
        self.t.is_empty()
    }

    /// Natural-order coefficients `[off, off+len)` (index `k1 + N1·k2` lives at
    /// T-position `k1·N2 + k2`), through `f`.
    pub fn gather<U: Send>(&self, off: usize, len: usize, f: impl Fn(&Fr) -> U + Sync) -> Vec<U> {
        let (n1, n2, t) = (self.n1, self.n2, &self.t);
        (off..off + len)
            .into_par_iter()
            .with_min_len(1 << 12)
            .map(|i| f(&t[(i % n1) * n2 + i / n1]))
            .collect()
    }

    /// MSM-ready integers for coefficients `[off, off+len)`.
    pub fn chunk(&self, off: usize, len: usize) -> Vec<Scalar> {
        self.gather(off, len, |x| x.into_bigint())
    }
}

/// Spill block: elements read back per step when combining with a spilled vector.
const SPILL_BLOCK: usize = 1 << 16;

/// `buf[i] = f(buf[i], spilled[i])`, reading the spilled vector block by block.
fn combine(
    buf: &mut [Fr],
    spill: &mut dyn Spill,
    f: impl Fn(&mut Fr, &Fr) + Sync,
) -> std::io::Result<()> {
    let mut tmp = vec![Fr::zero(); SPILL_BLOCK.min(buf.len())];
    for (bi, block) in buf.chunks_mut(SPILL_BLOCK).enumerate() {
        let t = &mut tmp[..block.len()];
        spill.load(bi * SPILL_BLOCK, t)?;
        block
            .par_iter_mut()
            .zip(t.par_iter())
            .for_each(|(x, y)| f(x, y));
    }
    Ok(())
}

/// The quotient `h`. With `spill`, only one domain-sized vector is ever resident:
/// each coset-transformed vector is parked in `spill` while the next is computed
/// (rows are then streamed three times instead of twice). Without, `A` and `B`
/// are evaluated in one pass into two vectors.
pub fn quotient<S: ConstraintSource + ?Sized>(
    src: &S,
    z: &[Fr],
    dom: &Domain,
    rows_per_window: usize,
    accel: &mut dyn Accelerator,
    spill: Option<&mut dyn Spill>,
    probe: &mut dyn crate::prover::Probe,
) -> std::io::Result<Quotient> {
    let m = src.num_constraints();
    let ninst = src.layout().num_instance();
    assert_eq!(
        z.len(),
        src.layout().num_vars(),
        "assignment length mismatch"
    );
    let z_inv = (Fr::GENERATOR.pow([dom.n as u64]) - Fr::from(1u64))
        .inverse()
        .unwrap();
    let mut a = vec![Fr::zero(); dom.n];
    match spill {
        Some(spill) => {
            eval_rows(src, z, rows_per_window, [Some(&mut a[..m]), None, None]);
            probe.mark("qap_rows");
            a[m..m + ninst].copy_from_slice(&z[..ninst]);
            to_coset(dom, &mut a, accel);
            probe.mark("qap_fft");
            spill.store(&a)?; // A
            a.fill(Fr::zero());
            eval_rows(src, z, rows_per_window, [None, Some(&mut a[..m]), None]);
            to_coset(dom, &mut a, accel);
            combine(&mut a, spill, |b, a| *b *= a)?;
            spill.store(&a)?; // AB
            a.fill(Fr::zero());
            eval_rows(src, z, rows_per_window, [None, None, Some(&mut a[..m])]);
            to_coset(dom, &mut a, accel);
            // (AB − C) / Z(g), Z(x) = xⁿ − 1 is constant on the coset.
            combine(&mut a, spill, |c, ab| *c = (*ab - *c) * z_inv)?;
        }
        None => {
            let mut b = vec![Fr::zero(); dom.n];
            eval_rows(
                src,
                z,
                rows_per_window,
                [Some(&mut a[..m]), Some(&mut b[..m]), None],
            );
            probe.mark("qap_rows");
            a[m..m + ninst].copy_from_slice(&z[..ninst]);
            to_coset(dom, &mut a, accel);
            to_coset(dom, &mut b, accel);
            probe.mark("qap_fft");
            a.par_iter_mut()
                .zip(b.par_iter())
                .for_each(|(x, y)| *x *= y);
            drop(b);
            let mut c = vec![Fr::zero(); dom.n];
            eval_rows(src, z, rows_per_window, [None, None, Some(&mut c[..m])]);
            probe.mark("qap_rows");
            to_coset(dom, &mut c, accel);
            a.par_iter_mut().zip(c.par_iter()).for_each(|(x, y)| {
                *x -= y;
                *x *= z_inv;
            });
        }
    }
    // Coset iFFT back to coefficients (T-layout).
    if !accel.from_coset_to_t(dom, &mut a) {
        dom.from_coset_to_t(&mut a, Fr::GENERATOR.inverse().unwrap());
    }
    Ok(Quotient {
        t: a,
        n1: dom.n1,
        n2: dom.n2,
    })
}

/// `h` coefficients (natural order) as field elements — directly comparable to
/// arkworks' `witness_map` output.
pub fn witness_map<S: ConstraintSource + ?Sized>(
    src: &S,
    z: &[Fr],
    cfg: FftConfig,
    rows_per_window: usize,
) -> Vec<Fr> {
    let dom = domain_for(src, cfg);
    let q = quotient(src, z, &dom, rows_per_window, &mut Local, None, &mut ()).unwrap();
    q.gather(0, q.len(), |x| *x)
}

/// [`witness_map`] through the spill path.
pub fn witness_map_spilled<S: ConstraintSource + ?Sized>(
    src: &S,
    z: &[Fr],
    cfg: FftConfig,
    rows_per_window: usize,
    spill: &mut dyn Spill,
) -> Vec<Fr> {
    let dom = domain_for(src, cfg);
    let q = quotient(
        src,
        z,
        &dom,
        rows_per_window,
        &mut Local,
        Some(spill),
        &mut (),
    )
    .unwrap();
    q.gather(0, q.len(), |x| *x)
}
