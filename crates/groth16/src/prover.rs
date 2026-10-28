//! The streaming Groth16 prover.
//!
//! Same math (and, for the same `r, s`, the same proof bytes) as ark-groth16's
//! `create_proof_with_reduction`, restructured so nothing O(circuit) beyond the
//! witness and two FFT vectors is ever resident:
//!
//! 1. `A`, `B₁`, `B₂` MSMs — key points streamed in chunks; each chunk's scalars are
//!    converted from the witness on the fly.
//! 2. `h` — rows streamed twice from the [`ConstraintSource`]; blocked FFT.
//! 3. `H`, `L` MSMs — streamed the same way; `h` is dropped right after `H`.

use crate::types::Proof;
use ark_bn254::{Bn254, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::CurveGroup;
use ark_ff::{PrimeField, UniformRand, Zero};
use rand::RngCore;

use crate::accel::{Accelerator, Local, sum_g1, sum_g2};
use crate::fft::FftConfig;
use crate::msm::{Scalar, StreamingMsm};
use crate::pk::{G1Query, KeyVector, PkError, PkSource};
use crate::qap;
use crate::r1cs::ConstraintSource;

/// Prover tuning.
#[derive(Clone, Debug)]
pub struct ProverConfig {
    /// Rows expanded per window when streaming constraints.
    pub rows_per_window: usize,
    /// Proving-key points per streamed MSM chunk.
    pub msm_chunk: usize,
    pub fft: FftConfig,
    /// Verify the proof against the key's embedded `vk` before returning.
    pub self_check: bool,
    /// Low-memory mode: park quotient vectors in a temp file in this directory,
    /// so only one domain-sized vector is resident (rows stream once more).
    pub spill_dir: Option<std::path::PathBuf>,
    /// QAP domain size for [`PushProver`](crate::PushProver): with it, `h` is
    /// computed up front instead of when the key's header (which states the
    /// domain) arrives. Only useful to start before the key does; a wrong value
    /// costs one recomputation, never a wrong proof. Pull-based proving reads
    /// the domain from the key and ignores this.
    pub domain: Option<usize>,
}

impl Default for ProverConfig {
    fn default() -> Self {
        ProverConfig {
            rows_per_window: 1 << 14,
            msm_chunk: 1 << 19,
            fft: FftConfig::default(),
            self_check: true,
            spill_dir: None,
            domain: None,
        }
    }
}

/// Errors from [`prove`].
#[derive(Debug)]
pub enum ProveError {
    Pk(PkError),
    /// Writing or reading the low-memory spill file failed.
    Spill(std::io::Error),
    /// The proving key's shape doesn't match the constraint source — wrong key for
    /// this circuit (or a different minimization of it).
    KeyMismatch(String),
    /// The proof failed verification under the key's own `vk` because the
    /// witness breaks constraint row `row` (of the source's rows): the inputs
    /// don't satisfy the circuit.
    Unsatisfied {
        row: usize,
    },
    /// The proof failed verification under the key's own `vk` although the
    /// witness satisfies every row: the key was made for a different circuit (or
    /// a different build of it). Never a forgeable state.
    SelfCheckFailed,
}

/// Why a proof failed its self-check: the witness, or the key.
pub(crate) fn self_check_failure<S: ConstraintSource + ?Sized>(src: &S, z: &[Fr]) -> ProveError {
    match crate::r1cs::first_unsatisfied(src, z) {
        Some(row) => ProveError::Unsatisfied { row },
        None => ProveError::SelfCheckFailed,
    }
}

impl std::fmt::Display for ProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProveError::Pk(e) => write!(f, "{e}"),
            ProveError::Spill(e) => write!(f, "low-memory spill file: {e}"),
            ProveError::KeyMismatch(m) => write!(f, "proving key does not match circuit: {m}"),
            ProveError::Unsatisfied { row } => write!(
                f,
                "the witness does not satisfy the circuit (constraint row {row} fails)"
            ),
            ProveError::SelfCheckFailed => write!(
                f,
                "the proof failed self-verification although the witness satisfies every \
                 constraint: the proving key was made for a different circuit (or build of it)"
            ),
        }
    }
}

impl std::error::Error for ProveError {}

impl From<PkError> for ProveError {
    fn from(e: PkError) -> Self {
        ProveError::Pk(e)
    }
}

/// Phase hook for instrumentation (timing / peak-memory sampling).
pub trait Probe {
    fn mark(&mut self, _phase: &'static str) {}
}

impl Probe for () {}

/// Check the key's vector lengths against the constraint source (the ordering
/// contract's first line of defence).
fn check_shape<S: ConstraintSource + ?Sized, P: PkSource + ?Sized>(
    src: &S,
    pk: &P,
    domain: usize,
) -> Result<(), ProveError> {
    let h = pk.header();
    let l = src.layout();
    let want = [
        ("a_query", h.a_len, l.num_vars()),
        ("b_g1_query", h.b_g1_len, l.num_vars()),
        ("b_g2_query", h.b_g2_len, l.num_vars()),
        ("l_query", h.l_len, l.num_witness()),
    ];
    for (name, got, exp) in want {
        if got != exp {
            return Err(ProveError::KeyMismatch(format!(
                "{name} has {got} points, circuit needs {exp}"
            )));
        }
    }
    if h.h_len + 1 != domain && h.h_len != domain {
        return Err(ProveError::KeyMismatch(format!(
            "h_query has {} points for a domain of {domain}",
            h.h_len
        )));
    }
    if h.vk.gamma_abc_g1.len() != l.num_instance() {
        return Err(ProveError::KeyMismatch(format!(
            "vk has {} public inputs, circuit has {}",
            h.vk.gamma_abc_g1.len() - 1,
            l.num_instance() - 1
        )));
    }
    Ok(())
}

/// Points per serialized chunk of vector `v` (G1 or G2, either encoding).
fn point_bytes(v: KeyVector, compressed: bool) -> usize {
    let g1 = if compressed { 32 } else { 64 };
    if v == KeyVector::BG2 { 2 * g1 } else { g1 }
}

/// Offer raw key chunks of `v` to the accelerator; `Ok(None)` if the source or
/// accelerator can't, in which case the caller streams decoded points itself.
fn accel_msm<P: PkSource + ?Sized>(
    pk: &mut P,
    accel: &mut dyn Accelerator,
    v: KeyVector,
    chunk: usize,
    sc: &dyn Fn(usize, usize) -> Vec<Scalar>,
) -> Result<Option<Vec<u8>>, PkError> {
    if !accel.wants_msm() {
        return Ok(None);
    }
    let mut parts: Vec<u8> = Vec::new();
    let mut declined = false;
    let supported = pk.stream_raw(v, chunk, &mut |off, bytes, compressed| {
        if declined {
            return;
        }
        let n = bytes.len() / point_bytes(v, compressed);
        match accel.msm(v == KeyVector::BG2, bytes, compressed, &sc(off, n)) {
            Some(p) => parts.extend_from_slice(&p),
            None => declined = true,
        }
    })?;
    Ok((supported && !declined).then_some(parts))
}

/// Stream a G1 vector against scalars `sc(offset, len)`.
fn stream_msm_g1<P: PkSource + ?Sized>(
    pk: &mut P,
    accel: &mut dyn Accelerator,
    q: G1Query,
    chunk: usize,
    sc: &dyn Fn(usize, usize) -> Vec<Scalar>,
) -> Result<G1Projective, PkError> {
    if let Some(parts) = accel_msm(pk, accel, q.into(), chunk, sc)? {
        return Ok(sum_g1(&parts));
    }
    let mut acc = StreamingMsm::<G1Projective>::new();
    pk.stream_g1(q, chunk, &mut |off, pts: &[G1Affine]| {
        acc.feed(pts, &sc(off, pts.len()));
    })?;
    Ok(acc.finish())
}

/// Stream the G2 `b` vector against scalars `sc(offset, len)`.
fn stream_msm_g2<P: PkSource + ?Sized>(
    pk: &mut P,
    accel: &mut dyn Accelerator,
    chunk: usize,
    sc: &dyn Fn(usize, usize) -> Vec<Scalar>,
) -> Result<G2Projective, PkError> {
    if let Some(parts) = accel_msm(pk, accel, KeyVector::BG2, chunk, sc)? {
        return Ok(sum_g2(&parts));
    }
    let mut acc = StreamingMsm::<G2Projective>::new();
    pk.stream_g2(chunk, &mut |off, pts: &[G2Affine]| {
        acc.feed(pts, &sc(off, pts.len()));
    })?;
    Ok(acc.finish())
}

/// The quotient, spilling per the accelerator or `cfg.spill_dir`.
pub(crate) fn quotient_for<S: ConstraintSource + ?Sized>(
    src: &S,
    z: &[Fr],
    dom: &crate::fft::Domain,
    cfg: &ProverConfig,
    accel: &mut dyn Accelerator,
    probe: &mut dyn Probe,
) -> Result<qap::Quotient, ProveError> {
    let mut spill: Option<Box<dyn crate::spill::Spill>> = match accel.spill() {
        Some(s) => Some(s),
        None => match &cfg.spill_dir {
            Some(d) => Some(Box::new(
                crate::spill::FileSpill::new_in(d).map_err(ProveError::Spill)?,
            )),
            None => None,
        },
    };
    let spill: Option<&mut dyn crate::spill::Spill> = match spill.as_mut() {
        Some(b) => Some(&mut **b),
        None => None,
    };
    let q = qap::quotient(src, z, dom, cfg.rows_per_window, accel, spill, probe);
    q.map_err(ProveError::Spill)
}

/// Prove with explicit randomness `(r, s)`. `z` is the full assignment in
/// [`VarLayout`](crate::r1cs::VarLayout) order (`z[0] = 1`).
pub fn prove_with_randomness<S, P>(
    src: &S,
    z: &[Fr],
    pk: &mut P,
    r: Fr,
    s: Fr,
    cfg: &ProverConfig,
    probe: &mut dyn Probe,
) -> Result<Proof<Bn254>, ProveError>
where
    S: ConstraintSource + ?Sized,
    P: PkSource + ?Sized,
{
    prove_accelerated(src, z, pk, r, s, cfg, probe, &mut Local)
}

/// [`prove_with_randomness`], routing FFT sweeps and MSM chunks through `accel`.
#[allow(clippy::too_many_arguments)]
pub fn prove_accelerated<S, P>(
    src: &S,
    z: &[Fr],
    pk: &mut P,
    r: Fr,
    s: Fr,
    cfg: &ProverConfig,
    probe: &mut dyn Probe,
    accel: &mut dyn Accelerator,
) -> Result<Proof<Bn254>, ProveError>
where
    S: ConstraintSource + ?Sized,
    P: PkSource + ?Sized,
{
    probe.mark("start");
    let dom = qap::key_domain(src, pk.header().h_len, cfg.fft).map_err(ProveError::KeyMismatch)?;
    if let Some(n) = pk.header().domain
        && n != dom.n
    {
        return Err(ProveError::KeyMismatch(format!(
            "header states a {n}-point domain, h_query implies {}",
            dom.n
        )));
    }
    check_shape(src, pk, dom.n)?;
    let ninst = src.layout().num_instance();
    let chunk = cfg.msm_chunk;
    let hdr = pk.header().clone();

    // Witness scalars for key positions [off, off+len), converted per chunk.
    let z_sc = |off: usize, len: usize| -> Vec<Scalar> {
        use rayon::prelude::*;
        z[off..off + len]
            .par_iter()
            .map(|x| x.into_bigint())
            .collect()
    };
    let aux_sc = |off: usize, len: usize| z_sc(ninst + off, len);

    // 1) A, B₁, B₂ (key file order). Each `query[0]` pairs with z[0] = 1.
    let a_acc = stream_msm_g1(pk, accel, G1Query::A, chunk, &z_sc)?;
    probe.mark("msm_a");
    let b1_acc = if r.is_zero() {
        G1Projective::zero()
    } else {
        stream_msm_g1(pk, accel, G1Query::BG1, chunk, &z_sc)?
    };
    probe.mark("msm_b_g1");
    let b2_acc = stream_msm_g2(pk, accel, chunk, &z_sc)?;
    probe.mark("msm_b_g2");

    // 2) h.
    let h = quotient_for(src, z, &dom, cfg, accel, probe)?;
    probe.mark("qap_h");

    // 3) H, L.
    let h_acc = stream_msm_g1(pk, accel, G1Query::H, chunk, &|off, len| h.chunk(off, len))?;
    drop(h);
    probe.mark("msm_h");
    let l_acc = stream_msm_g1(pk, accel, G1Query::L, chunk, &aux_sc)?;
    probe.mark("msm_l");

    let g_a = hdr.delta_g1 * r + a_acc + hdr.vk.alpha_g1;
    let g1_b = if r.is_zero() {
        G1Projective::zero()
    } else {
        hdr.delta_g1 * s + b1_acc + hdr.beta_g1
    };
    let g2_b = hdr.vk.delta_g2 * s + b2_acc + hdr.vk.beta_g2;
    let mut g_c = g_a * s;
    g_c += g1_b * r;
    g_c -= hdr.delta_g1 * (r * s);
    g_c += l_acc;
    g_c += h_acc;

    let proof = Proof {
        a: g_a.into_affine(),
        b: g2_b.into_affine(),
        c: g_c.into_affine(),
    };
    if cfg.self_check {
        if !crate::types::verify(&hdr.vk, &z[1..ninst], &proof).unwrap_or(false) {
            return Err(self_check_failure(src, z));
        }
        probe.mark("self_check");
    }
    Ok(proof)
}

/// Prove with randomness drawn from `rng` exactly as arkworks does (`r` then `s`),
/// so a seeded RNG reproduces arkworks' proof byte-for-byte.
pub fn prove<S, P, R>(
    src: &S,
    z: &[Fr],
    pk: &mut P,
    rng: &mut R,
    cfg: &ProverConfig,
) -> Result<Proof<Bn254>, ProveError>
where
    S: ConstraintSource + ?Sized,
    P: PkSource + ?Sized,
    R: RngCore,
{
    let r = Fr::rand(rng);
    let s = Fr::rand(rng);
    prove_with_randomness(src, z, pk, r, s, cfg, &mut ())
}
