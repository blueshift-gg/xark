//! The streaming Groth16 prover.
//!
//! Same math (and, for the same `r, s`, the same proof bytes) as ark-groth16's
//! `create_proof_with_reduction`, restructured so nothing O(circuit) beyond the
//! witness and two FFT vectors is ever resident:
//!
//! 1. `A`, `B₁`, `B₂` MSMs — key points streamed in chunks; each chunk's scalars are
//!    converted from the witness on the fly.
//! 2. `h` — rows streamed twice from the [`ConstraintSource`]; blocked FFT. Without
//!    an accelerator it is computed on the thread pool while 1. runs.
//! 3. `H`, `L` MSMs — streamed the same way; `h` is dropped right after `H`.
//!
//! A key already in memory ([`PkSource::resident`]) needs no order: its five MSMs
//! and the quotient run side by side.

use crate::types::Proof;
use ark_bn254::{Bn254, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::CurveGroup;
use ark_ec::pairing::Pairing;
use ark_ff::{PrimeField, UniformRand, Zero};
use rand::RngCore;

use crate::accel::{Accelerator, Local, sum_g1, sum_g2, valid_msm_output};
use crate::fft::FftConfig;
use crate::msm::{Scalar, StreamingMsm, SwCurve};
use crate::pk::{G1Query, KeyVector, PkError, PkSource};
use crate::qap;
use crate::r1cs::ConstraintSource;
use crate::types::Prepared;

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
    /// A circuit with fewer variables than this, proved from a resident key
    /// ([`PkSource::resident`]), gets its proof from three MSMs rather than five
    /// (see `prove_merged`). Past it, a witness of bits keeps its MSMs narrow.
    pub merge_below: usize,
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
            merge_below: 1 << 12,
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
        let g2 = v == KeyVector::BG2;
        match accel.msm(g2, bytes, compressed, &sc(off, n)) {
            Some(p) if valid_msm_output(g2, &p) => parts.extend_from_slice(&p),
            Some(_) | None => declined = true,
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

/// A small circuit's proof from a resident key in three MSMs instead of five, the
/// terms that need only `r` and `s` folded in as extra points:
///
/// * `A = Σ zᵢ·Aᵢ + α + r·δ`,
/// * `B = Σ zᵢ·B₂ᵢ + β + s·δ`,
/// * `C = s·A + Σ r·zᵢ·B₁ᵢ + r·β + Σ zⱼ·Lⱼ + Σ hₖ·Hₖ`, since `C = s·A + r·B₁ − rs·δ
///   + L + H` and `B₁ = Σ zᵢ·B₁ᵢ + β + s·δ` is used nowhere else.
///
/// Each small Pippenger pays its windows' fixed costs (bucket reductions,
/// doublings) whatever its length, so one MSM over B₁, L and H costs well under
/// three; the price is `r·zᵢ` being full width even where `zᵢ` is a bit, which is
/// why this is for small circuits only ([`ProverConfig::merge_below`]).
fn prove_merged<S: ConstraintSource + ?Sized>(
    src: &S,
    z: &[Fr],
    key: &crate::types::ProvingKey<Bn254>,
    dom: &crate::fft::Domain,
    r: Fr,
    s: Fr,
    cfg: &ProverConfig,
) -> Result<Proof<Bn254>, ProveError> {
    use crate::msm::msm;
    let ninst = key.vk.gamma_abc_g1.len();
    let zs: Vec<Scalar> = z.iter().map(|x| x.into_bigint()).collect();
    let one = Fr::from(1u64).into_bigint();
    let (mut ab, mut rest, mut prep) = (None, None, None);
    let check = cfg.self_check;
    // The self-check's Miller loops split along the proof: with C = s·A + rest,
    // e(A, B)·e(C, −δ) = e(A, B − s·δ)·e(rest, −δ), and B − s·δ = β + Σ zᵢ·B₂ᵢ,
    // so one loop follows A and B, one follows rest, and only the final
    // exponentiation is left after both.
    type G2Prepared = <Bn254 as Pairing>::G2Prepared;
    rayon::scope(|sc| {
        sc.spawn(|_| {
            let (b_msm, g_a) = rayon::join(
                || {
                    let mut pts = key.b_g2_query.clone();
                    pts.push(key.vk.beta_g2);
                    let mut k = zs.clone();
                    k.push(one);
                    msm::<G2Projective>(&pts, &k)
                },
                || {
                    let mut pts = key.a_query.clone();
                    pts.extend([key.vk.alpha_g1, key.delta_g1]);
                    let mut k = zs.clone();
                    k.extend([one, r.into_bigint()]);
                    msm::<G1Projective>(&pts, &k)
                },
            );
            let a = g_a.into_affine();
            let ((b, sa), ml) = rayon::join(
                || ((b_msm + key.vk.delta_g2 * s).into_affine(), g_a * s),
                || check.then(|| Bn254::multi_miller_loop([a], [b_msm.into_affine()]).0),
            );
            ab = Some((a, b, sa, ml));
        });
        sc.spawn(|_| {
            let (c, neg_delta) = rayon::join(
                || {
                    quotient_for(src, z, dom, cfg, &mut Local, &mut ()).map(|h| {
                        let n = key.b_g1_query.len() + key.l_query.len() + key.h_query.len() + 1;
                        let mut pts = Vec::with_capacity(n);
                        let mut k = Vec::with_capacity(n);
                        if !r.is_zero() {
                            pts.push(key.beta_g1);
                            k.push(r.into_bigint());
                            pts.extend_from_slice(&key.b_g1_query);
                            k.extend(z.iter().map(|x| (*x * r).into_bigint()));
                        }
                        pts.extend_from_slice(&key.l_query);
                        k.extend_from_slice(&zs[ninst..]);
                        pts.extend_from_slice(&key.h_query);
                        k.extend(h.chunk(0, key.h_query.len()));
                        msm::<G1Projective>(&pts, &k)
                    })
                },
                || check.then(|| G2Prepared::from(-key.vk.delta_g2)),
            );
            rest = Some(c.map(|c| {
                let ml = neg_delta.map(|nd| Bn254::multi_miller_loop([c.into_affine()], [nd]).0);
                (c, ml)
            }));
        });
        if check {
            sc.spawn(|_| prep = Some(Prepared::new(&key.vk, &z[1..ninst])));
        }
    });
    let joined = "the scope joined every task";
    let (a, b, sa, ml_ab) = ab.expect(joined);
    let (rest, ml_rest) = rest.expect(joined)?;
    let proof = Proof {
        a,
        b,
        c: (sa + rest).into_affine(),
    };
    if check {
        let made = "made when self-checking";
        let ok = prep
            .expect(joined)
            .is_ok_and(|p| p.verify_with(ml_ab.expect(made) * ml_rest.expect(made)));
        if !ok {
            return Err(self_check_failure(src, z));
        }
    }
    Ok(proof)
}

/// `Σ sᵢ·Pᵢ` over a resident key vector, `chunk` points at a time (bounding
/// the MSM's digit tables, as a streamed key's chunks do).
fn resident_msm<G: SwCurve>(
    v: &[G::Affine],
    chunk: usize,
    sc: &(dyn Fn(usize, usize) -> Vec<Scalar> + Sync),
) -> G {
    let chunk = chunk.max(1);
    let mut acc = StreamingMsm::<G>::new();
    for (i, c) in v.chunks(chunk).enumerate() {
        acc.feed(c, &sc(i * chunk, c.len()));
    }
    acc.finish()
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
    prove_impl(src, z, pk, r, s, cfg, probe, None)
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
    prove_impl(src, z, pk, r, s, cfg, probe, Some(accel))
}

/// With no accelerator and no `cfg.spill_dir`, `h` is computed on the thread pool
/// while this thread streams the A, B₁, B₂ MSMs; an accelerator may own the workers
/// (and is not `Send`), and spilling caps peak memory, so then the steps run in turn.
#[allow(clippy::too_many_arguments)]
fn prove_impl<S, P>(
    src: &S,
    z: &[Fr],
    pk: &mut P,
    r: Fr,
    s: Fr,
    cfg: &ProverConfig,
    probe: &mut dyn Probe,
    accel: Option<&mut dyn Accelerator>,
) -> Result<Proof<Bn254>, ProveError>
where
    S: ConstraintSource + ?Sized,
    P: PkSource + ?Sized,
{
    let mut local = Local;
    let (concurrent, accel) = match accel {
        Some(a) => (false, a),
        None => (cfg.spill_dir.is_none(), &mut local as &mut dyn Accelerator),
    };
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
            .with_min_len(1 << 12)
            .map(|x| x.into_bigint())
            .collect()
    };
    let aux_sc = |off: usize, len: usize| z_sc(ninst + off, len);

    // 1) A, B₁, B₂ (key file order). Each `query[0]` pairs with z[0] = 1.
    let witness_msms = |pk: &mut P, accel: &mut dyn Accelerator, probe: &mut dyn Probe| {
        let a = stream_msm_g1(pk, accel, G1Query::A, chunk, &z_sc)?;
        probe.mark("msm_a");
        let b1 = if r.is_zero() {
            G1Projective::zero()
        } else {
            stream_msm_g1(pk, accel, G1Query::BG1, chunk, &z_sc)?
        };
        probe.mark("msm_b1");
        let b2 = stream_msm_g2(pk, accel, chunk, &z_sc)?;
        Ok::<_, PkError>((a, b1, b2))
    };
    // The terms of A, B and C that need only r and s, and the self-check's half
    // that needs no proof: both made while the MSMs run. With
    // A = α + A_msm + r·δ and B₁ = β + B₁_msm + s·δ (only C uses B₁),
    // C = s·A + r·B₁ − rs·δ + L + H = s·α + r·β + rs·δ + s·A_msm + r·B₁_msm + L + H.
    let fixed = || {
        let rs_term = if r.is_zero() {
            hdr.vk.alpha_g1 * s
        } else {
            hdr.vk.alpha_g1 * s + hdr.beta_g1 * r + hdr.delta_g1 * (r * s)
        };
        (hdr.delta_g1 * r, hdr.vk.delta_g2 * s, rs_term)
    };
    let mut fixed_terms = None;
    let mut prep = None;
    let merged = concurrent
        && pk
            .resident()
            .is_some_and(|k| k.a_query.len() < cfg.merge_below);
    if merged {
        let key = pk.resident().expect("checked above");
        let proof = prove_merged(src, z, key, &dom, r, s, cfg)?;
        probe.mark("msm+qap_h+self_check");
        return Ok(proof);
    }
    let (a_acc, b1_acc, b2_acc, l_acc, h_acc) = if concurrent && pk.resident().is_some() {
        // 2) A resident key: each MSM is a task beside the quotient, so a small
        // circuit's MSMs, too short to fill the pool one at a time, fill it
        // together, and H starts as soon as h is ready.
        let key = pk.resident().expect("checked above");
        let (mut a, mut b1, mut b2, mut l) = (None, None, None, None);
        let mut h = None;
        rayon::scope(|sc| {
            sc.spawn(|_| {
                h = Some(
                    quotient_for(src, z, &dom, cfg, &mut Local, &mut ())
                        .map(|h| resident_msm(&key.h_query, chunk, &|off, len| h.chunk(off, len))),
                )
            });
            sc.spawn(|_| a = Some(resident_msm(&key.a_query, chunk, &z_sc)));
            if !r.is_zero() {
                sc.spawn(|_| b1 = Some(resident_msm(&key.b_g1_query, chunk, &z_sc)));
            }
            sc.spawn(|_| b2 = Some(resident_msm(&key.b_g2_query, chunk, &z_sc)));
            sc.spawn(|_| l = Some(resident_msm(&key.l_query, chunk, &aux_sc)));
            if cfg.self_check {
                sc.spawn(|_| prep = Some(Prepared::new(&hdr.vk, &z[1..ninst])));
            }
            sc.spawn(|_| fixed_terms = Some(fixed()));
        });
        probe.mark("msm+qap_h");
        let h = h.expect("the scope joined the quotient")?;
        let some = |p: Option<G1Projective>| p.expect("the scope joined every MSM");
        (
            some(a),
            b1.unwrap_or_default(),
            b2.expect("the scope joined every MSM"),
            some(l),
            h,
        )
    } else {
        // 2) h. Alone, 1) leaves cores idle (key reads, small digit classes, the
        // tail of each chunk), which the quotient's work fills.
        let ((a, b1, b2), h) = if concurrent {
            let mut h = None;
            let abl = rayon::in_place_scope(|sc| {
                sc.spawn(|_| h = Some(quotient_for(src, z, &dom, cfg, &mut Local, &mut ())));
                if cfg.self_check {
                    sc.spawn(|_| prep = Some(Prepared::new(&hdr.vk, &z[1..ninst])));
                }
                sc.spawn(|_| fixed_terms = Some(fixed()));
                witness_msms(pk, accel, &mut ())
            });
            probe.mark("msm_ab+qap_h");
            (abl?, h.expect("the scope joined the quotient")?)
        } else {
            let abl = witness_msms(pk, accel, probe)?;
            probe.mark("msm_ab");
            let h = quotient_for(src, z, &dom, cfg, accel, probe)?;
            probe.mark("qap_h");
            (abl, h)
        };
        // 3) H, L, in the key's order (a tee re-writes the key as it is read).
        let hq = stream_msm_g1(pk, accel, G1Query::H, chunk, &|off, len| h.chunk(off, len))?;
        drop(h);
        probe.mark("msm_h");
        let l = stream_msm_g1(pk, accel, G1Query::L, chunk, &aux_sc)?;
        probe.mark("msm_l");
        (a, b1, b2, l, hq)
    };

    let (delta_r, delta2_s, rs_term) = fixed_terms.unwrap_or_else(fixed);
    let g_a = delta_r + a_acc + hdr.vk.alpha_g1;
    let g2_b = delta2_s + b2_acc + hdr.vk.beta_g2;
    let (a_s, b1_r) = rayon::join(|| a_acc * s, || b1_acc * r);
    let g_c = rs_term + a_s + b1_r + l_acc + h_acc;

    let proof = Proof {
        a: g_a.into_affine(),
        b: g2_b.into_affine(),
        c: g_c.into_affine(),
    };
    if cfg.self_check {
        let prep = prep.unwrap_or_else(|| Prepared::new(&hdr.vk, &z[1..ninst]));
        if !prep.is_ok_and(|p| p.verify(&proof)) {
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
