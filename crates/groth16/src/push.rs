//! Push-driven proving: feed the serialized proving key **as it arrives** (e.g.
//! chunks of a `fetch` response body) instead of reading it from a seekable source.
//!
//! The prover consumes the key strictly in file order — header, then the
//! `A`, `B₁`, `B₂`, `H`, `L` point vectors — so one forward pass suffices: each
//! vector's points arrive in chunks of at most one MSM chunk ([`KeyStream`]), are
//! folded into that vector's accumulator, and dropped. Neither the caller nor the
//! prover ever holds the key. `h` is computed as soon as the key's header — which
//! states the QAP domain — arrives (or up front, given the domain), so the work
//! overlaps the rest of the download.

use crate::types::{Proof, VerifyingKey};
use ark_bn254::{Bn254, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::CurveGroup;
use ark_ff::{PrimeField, Zero};
use ark_serialize::Compress;
use rayon::prelude::*;

use crate::accel::{Accelerator, sum_g1, sum_g2};
use crate::keystream::{KeyEvent, KeyStream, KeyStreamError};
use crate::msm::{Scalar, StreamingMsm};
use crate::pk::KeyVector;
use crate::prover::{ProveError, ProverConfig};
use crate::qap;
use crate::r1cs::ConstraintSource;

/// A proof in progress, waiting for proving-key bytes. See the module docs.
pub struct PushProver<S: ConstraintSource> {
    src: S,
    z: Vec<Fr>,
    /// The quotient, once the domain is known.
    h: Option<qap::Quotient>,
    r: Fr,
    s: Fr,
    cfg: ProverConfig,
    ks: KeyStream,
    header: Option<(VerifyingKey<Bn254>, G1Affine, G1Affine)>,
    g1: [StreamingMsm<G1Projective>; 4],
    g2: StreamingMsm<G2Projective>,
    /// Partial sums returned by an accelerator, per vector (uncompressed affine).
    parts: [Vec<u8>; 5],
}

fn index(v: KeyVector) -> usize {
    match v {
        KeyVector::A => 0,
        KeyVector::BG1 => 1,
        KeyVector::BG2 => 2,
        KeyVector::H => 3,
        KeyVector::L => 4,
    }
}

/// The prover's event handler (split from [`PushProver`] so the key stream can
/// be borrowed mutably alongside it).
struct Fold<'a, S: ConstraintSource> {
    src: &'a S,
    z: &'a [Fr],
    h: &'a mut Option<qap::Quotient>,
    cfg: &'a ProverConfig,
    header: &'a mut Option<(VerifyingKey<Bn254>, G1Affine, G1Affine)>,
    g1: &'a mut [StreamingMsm<G1Projective>; 4],
    g2: &'a mut StreamingMsm<G2Projective>,
    parts: &'a mut [Vec<u8>; 5],
    accel: &'a mut dyn Accelerator,
}

impl<S: ConstraintSource> Fold<'_, S> {
    fn quotient(&mut self, dom: &crate::fft::Domain) -> Result<(), ProveError> {
        *self.h = Some(crate::prover::quotient_for(
            self.src,
            self.z,
            dom,
            self.cfg,
            self.accel,
            &mut (),
        )?);
        Ok(())
    }

    fn event(&mut self, e: KeyEvent) -> Result<(), ProveError> {
        let mismatch = |m: String| ProveError::KeyMismatch(m);
        let layout = self.src.layout();
        match e {
            KeyEvent::Header {
                vk,
                beta_g1,
                delta_g1,
                domain,
                ..
            } => {
                if vk.gamma_abc_g1.len() != layout.num_instance() {
                    return Err(mismatch(format!(
                        "vk has {} public inputs, circuit has {}",
                        vk.gamma_abc_g1.len().saturating_sub(1),
                        layout.num_instance() - 1
                    )));
                }
                *self.header = Some((vk.clone(), beta_g1, delta_g1));
                if self.h.is_none() {
                    // The header states the domain (v2); an older key implies
                    // radix-2, corrected below if its `H` length disagrees.
                    let dom = match domain {
                        Some(n) => {
                            qap::domain_of_size(self.src, n, self.cfg.fft).map_err(mismatch)?
                        }
                        None => qap::domain_for(self.src, self.cfg.fft),
                    };
                    self.quotient(&dom)?;
                }
            }
            KeyEvent::Len { v, len } => {
                let (ok, want) = match v {
                    KeyVector::H => {
                        let n = self.h.as_ref().map_or(0, |h| h.len());
                        if len + 1 != n && len != n {
                            // `h` was computed for a hinted or implied domain; the
                            // key was made for another one (e.g. smooth vs radix-2).
                            let dom =
                                qap::key_domain(self.src, len, self.cfg.fft).map_err(mismatch)?;
                            self.quotient(&dom)?;
                        }
                        (true, len)
                    }
                    KeyVector::L => (len == layout.num_witness(), layout.num_witness()),
                    _ => (len == layout.num_vars(), layout.num_vars()),
                };
                if !ok {
                    return Err(mismatch(format!(
                        "key vector {v:?} has {len} points, circuit needs {want}"
                    )));
                }
            }
            KeyEvent::Points {
                v,
                offset,
                bytes,
                compressed,
            } => self.fold(index(v), offset, bytes, compressed)?,
        }
        Ok(())
    }

    /// Scalars for vector `i` (file order: A, B₁, B₂, H, L) at points `[off, off+n)`.
    fn scalars(&self, i: usize, off: usize, n: usize) -> Vec<Scalar> {
        let ninst = self.src.layout().num_instance();
        match i {
            3 => self
                .h
                .as_ref()
                .expect("h computed at the header")
                .chunk(off, n),
            4 => self.z[ninst + off..ninst + off + n]
                .par_iter()
                .map(|x| x.into_bigint())
                .collect(),
            _ => self.z[off..off + n]
                .par_iter()
                .map(|x| x.into_bigint())
                .collect(),
        }
    }

    fn fold(
        &mut self,
        i: usize,
        off: usize,
        bytes: &[u8],
        compressed: bool,
    ) -> Result<(), ProveError> {
        let c = if compressed {
            Compress::Yes
        } else {
            Compress::No
        };
        let psz = if i == 2 {
            ark_serialize::CanonicalSerialize::serialized_size(&G2Affine::default(), c)
        } else {
            ark_serialize::CanonicalSerialize::serialized_size(&G1Affine::default(), c)
        };
        let n = bytes.len() / psz;
        let sc = self.scalars(i, off, n);
        if self.accel.wants_msm()
            && let Some(p) = self.accel.msm(i == 2, bytes, compressed, &sc)
        {
            self.parts[i].extend_from_slice(&p);
            return Ok(());
        }
        let de = |e| ProveError::Pk(crate::pk::PkError::Deserialize(e));
        if i == 2 {
            let pts: Vec<G2Affine> = bytes
                .par_chunks(psz)
                .map(|b| crate::decode::point::<G2Affine>(b, c))
                .collect::<Result<_, _>>()
                .map_err(de)?;
            self.g2.feed(&pts, &sc);
        } else {
            let pts: Vec<G1Affine> = bytes
                .par_chunks(psz)
                .map(|b| crate::decode::point::<G1Affine>(b, c))
                .collect::<Result<_, _>>()
                .map_err(de)?;
            let slot = [0, 1, usize::MAX, 2, 3][i];
            self.g1[slot].feed(&pts, &sc);
        }
        Ok(())
    }
}

impl<S: ConstraintSource> PushProver<S> {
    /// Start a proof: `z` is the full assignment. `h` is computed when the key's
    /// header arrives — or now, if `cfg.domain` gives the domain — so it overlaps
    /// the key download. `accel` (if any) runs the FFT here and MSMs in [`push`].
    ///
    /// [`push`]: Self::push
    pub fn new(
        src: S,
        z: Vec<Fr>,
        r: Fr,
        s: Fr,
        cfg: ProverConfig,
        accel: &mut dyn Accelerator,
    ) -> Result<Self, ProveError> {
        let h = match cfg.domain {
            Some(n) => {
                let dom = qap::domain_of_size(&src, n, cfg.fft).map_err(ProveError::KeyMismatch)?;
                Some(crate::prover::quotient_for(
                    &src,
                    &z,
                    &dom,
                    &cfg,
                    accel,
                    &mut (),
                )?)
            }
            None => None,
        };
        let ks = KeyStream::new(cfg.msm_chunk);
        Ok(PushProver {
            src,
            z,
            h,
            r,
            s,
            cfg,
            ks,
            header: None,
            g1: std::array::from_fn(|_| StreamingMsm::new()),
            g2: StreamingMsm::new(),
            parts: Default::default(),
        })
    }

    /// The public inputs this proof is for (the instance part of the assignment).
    pub fn public_inputs(&self) -> &[Fr] {
        &self.z[1..self.src.layout().num_instance()]
    }

    /// Key bytes consumed so far.
    pub fn received(&self) -> u64 {
        self.ks.received()
    }

    /// Whether the whole key has been consumed.
    pub fn is_complete(&self) -> bool {
        self.ks.is_complete()
    }

    /// Feed the next bytes of the serialized key (any chunking).
    pub fn push(&mut self, bytes: &[u8], accel: &mut dyn Accelerator) -> Result<(), ProveError> {
        let mut fold = Fold {
            src: &self.src,
            z: &self.z,
            h: &mut self.h,
            cfg: &self.cfg,
            header: &mut self.header,
            g1: &mut self.g1,
            g2: &mut self.g2,
            parts: &mut self.parts,
            accel,
        };
        self.ks
            .push(bytes, &mut |e| fold.event(e))
            .map_err(|e| match e {
                KeyStreamError::Malformed(m) => ProveError::KeyMismatch(m),
                KeyStreamError::Handler(e) => e,
            })
    }

    /// Assemble (and self-check) the proof once the whole key has been pushed.
    pub fn finish(self) -> Result<Proof<Bn254>, ProveError> {
        if !self.ks.is_complete() {
            return Err(ProveError::KeyMismatch(format!(
                "proving key ended early (after {} bytes)",
                self.ks.received()
            )));
        }
        let (vk, beta_g1, delta_g1) = self.header.expect("header parsed");
        let [a, b1, h, l] = self.g1;
        let a = a.finish() + sum_g1(&self.parts[0]);
        let b1 = b1.finish() + sum_g1(&self.parts[1]);
        let b2 = self.g2.finish() + sum_g2(&self.parts[2]);
        let h = h.finish() + sum_g1(&self.parts[3]);
        let l = l.finish() + sum_g1(&self.parts[4]);
        let (r, s) = (self.r, self.s);
        let g_a = delta_g1 * r + a + vk.alpha_g1;
        let g1_b = if r.is_zero() {
            G1Projective::zero()
        } else {
            delta_g1 * s + b1 + beta_g1
        };
        let g2_b = vk.delta_g2 * s + b2 + vk.beta_g2;
        let mut g_c = g_a * s;
        g_c += g1_b * r;
        g_c -= delta_g1 * (r * s);
        g_c += l;
        g_c += h;
        let proof = Proof {
            a: g_a.into_affine(),
            b: g2_b.into_affine(),
            c: g_c.into_affine(),
        };
        if self.cfg.self_check {
            let ninst = self.src.layout().num_instance();
            if !crate::types::verify(&vk, &self.z[1..ninst], &proof).unwrap_or(false) {
                return Err(crate::prover::self_check_failure(&self.src, &self.z));
            }
        }
        Ok(proof)
    }
}
