//! Offloading the prover's data-parallel steps (e.g. to Web Workers).
//!
//! The prover itself is a sequential driver; its two heavy, embarrassingly
//! parallel steps are routed through an [`Accelerator`]:
//!
//! * the coset transforms of the quotient step — each is 2–3 sweeps
//!   ([`Domain::cols_kernel`] over column tiles, [`Domain::rows_kernel`] over row
//!   blocks) separated by barriers, exactly the four-step structure;
//! * the MSMs — each streamed proving-key chunk (raw serialized points) splits into
//!   independent sub-MSMs whose results are summed.
//!
//! Every hook may decline (return `None`/`false`) and the prover then does that step
//! itself, so a host without threads simply uses [`Local`]. The worker-side halves
//! are the pure functions in this module, so both ends share one implementation.

use ark_bn254::{Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::CurveGroup;
use ark_ff::{BigInt, Field};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress};

use crate::fft::{ColOp, Domain, RowStage};
use crate::msm::{Scalar, msm};

/// Offload hooks. Defaults decline, so implement only what you accelerate.
#[allow(clippy::wrong_self_convention)]
pub trait Accelerator {
    /// In place: evaluations (natural) → coset evaluations (natural), coset `g`.
    fn to_coset(&mut self, _dom: &Domain, _buf: &mut [Fr]) -> bool {
        false
    }
    /// In place: coset evaluations → coefficients in T-layout (coset `g`).
    fn from_coset_to_t(&mut self, _dom: &Domain, _buf: &mut [Fr]) -> bool {
        false
    }
    /// Whether [`msm`](Self::msm) should be offered raw key chunks.
    fn wants_msm(&self) -> bool {
        false
    }
    /// `Σ sᵢ·Pᵢ` over serialized points (`g2` selects the group; `compressed` the
    /// point encoding). Returns the sum in uncompressed affine encoding.
    fn msm(
        &mut self,
        _g2: bool,
        _points: &[u8],
        _compressed: bool,
        _scalars: &[Scalar],
    ) -> Option<Vec<u8>> {
        None
    }
    /// Somewhere outside the working set to park a quotient vector (e.g. a JS
    /// buffer outside wasm linear memory). `None`: use
    /// [`ProverConfig::spill_dir`](crate::ProverConfig::spill_dir) if set, else keep
    /// both vectors in memory.
    fn spill(&mut self) -> Option<Box<dyn crate::spill::Spill>> {
        None
    }
    /// Re-encode compressed points uncompressed (for key transcoding).
    fn decompress(&mut self, _g2: bool, _points: &[u8]) -> Option<Vec<u8>> {
        None
    }
}

/// No offloading: everything runs in-process (rayon-parallel where available).
pub struct Local;
impl Accelerator for Local {}

/// The coset generator used by the QAP (`Fr::GENERATOR`, as arkworks).
pub fn coset_gen() -> Fr {
    <Fr as ark_ff::FftField>::GENERATOR
}

/// Worker kernel: one block of whole rows of a coset transform chain.
/// `to_coset = true` → the fused middle sweep of [`Domain::to_coset`];
/// `false` → the final sweep of [`Domain::from_coset_to_t`].
pub fn kernel_rows(dom: &Domain, rows: &mut [Fr], first_row: usize, to_coset: bool) {
    if to_coset {
        dom.rows_kernel(
            rows,
            first_row,
            &[RowStage::Ifft, RowStage::Coset(coset_gen()), RowStage::Fft],
        );
    } else {
        let g_inv = coset_gen().inverse().unwrap();
        dom.rows_kernel(rows, first_row, &[RowStage::Ifft, RowStage::Coset(g_inv)]);
    }
}

/// Worker kernel: a row-major `N1 × b` column tile starting at column `c0`.
pub fn kernel_cols(dom: &Domain, block: &mut [Fr], c0: usize, op: ColOp) {
    dom.cols_kernel(block, c0, op);
}

/// Worker kernel: MSM over serialized points + 32-byte little-endian scalars,
/// returning the uncompressed affine encoding of the sum.
pub fn kernel_msm(g2: bool, points: &[u8], compressed: bool, scalars: &[u8]) -> Vec<u8> {
    let sc: Vec<Scalar> = scalars
        .as_chunks::<32>()
        .0
        .iter()
        .map(|b| {
            let mut l = [0u64; 4];
            for (i, w) in b.as_chunks::<8>().0.iter().enumerate() {
                l[i] = u64::from_le_bytes(*w);
            }
            BigInt(l)
        })
        .collect();
    let c = if compressed {
        Compress::Yes
    } else {
        Compress::No
    };
    let mut out = Vec::new();
    if g2 {
        let sz = points.len() / sc.len().max(1);
        let pts: Vec<G2Affine> = points
            .chunks_exact(sz.max(1))
            .map(|b| crate::decode::point::<G2Affine>(b, c).expect("bad G2 point"))
            .collect();
        msm::<G2Projective>(&pts, &sc)
            .into_affine()
            .serialize_uncompressed(&mut out)
            .unwrap();
    } else {
        let sz = points.len() / sc.len().max(1);
        let pts: Vec<G1Affine> = points
            .chunks_exact(sz.max(1))
            .map(|b| crate::decode::point::<G1Affine>(b, c).expect("bad G1 point"))
            .collect();
        msm::<G1Projective>(&pts, &sc)
            .into_affine()
            .serialize_uncompressed(&mut out)
            .unwrap();
    }
    out
}

/// Scalars as the 32-byte little-endian limbs [`kernel_msm`] reads.
pub fn scalars_to_bytes(sc: &[Scalar]) -> Vec<u8> {
    let mut out = Vec::with_capacity(sc.len() * 32);
    for s in sc {
        for l in s.0 {
            out.extend_from_slice(&l.to_le_bytes());
        }
    }
    out
}

/// Decode a sum returned by [`Accelerator::msm`] / [`kernel_msm`] (possibly the
/// concatenation of several partial sums) and add it up.
pub fn sum_g1(bytes: &[u8]) -> G1Projective {
    let sz = G1Affine::default().uncompressed_size();
    bytes
        .chunks_exact(sz)
        .map(|b| G1Affine::deserialize_uncompressed_unchecked(b).expect("bad partial sum"))
        .fold(G1Projective::default(), |acc, p| acc + p)
}

/// G2 counterpart of [`sum_g1`].
pub fn sum_g2(bytes: &[u8]) -> G2Projective {
    let sz = G2Affine::default().uncompressed_size();
    bytes
        .chunks_exact(sz)
        .map(|b| G2Affine::deserialize_uncompressed_unchecked(b).expect("bad partial sum"))
        .fold(G2Projective::default(), |acc, p| acc + p)
}

/// View a field vector as raw bytes (Montgomery limbs, native endianness) — the
/// zero-copy form handed to an accelerator. Only meaningful between instances of
/// the same build (both ends of a worker pool).
pub fn fr_bytes_mut(v: &mut [Fr]) -> &mut [u8] {
    // SAFETY: `Fr` is four `u64` limbs with no padding; any bytes written back are
    // produced by the same kernels from valid elements.
    unsafe { std::slice::from_raw_parts_mut(v.as_mut_ptr() as *mut u8, std::mem::size_of_val(v)) }
}
