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
use ark_ec::{
    AffineRepr, CurveGroup,
    short_weierstrass::{Affine as SwAffine, SWCurveConfig},
};
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
    try_kernel_msm(g2, points, compressed, scalars).expect("invalid MSM work item")
}

/// Checked worker kernel for MSM over serialized points and 32-byte LE scalars.
/// Returns the uncompressed affine encoding of the sum.
pub fn try_kernel_msm(
    g2: bool,
    points: &[u8],
    compressed: bool,
    scalars: &[u8],
) -> Result<Vec<u8>, String> {
    if !scalars.len().is_multiple_of(32) {
        return Err("MSM scalar buffer length is not a multiple of 32".into());
    }
    let c = if compressed {
        Compress::Yes
    } else {
        Compress::No
    };
    let n = scalars.len() / 32;
    if n >= (1usize << 31) {
        return Err("MSM chunk is too large".into());
    }
    let point_size = if g2 {
        G2Affine::generator().serialized_size(c)
    } else {
        G1Affine::generator().serialized_size(c)
    };
    let expected_point_bytes = n
        .checked_mul(point_size)
        .ok_or_else(|| "MSM point buffer length overflows".to_string())?;
    if points.len() != expected_point_bytes {
        return Err(format!(
            "MSM point buffer has {} bytes for {n} scalars; expected {expected_point_bytes}",
            points.len()
        ));
    }
    let (scalar_chunks, _) = scalars.as_chunks::<32>();
    let sc: Vec<Scalar> = scalar_chunks
        .iter()
        .map(|b| {
            let mut l = [0u64; 4];
            let (words, _) = b.as_chunks::<8>();
            for (i, w) in words.iter().enumerate() {
                l[i] = u64::from_le_bytes(w.try_into().unwrap());
            }
            BigInt(l)
        })
        .collect();
    let mut out = Vec::new();
    if g2 {
        let pts: Vec<G2Affine> = points
            .chunks_exact(point_size)
            .map(|b| crate::decode::point::<G2Affine>(b, c).map_err(|e| e.to_string()))
            .collect::<Result<_, _>>()?;
        if !valid_group_points(&pts) {
            return Err("MSM input contains an invalid G2 point".into());
        }
        msm::<G2Projective>(&pts, &sc)
            .into_affine()
            .serialize_uncompressed(&mut out)
            .map_err(|e| e.to_string())?;
    } else {
        let pts: Vec<G1Affine> = points
            .chunks_exact(point_size)
            .map(|b| crate::decode::point::<G1Affine>(b, c).map_err(|e| e.to_string()))
            .collect::<Result<_, _>>()?;
        if !valid_group_points(&pts) {
            return Err("MSM input contains an invalid G1 point".into());
        }
        msm::<G1Projective>(&pts, &sc)
            .into_affine()
            .serialize_uncompressed(&mut out)
            .map_err(|e| e.to_string())?;
    }
    Ok(out)
}

fn valid_group_points<P: SWCurveConfig>(points: &[SwAffine<P>]) -> bool {
    points
        .iter()
        .all(|point| point.is_on_curve() && point.is_in_correct_subgroup_assuming_on_curve())
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

/// Whether an accelerator returned one or more valid uncompressed partial sums.
/// A malformed response must be declined before `sum_g1` / `sum_g2` consumes it.
pub(crate) fn valid_msm_output(g2: bool, bytes: &[u8]) -> bool {
    if g2 {
        let point_size = G2Affine::default().uncompressed_size();
        !bytes.is_empty()
            && bytes.len().is_multiple_of(point_size)
            && bytes
                .chunks_exact(point_size)
                .all(|part| G2Affine::deserialize_uncompressed(part).is_ok())
    } else {
        let point_size = G1Affine::default().uncompressed_size();
        !bytes.is_empty()
            && bytes.len().is_multiple_of(point_size)
            && bytes
                .chunks_exact(point_size)
                .all(|part| G1Affine::deserialize_uncompressed(part).is_ok())
    }
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

#[cfg(test)]
mod tests {
    use super::{try_kernel_msm, valid_msm_output};
    use ark_bn254::{Fq, Fq2, G1Affine, G2Affine};
    use ark_ec::AffineRepr;
    use ark_serialize::CanonicalSerialize;

    fn scalar_one() -> [u8; 32] {
        let mut bytes = [0; 32];
        bytes[0] = 1;
        bytes
    }

    #[test]
    fn rejects_incomplete_scalar_bytes() {
        assert!(try_kernel_msm(false, &[], true, &[0; 31]).is_err());
    }

    #[test]
    fn rejects_point_count_mismatch_before_decoding() {
        assert!(try_kernel_msm(false, &[0; 32], true, &[0; 64]).is_err());
    }

    #[test]
    fn rejects_invalid_compressed_points_without_panicking() {
        assert!(try_kernel_msm(false, &[0xff; 32], true, &scalar_one()).is_err());
    }

    #[test]
    fn rejects_off_curve_uncompressed_points_in_both_groups() {
        let g1 = G1Affine::new_unchecked(Fq::from(1u64), Fq::from(1u64));
        let mut g1_bytes = Vec::new();
        g1.serialize_uncompressed(&mut g1_bytes).unwrap();
        assert!(try_kernel_msm(false, &g1_bytes, false, &scalar_one()).is_err());

        let one = Fq::from(1u64);
        let zero = Fq::from(0u64);
        let g2 = G2Affine::new_unchecked(Fq2::new(one, zero), Fq2::new(one, zero));
        let mut g2_bytes = Vec::new();
        g2.serialize_uncompressed(&mut g2_bytes).unwrap();
        assert!(try_kernel_msm(true, &g2_bytes, false, &scalar_one()).is_err());
    }

    #[test]
    fn checked_kernel_returns_the_single_point_product() {
        let mut point = Vec::new();
        G1Affine::generator()
            .serialize_compressed(&mut point)
            .unwrap();
        let got = try_kernel_msm(false, &point, true, &scalar_one()).unwrap();

        let mut expected = Vec::new();
        G1Affine::generator()
            .serialize_uncompressed(&mut expected)
            .unwrap();
        assert_eq!(got, expected);
    }

    #[test]
    fn checked_kernel_accepts_a_valid_g2_generator() {
        let mut point = Vec::new();
        G2Affine::generator()
            .serialize_compressed(&mut point)
            .unwrap();
        let got = try_kernel_msm(true, &point, true, &scalar_one()).unwrap();

        let mut expected = Vec::new();
        G2Affine::generator()
            .serialize_uncompressed(&mut expected)
            .unwrap();
        assert_eq!(got, expected);
    }

    #[test]
    fn validates_accelerator_partial_sum_buffers() {
        let mut g1 = Vec::new();
        G1Affine::generator()
            .serialize_uncompressed(&mut g1)
            .unwrap();
        let mut g2 = Vec::new();
        G2Affine::generator()
            .serialize_uncompressed(&mut g2)
            .unwrap();

        assert!(valid_msm_output(false, &g1));
        assert!(valid_msm_output(
            false,
            &[g1.as_slice(), g1.as_slice()].concat()
        ));
        assert!(!valid_msm_output(false, &[]));
        assert!(!valid_msm_output(false, &[g1.as_slice(), &[0]].concat()));
        assert!(!valid_msm_output(false, &[0xff; 64]));
        assert!(valid_msm_output(true, &g2));
        assert!(!valid_msm_output(true, &g1));
    }
}
