use ark_bn254::{Fq, Fr, G1Affine};
use ark_ec::AffineRepr;
use ark_ff::{BigInt, PrimeField};
use ark_serialize::{CanonicalSerialize, Compress};
use rayon::prelude::*;
use xark_groth16::{Accelerator, msm::Scalar};

const PARALLEL_PREPARE_THRESHOLD: usize = 1024;

/// Xark's custom BN254 G1 bucket MSM kernel.
///
/// The native bridge is linked only with the `custom-cuda` feature. Without it,
/// this adapter declines all work so the prover uses its CPU MSM path.
#[derive(Default)]
pub struct CustomCudaMsm;

#[cfg(feature = "custom-cuda")]
unsafe extern "C" {
    fn xark_cuda_device_available() -> bool;
    fn xark_cuda_msm_g1(
        point_words: *const u32,
        scalar_limbs_soa: *const u64,
        scalar_count: usize,
        result_words: *mut u32,
    ) -> i32;
}

fn field_words(value: Fq) -> [u32; 8] {
    let limbs = value.into_bigint().0;
    std::array::from_fn(|index| {
        let word = limbs[index / 2];
        if index % 2 == 0 {
            word as u32
        } else {
            (word >> 32) as u32
        }
    })
}

fn field_from_words(words: &[u32]) -> Option<Fq> {
    let limbs = std::array::from_fn(|index| {
        u64::from(words[2 * index]) | (u64::from(words[2 * index + 1]) << 32)
    });
    Fq::from_bigint(BigInt(limbs))
}

fn prepare_inputs(
    points: &[u8],
    compressed: bool,
    scalars: &[Scalar],
) -> Option<(Vec<u32>, Vec<u64>)> {
    let encoding = if compressed {
        Compress::Yes
    } else {
        Compress::No
    };
    let point_size = G1Affine::generator().serialized_size(encoding);
    if points.len() != scalars.len().checked_mul(point_size)? {
        return None;
    }
    let point_word_count = scalars.len().checked_mul(17)?;
    let scalar_word_count = scalars.len().checked_mul(4)?;
    let mut point_words = Vec::new();
    let mut scalar_limbs_soa = Vec::new();
    point_words.try_reserve_exact(point_word_count).ok()?;
    scalar_limbs_soa.try_reserve_exact(scalar_word_count).ok()?;
    point_words.resize(point_word_count, 0);
    scalar_limbs_soa.resize(scalar_word_count, 0);

    let prepare_one = |words: &mut [u32], point_bytes: &[u8], scalar: &Scalar| {
        let point = xark_groth16::decode::point::<G1Affine>(point_bytes, encoding).ok()?;
        if !point.is_on_curve() || Fr::from_bigint(BigInt(scalar.0)).is_none() {
            return None;
        }
        if point.is_zero() {
            words[16] = 1;
        } else {
            words[..8].copy_from_slice(&field_words(point.x));
            words[8..16].copy_from_slice(&field_words(point.y));
        }
        Some(())
    };

    if scalars.len() < PARALLEL_PREPARE_THRESHOLD {
        for (index, (point_bytes, scalar)) in
            points.chunks_exact(point_size).zip(scalars).enumerate()
        {
            prepare_one(
                &mut point_words[index * 17..(index + 1) * 17],
                point_bytes,
                scalar,
            )?;
        }
    } else {
        point_words
            .par_chunks_mut(17)
            .zip(points.par_chunks_exact(point_size))
            .zip(scalars.par_iter())
            .try_for_each(|((words, point_bytes), scalar)| {
                prepare_one(words, point_bytes, scalar)
            })?;
    }

    if scalars.len() < PARALLEL_PREPARE_THRESHOLD {
        for (index, scalar) in scalars.iter().enumerate() {
            for limb in 0..4 {
                scalar_limbs_soa[limb * scalars.len() + index] = scalar.0[limb];
            }
        }
    } else {
        for limb in 0..4 {
            scalar_limbs_soa[limb * scalars.len()..(limb + 1) * scalars.len()]
                .par_iter_mut()
                .zip(scalars.par_iter())
                .for_each(|(word, scalar)| *word = scalar.0[limb]);
        }
    }

    Some((point_words, scalar_limbs_soa))
}

fn decode_result(words: &[u32; 17]) -> Option<Vec<u8>> {
    if words[16] > 1 {
        return None;
    }
    let point = if words[16] == 1 {
        if words[..16].iter().any(|word| *word != 0) {
            return None;
        }
        G1Affine::zero()
    } else {
        let x = field_from_words(&words[..8])?;
        let y = field_from_words(&words[8..16])?;
        G1Affine::new_unchecked(x, y)
    };
    if !point.is_on_curve() {
        return None;
    }
    let mut bytes = Vec::new();
    point.serialize_uncompressed(&mut bytes).ok()?;
    Some(bytes)
}

impl Accelerator for CustomCudaMsm {
    fn wants_msm(&self) -> bool {
        #[cfg(feature = "custom-cuda")]
        {
            // SAFETY: this C function reads the CUDA device count and does not retain
            // pointers or access Rust-owned memory.
            unsafe { xark_cuda_device_available() }
        }
        #[cfg(not(feature = "custom-cuda"))]
        {
            false
        }
    }

    fn msm(
        &mut self,
        g2: bool,
        points: &[u8],
        compressed: bool,
        scalars: &[Scalar],
    ) -> Option<Vec<u8>> {
        #[cfg(not(feature = "custom-cuda"))]
        {
            let _ = (g2, points, compressed, scalars);
            return None;
        }
        #[cfg(feature = "custom-cuda")]
        {
            if g2 || !self.wants_msm() {
                return None;
            }
            let (point_words, scalar_limbs_soa) = prepare_inputs(points, compressed, scalars)?;
            let mut result_words = [0u32; 17];
            // SAFETY: slices provide the exact lengths expected by the C ABI, and
            // the native function copies all input data before returning.
            let status = unsafe {
                xark_cuda_msm_g1(
                    point_words.as_ptr(),
                    scalar_limbs_soa.as_ptr(),
                    scalars.len(),
                    result_words.as_mut_ptr(),
                )
            };
            if status != 0 {
                return None;
            }
            decode_result(&result_words)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{decode_result, field_from_words, field_words, prepare_inputs};
    use ark_bn254::{Fq, Fr, G1Affine};
    use ark_ec::AffineRepr;
    use ark_ff::PrimeField;
    use ark_serialize::{CanonicalSerialize, Compress};
    use xark_groth16::msm::Scalar;

    #[test]
    fn canonical_field_words_round_trip() {
        for value in [
            Fq::from(0u64),
            Fq::from(1u64),
            Fq::from(17u64),
            -Fq::from(1u64),
        ] {
            assert_eq!(field_from_words(&field_words(value)), Some(value));
        }
    }

    #[test]
    fn point_and_scalar_layout_matches_native_soa_contract() {
        let point = G1Affine::generator();
        let mut encoded = Vec::new();
        point
            .serialize_with_mode(&mut encoded, Compress::Yes)
            .unwrap();
        let scalars = [Scalar([5, 0, 0, 0]), Scalar([7, 0, 0, 0])];
        let (points, limbs) = prepare_inputs(&[encoded.clone(), encoded].concat(), true, &scalars)
            .expect("canonical inputs prepare");

        assert_eq!(points.len(), 34);
        assert_eq!(limbs, [5, 7, 0, 0, 0, 0, 0, 0]);
        assert_eq!(points[16], 0);
    }

    #[test]
    fn parallel_input_preparation_preserves_soa_limb_order() {
        let point = G1Affine::generator();
        let mut encoded_point = Vec::new();
        point.serialize_compressed(&mut encoded_point).unwrap();
        let scalars: Vec<_> = (0..super::PARALLEL_PREPARE_THRESHOLD)
            .map(|index| {
                Scalar([
                    index as u64,
                    2 * index as u64,
                    3 * index as u64,
                    4 * index as u64,
                ])
            })
            .collect();
        let encoded_points = encoded_point.repeat(super::PARALLEL_PREPARE_THRESHOLD);

        let (points, limbs) = prepare_inputs(&encoded_points, true, &scalars).unwrap();
        assert_eq!(points.len(), 17 * scalars.len());
        for limb in 0..4 {
            let start = limb * scalars.len();
            assert!(
                limbs[start..start + scalars.len()]
                    .iter()
                    .zip(&scalars)
                    .all(|(actual, scalar)| *actual == scalar.0[limb])
            );
        }
    }

    #[test]
    fn input_preparation_rejects_noncanonical_scalars_and_bad_lengths() {
        let point = G1Affine::generator();
        let mut encoded = Vec::new();
        point
            .serialize_with_mode(&mut encoded, Compress::Yes)
            .unwrap();
        let noncanonical = [xark_groth16::msm::Scalar(Fr::MODULUS.0)];
        assert!(prepare_inputs(&encoded, true, &noncanonical).is_none());
        assert!(
            prepare_inputs(
                &encoded[..encoded.len() - 1],
                true,
                &[xark_groth16::msm::Scalar([1, 0, 0, 0])]
            )
            .is_none()
        );

        let off_curve = G1Affine::new_unchecked(Fq::from(1u64), Fq::from(1u64));
        let mut off_curve_bytes = Vec::new();
        off_curve
            .serialize_compressed(&mut off_curve_bytes)
            .unwrap();
        assert!(prepare_inputs(&off_curve_bytes, true, &[Scalar([1, 0, 0, 0])]).is_none());
    }

    #[test]
    fn result_decoder_rejects_noncanonical_or_invalid_points() {
        let mut words = [0u32; 17];
        words[16] = 2;
        assert!(decode_result(&words).is_none());
        words[16] = 0;
        words[0] = u32::MAX;
        assert!(decode_result(&words).is_none());
        assert!(decode_result(&[0u32; 17]).is_none());
        let infinity = [0u32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
        assert!(decode_result(&infinity).is_some());
    }
}
