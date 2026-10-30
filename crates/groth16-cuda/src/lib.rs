//! Optional BN254 G1 MSM adapter backed by ICICLE.
//!
//! The adapter accepts Xark's canonical serialized proving-key points and scalar
//! integers, converts them to ICICLE's fixed-width limbs, and returns an arkworks
//! uncompressed point. G2 remains on the CPU path for now.

use std::sync::OnceLock;

use ark_bn254::{Fq, Fr, G1Affine};
use ark_ec::AffineRepr;
use ark_ff::{BigInt, PrimeField};
use ark_serialize::{CanonicalSerialize, Compress};
use icicle_bn254::curve::{BaseField, G1Projective as IcicleG1, ScalarField};
use icicle_core::{
    affine::Affine as IcicleAffine,
    msm::{self, MSMConfig},
    projective::Projective as IcicleProjective,
};
use icicle_runtime::{Device, memory::HostSlice, runtime};

use xark_groth16::{Accelerator, msm::Scalar};

type IcicleG1Affine = <IcicleG1 as IcicleProjective>::Affine;

/// MSM adapter. The runtime is loaded lazily so the default Xark build does not
/// initialize GPU support.
#[derive(Default)]
pub struct IcicleMsm;

static BACKEND_LOADED: OnceLock<bool> = OnceLock::new();

fn cuda_device_ready() -> bool {
    let loaded = BACKEND_LOADED.get_or_init(|| runtime::load_backend_from_env_or_default().is_ok());
    if !loaded {
        return false;
    }

    let device = Device::new("CUDA", 0);
    icicle_runtime::is_device_available(&device) && icicle_runtime::set_device(&device).is_ok()
}

fn ark_limbs_to_u32(limbs: [u64; 4]) -> [u32; 8] {
    std::array::from_fn(|i| {
        let word = limbs[i / 2];
        if i % 2 == 0 {
            word as u32
        } else {
            (word >> 32) as u32
        }
    })
}

fn ark_scalar_to_icicle(scalar: &Scalar) -> Option<ScalarField> {
    let scalar = Fr::from_bigint(BigInt(scalar.0))?;
    Some(ScalarField::from(ark_limbs_to_u32(scalar.into_bigint().0)))
}

fn icicle_base_to_ark(value: BaseField) -> Option<Fq> {
    let limbs: [u32; 8] = value.into();
    let words =
        std::array::from_fn(|i| u64::from(limbs[2 * i]) | (u64::from(limbs[2 * i + 1]) << 32));
    Fq::from_bigint(BigInt(words))
}

fn checked_uncompressed(point: G1Affine) -> Option<Vec<u8>> {
    if !point.is_on_curve() || !point.is_in_correct_subgroup_assuming_on_curve() {
        return None;
    }
    let mut bytes = Vec::new();
    point.serialize_uncompressed(&mut bytes).ok()?;
    Some(bytes)
}

fn prepare_g1_inputs(
    points: &[u8],
    compressed: bool,
    scalars: &[Scalar],
) -> Option<(Vec<IcicleG1Affine>, Vec<ScalarField>)> {
    let encoding = if compressed {
        Compress::Yes
    } else {
        Compress::No
    };
    let point_size = G1Affine::generator().serialized_size(encoding);
    let expected = scalars.len().checked_mul(point_size)?;
    if points.len() != expected {
        return None;
    }

    let mut device_points = Vec::with_capacity(scalars.len());
    let mut device_scalars = Vec::with_capacity(scalars.len());
    for (point_bytes, scalar) in points.chunks_exact(point_size).zip(scalars) {
        let point = xark_groth16::decode::point::<G1Affine>(point_bytes, encoding).ok()?;
        let scalar_is_zero = scalar.0.iter().all(|limb| *limb == 0);
        let scalar = ark_scalar_to_icicle(scalar)?;
        if point.is_zero() || scalar_is_zero {
            continue;
        }

        let x_limbs = ark_limbs_to_u32(point.x.into_bigint().0);
        let y_limbs = ark_limbs_to_u32(point.y.into_bigint().0);
        device_scalars.push(scalar);
        device_points.push(IcicleG1Affine::from_limbs(x_limbs, y_limbs));
    }

    Some((device_points, device_scalars))
}

impl Accelerator for IcicleMsm {
    fn wants_msm(&self) -> bool {
        cuda_device_ready()
    }

    fn msm(
        &mut self,
        g2: bool,
        points: &[u8],
        compressed: bool,
        scalars: &[Scalar],
    ) -> Option<Vec<u8>> {
        if g2 || !cuda_device_ready() {
            return None;
        }

        let (device_points, device_scalars) = prepare_g1_inputs(points, compressed, scalars)?;

        let mut result = [IcicleG1::zero()];
        if !device_points.is_empty() {
            msm::msm(
                HostSlice::from_slice(&device_scalars),
                HostSlice::from_slice(&device_points),
                &MSMConfig::default(),
                HostSlice::from_mut_slice(&mut result),
            )
            .ok()?;
        }

        let affine = result[0].to_affine();
        if affine == <IcicleG1 as IcicleProjective>::Affine::zero() {
            return checked_uncompressed(G1Affine::zero());
        }

        let x = icicle_base_to_ark(affine.x())?;
        let y = icicle_base_to_ark(affine.y())?;
        checked_uncompressed(G1Affine::new_unchecked(x, y))
    }
}

#[cfg(test)]
mod tests {
    use super::{
        IcicleG1Affine, ark_limbs_to_u32, ark_scalar_to_icicle, icicle_base_to_ark,
        prepare_g1_inputs,
    };
    use ark_bn254::{Fq, Fr, G1Affine};
    use ark_ec::AffineRepr;
    use ark_ff::PrimeField;
    use ark_serialize::{CanonicalSerialize, Compress};
    use icicle_bn254::curve::{BaseField, ScalarField};
    use icicle_core::affine::Affine as IcicleAffine;

    #[test]
    fn scalar_limbs_preserve_little_endian_word_order() {
        let value = Fr::from(0x0123_4567_89ab_cdefu64);
        let limbs = ark_limbs_to_u32(value.into_bigint().0);
        assert_eq!(limbs[0], 0x89ab_cdef);
        assert_eq!(limbs[1], 0x0123_4567);
        assert!(limbs[2..].iter().all(|limb| *limb == 0));

        let icicle = ScalarField::from(limbs);
        let converted: [u32; 8] = icicle.into();
        assert_eq!(converted, limbs);
    }

    #[test]
    fn scalar_conversion_accepts_canonical_values_only() {
        let zero = Fr::from(0u64).into_bigint();
        let maximum = (-Fr::from(1u64)).into_bigint();
        let modulus = ark_ff::BigInt::<4>(Fr::MODULUS.0);

        assert!(ark_scalar_to_icicle(&zero).is_some());
        assert!(ark_scalar_to_icicle(&maximum).is_some());
        assert!(ark_scalar_to_icicle(&modulus).is_none());
    }

    #[test]
    fn base_field_limbs_round_trip_to_arkworks() {
        let value = Fq::from(0xfedc_ba98_7654_3210u64);
        let limbs = ark_limbs_to_u32(value.into_bigint().0);
        let icicle = BaseField::from(limbs);
        assert_eq!(icicle_base_to_ark(icicle), Some(value));
    }

    #[test]
    fn input_preparation_converts_compressed_and_uncompressed_points() {
        let scalar = [Fr::from(7u64).into_bigint()];
        let generator = G1Affine::generator();
        let expected = IcicleG1Affine::from_limbs(
            ark_limbs_to_u32(generator.x.into_bigint().0),
            ark_limbs_to_u32(generator.y.into_bigint().0),
        );
        for (compressed, encoding) in [(true, Compress::Yes), (false, Compress::No)] {
            let mut encoded = Vec::new();
            generator
                .serialize_with_mode(&mut encoded, encoding)
                .unwrap();

            let (points, scalars) = prepare_g1_inputs(&encoded, compressed, &scalar).unwrap();
            assert_eq!(points, [expected]);
            assert_eq!(scalars, [ScalarField::from(ark_limbs_to_u32(scalar[0].0))]);
        }
    }

    #[test]
    fn input_preparation_declines_bad_lengths_points_and_scalars() {
        let scalar = [Fr::from(1u64).into_bigint()];
        assert!(prepare_g1_inputs(&[0; 31], true, &scalar).is_none());
        assert!(prepare_g1_inputs(&[0xff; 32], true, &scalar).is_none());

        let mut encoded = Vec::new();
        G1Affine::generator()
            .serialize_with_mode(&mut encoded, Compress::Yes)
            .unwrap();
        let noncanonical = [ark_ff::BigInt::<4>(Fr::MODULUS.0)];
        assert!(prepare_g1_inputs(&encoded, true, &noncanonical).is_none());
    }

    #[test]
    fn input_preparation_removes_infinity_and_zero_scalar_terms() {
        let mut encoded = Vec::new();
        G1Affine::zero()
            .serialize_with_mode(&mut encoded, Compress::Yes)
            .unwrap();
        G1Affine::generator()
            .serialize_with_mode(&mut encoded, Compress::Yes)
            .unwrap();
        let scalars = [Fr::from(1u64).into_bigint(), Fr::from(0u64).into_bigint()];

        let (points, converted_scalars) = prepare_g1_inputs(&encoded, true, &scalars).unwrap();
        assert!(points.is_empty());
        assert!(converted_scalars.is_empty());
    }
}
