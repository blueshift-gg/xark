//! Optional BN254 G1 MSM adapter backed by ICICLE.
//!
//! The adapter accepts Xark's canonical serialized proving-key points and scalar
//! integers, converts them to ICICLE's fixed-width limbs, and returns an arkworks
//! uncompressed point. G2 remains on the CPU path for now.

use std::sync::OnceLock;
use std::{cmp::min, ops::Range};

use ark_bn254::{Fq, Fr, G1Affine, G1Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInt, PrimeField, Zero};
use ark_serialize::{CanonicalSerialize, Compress};
use icicle_bn254::curve::{BaseField, G1Projective as IcicleG1, ScalarField};
use icicle_core::{
    affine::Affine as IcicleAffine,
    msm::{self, MSMConfig},
    projective::Projective as IcicleProjective,
};
use icicle_runtime::{Device, memory::HostSlice, runtime};
use rayon::prelude::*;

use xark_groth16::{Accelerator, msm::Scalar};

mod custom_cuda;
pub use custom_cuda::CustomCudaMsm;

type IcicleG1Affine = <IcicleG1 as IcicleProjective>::Affine;
const PARALLEL_PREPARE_THRESHOLD: usize = 1024;

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
    if !point.is_on_curve() {
        return None;
    }
    let mut bytes = Vec::new();
    point.serialize_uncompressed(&mut bytes).ok()?;
    Some(bytes)
}

// This adapter requests one result, and ICICLE narrows its per-MSM count to i32.
fn icicle_msm_count(scalar_count: usize) -> Option<i32> {
    i32::try_from(scalar_count).ok()
}

fn icicle_point_chunks(
    scalar_count: usize,
    point_size: usize,
    max_scalars: usize,
) -> Option<Vec<Range<usize>>> {
    if max_scalars == 0 {
        return None;
    }
    scalar_count.checked_mul(point_size)?;
    let mut ranges = Vec::new();
    let mut first_scalar = 0;
    while first_scalar < scalar_count {
        let end_scalar = min(first_scalar.checked_add(max_scalars)?, scalar_count);
        ranges.push(first_scalar.checked_mul(point_size)?..end_scalar.checked_mul(point_size)?);
        first_scalar = end_scalar;
    }
    Some(ranges)
}

fn icicle_msm_config() -> MSMConfig {
    let mut config = MSMConfig::default();
    config.are_scalars_montgomery_form = false;
    config.are_bases_montgomery_form = false;
    config.is_async = false;
    config
}

fn icicle_msm_g1(points: &[u8], compressed: bool, scalars: &[Scalar]) -> Option<G1Affine> {
    icicle_msm_count(scalars.len())?;
    let (device_points, device_scalars) = prepare_g1_inputs(points, compressed, scalars)?;
    if device_points.is_empty() {
        return Some(G1Affine::zero());
    }

    let mut result = [IcicleG1::zero()];
    msm::msm(
        HostSlice::from_slice(&device_scalars),
        HostSlice::from_slice(&device_points),
        &icicle_msm_config(),
        HostSlice::from_mut_slice(&mut result),
    )
    .ok()?;

    let affine = result[0].to_affine();
    if affine == <IcicleG1 as IcicleProjective>::Affine::zero() {
        return Some(G1Affine::zero());
    }
    let x = icicle_base_to_ark(affine.x())?;
    let y = icicle_base_to_ark(affine.y())?;
    let point = G1Affine::new_unchecked(x, y);
    point.is_on_curve().then_some(point)
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

    let prepare_one = |point_bytes: &[u8], scalar: &Scalar| {
        let point = xark_groth16::decode::point::<G1Affine>(point_bytes, encoding).ok()?;
        if !point.is_on_curve() {
            return None;
        }
        let scalar_is_zero = scalar.0.iter().all(|limb| *limb == 0);
        let scalar = ark_scalar_to_icicle(scalar)?;
        Some(if point.is_zero() || scalar_is_zero {
            None
        } else {
            let x_limbs = ark_limbs_to_u32(point.x.into_bigint().0);
            let y_limbs = ark_limbs_to_u32(point.y.into_bigint().0);
            Some((IcicleG1Affine::from_limbs(x_limbs, y_limbs), scalar))
        })
    };
    let mut prepared = Vec::with_capacity(scalars.len());
    if scalars.len() < PARALLEL_PREPARE_THRESHOLD {
        for (point_bytes, scalar) in points.chunks_exact(point_size).zip(scalars) {
            if let Some(term) = prepare_one(point_bytes, scalar)? {
                prepared.push(term);
            }
        }
    } else {
        prepared = points
            .par_chunks_exact(point_size)
            .zip(scalars.par_iter())
            .try_fold(Vec::new, |mut output, (point_bytes, scalar)| {
                if let Some(term) = prepare_one(point_bytes, scalar)? {
                    output.push(term);
                }
                Some(output)
            })
            .try_reduce(Vec::new, |mut left, mut right| {
                left.append(&mut right);
                Some(left)
            })?;
    }
    let (device_points, device_scalars) = prepared.into_iter().unzip();

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
        let encoding = if compressed {
            Compress::Yes
        } else {
            Compress::No
        };
        let point_size = G1Affine::generator().serialized_size(encoding);
        if points.len() != scalars.len().checked_mul(point_size)? {
            return None;
        }

        let max_chunk = i32::MAX as usize;
        let ranges = icicle_point_chunks(scalars.len(), point_size, max_chunk)?;
        let mut total = G1Projective::zero();
        for (range, scalar_chunk) in ranges.into_iter().zip(scalars.chunks(max_chunk)) {
            let chunk = icicle_msm_g1(&points[range], compressed, scalar_chunk)?;
            total += chunk;
        }
        checked_uncompressed(total.into_affine())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::{
        IcicleG1Affine, PARALLEL_PREPARE_THRESHOLD, ark_limbs_to_u32, ark_scalar_to_icicle,
        icicle_base_to_ark, icicle_msm_config, icicle_msm_count, icicle_point_chunks,
        prepare_g1_inputs,
    };
    use ark_bn254::{Fq, Fr, G1Affine};
    use ark_ec::AffineRepr;
    use ark_ff::PrimeField;
    use ark_serialize::{CanonicalSerialize, Compress};
    use icicle_bn254::curve::{BaseField, ScalarField};
    use icicle_core::affine::Affine as IcicleAffine;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use xark_groth16::{
        ConstraintSource, DomainKind, Local, ProgramSource, ProverConfig, SerializedPk,
        prove_accelerated, verify,
    };
    use xark_ir::LinearCombination;
    use xark_ir::r1cs::{FieldSpec, R1csConstraint, R1csProgram, Variable, Visibility};

    #[test]
    fn adapter_matches_cpu_proof_and_verifies() {
        let program = R1csProgram {
            field: FieldSpec::bn254(),
            variables: vec![
                Variable {
                    id: 0,
                    name: "out".into(),
                    visibility: Visibility::Public,
                },
                Variable {
                    id: 1,
                    name: "left".into(),
                    visibility: Visibility::Private,
                },
                Variable {
                    id: 2,
                    name: "right".into(),
                    visibility: Visibility::Private,
                },
            ],
            constraints: vec![R1csConstraint::mul(
                0,
                LinearCombination::var(1),
                LinearCombination::var(2),
                0,
                "private factors match public output",
            )],
        };
        let assignment = BTreeMap::from([
            (0, Fr::from(6u64)),
            (1, Fr::from(2u64)),
            (2, Fr::from(3u64)),
        ]);
        let source = ProgramSource::new(&program);
        let witness = source.layout().assignment_from_map(&assignment);

        let mut key_bytes = Vec::new();
        let vk = xark_groth16::setup::dev_setup(
            &source,
            &mut ChaCha20Rng::seed_from_u64(0x5841_524b),
            &mut key_bytes,
            Compress::Yes,
            DomainKind::Radix2,
        )
        .expect("test circuit setup succeeds");
        let proof = prove_accelerated(
            &source,
            &witness,
            &mut SerializedPk::from_bytes(&key_bytes).expect("serialized key parses"),
            Fr::from(11u64),
            Fr::from(13u64),
            &ProverConfig {
                msm_chunk: 2,
                self_check: true,
                ..ProverConfig::default()
            },
            &mut (),
            &mut Local,
        )
        .expect("CPU proof generation succeeds");

        let public_inputs = &witness[1..source.layout().num_instance()];
        assert!(verify(&vk, public_inputs, &proof).expect("public input count is valid"));

        let adapter_proof = prove_accelerated(
            &source,
            &witness,
            &mut SerializedPk::from_bytes(&key_bytes).expect("serialized key parses"),
            Fr::from(11u64),
            Fr::from(13u64),
            &ProverConfig {
                msm_chunk: 2,
                self_check: true,
                ..ProverConfig::default()
            },
            &mut (),
            &mut super::IcicleMsm,
        )
        .expect("adapter proof generation succeeds or falls back to CPU");

        assert_eq!(adapter_proof, proof, "adapter and CPU proofs differ");
        assert!(verify(&vk, public_inputs, &adapter_proof).expect("public input count is valid"));
    }

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
    fn msm_count_must_fit_icicles_signed_ffi_parameter() {
        assert_eq!(icicle_msm_count(0), Some(0));
        assert_eq!(icicle_msm_count(i32::MAX as usize), Some(i32::MAX));
        let first_unsupported = (i32::MAX as usize) + 1;
        assert_eq!(icicle_msm_count(first_unsupported), None);
    }

    #[test]
    fn oversized_icicle_calls_split_on_point_boundaries() {
        assert_eq!(
            icicle_point_chunks(5, 3, 2),
            Some(vec![0..6, 6..12, 12..15])
        );
        assert_eq!(icicle_point_chunks(0, 3, 2), Some(vec![]));
        assert_eq!(icicle_point_chunks(1, 3, 0), None);
        assert_eq!(icicle_point_chunks(usize::MAX, 3, 2), None);
    }

    #[test]
    fn msm_config_uses_canonical_inputs_and_waits_for_the_result() {
        let config = icicle_msm_config();

        assert!(!config.are_scalars_montgomery_form);
        assert!(!config.are_bases_montgomery_form);
        assert!(!config.is_async);
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
    fn parallel_input_preparation_preserves_point_scalar_pairs() {
        let generator = G1Affine::generator();
        let negative_generator = -generator;
        let scalars: Vec<_> = (0..PARALLEL_PREPARE_THRESHOLD)
            .map(|index| Fr::from(index as u64 + 1).into_bigint())
            .collect();
        let mut encoded = Vec::new();
        for index in 0..PARALLEL_PREPARE_THRESHOLD {
            let point = if index % 2 == 0 {
                generator
            } else {
                negative_generator
            };
            point.serialize_compressed(&mut encoded).unwrap();
        }

        let (points, converted_scalars) = prepare_g1_inputs(&encoded, true, &scalars).unwrap();
        assert_eq!(points.len(), PARALLEL_PREPARE_THRESHOLD);
        assert_eq!(converted_scalars.len(), PARALLEL_PREPARE_THRESHOLD);
        for (point, scalar) in points.iter().zip(converted_scalars) {
            let scalar_limbs: [u32; 8] = scalar.into();
            let expected = if scalar_limbs[0] % 2 == 1 {
                IcicleG1Affine::from_limbs(
                    ark_limbs_to_u32(generator.x.into_bigint().0),
                    ark_limbs_to_u32(generator.y.into_bigint().0),
                )
            } else {
                IcicleG1Affine::from_limbs(
                    ark_limbs_to_u32(negative_generator.x.into_bigint().0),
                    ark_limbs_to_u32(negative_generator.y.into_bigint().0),
                )
            };
            assert_eq!(point, &expected);
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
    fn input_preparation_rejects_off_curve_uncompressed_points() {
        let invalid = G1Affine::new_unchecked(Fq::from(1u64), Fq::from(1u64));
        let mut encoded = Vec::new();
        invalid
            .serialize_with_mode(&mut encoded, Compress::No)
            .unwrap();

        let scalar = [Fr::from(1u64).into_bigint()];
        assert!(prepare_g1_inputs(&encoded, false, &scalar).is_none());
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
