use ark_bn254::{Fr, G1Affine, G1Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{PrimeField, UniformRand};
use ark_serialize::CanonicalSerialize;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use xark_groth16::{
    Accelerator,
    msm::{Scalar, msm},
};
use xark_groth16_opencl::{OpenClDeviceKind, OpenClMsm};

#[test]
fn opencl_g1_msm_matches_xark_cpu() {
    let mut bases = vec![
        G1Affine::generator(),
        G1Affine::generator(),
        -G1Affine::generator(),
        G1Affine::zero(),
        G1Affine::generator(),
        G1Affine::generator(),
    ];
    let mut scalars: Vec<Scalar> = [
        Fr::from(17u64),
        Fr::from(29u64),
        Fr::from(29u64),
        Fr::from(123u64),
        Fr::from(0u64),
        -Fr::from(1u64),
    ]
    .into_iter()
    .map(|value| value.into_bigint())
    .collect();
    let mut rng = ChaCha20Rng::seed_from_u64(0x5841_524b_4f50_454e);
    for _ in 0..8 {
        let base_scalar = Fr::rand(&mut rng);
        let msm_scalar = Fr::rand(&mut rng);
        bases.push((G1Affine::generator() * base_scalar).into_affine());
        scalars.push(msm_scalar.into_bigint());
    }
    let mut encoded = Vec::new();
    for point in &bases {
        point.serialize_compressed(&mut encoded).unwrap();
    }

    let mut opencl = OpenClMsm::with_device_kind(OpenClDeviceKind::Any);
    let Some(actual) = opencl.msm(false, &encoded, true, &scalars) else {
        if std::env::var_os("XARK_OPENCL_REQUIRED").is_some() {
            panic!("OpenCL runtime declined a valid G1 MSM");
        }
        eprintln!(
            "skipping OpenCL comparison because no usable OpenCL compiler/device is available"
        );
        return;
    };

    let expected_point = msm::<G1Projective>(&bases, &scalars).into_affine();
    let mut expected = Vec::new();
    expected_point
        .serialize_uncompressed(&mut expected)
        .unwrap();
    assert_eq!(actual, expected);
}

#[test]
fn unsupported_group_and_malformed_lengths_decline() {
    let mut opencl = OpenClMsm::new();
    let scalar = Fr::from(1u64).into_bigint();
    assert!(opencl.msm(true, &[], true, &[scalar]).is_none());
    assert!(opencl.msm(false, &[0; 31], true, &[scalar]).is_none());
}
