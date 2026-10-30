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
use xark_groth16_cuda::IcicleMsm;

#[test]
fn cuda_g1_msm_matches_xark_cpu() {
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
    let mut rng = ChaCha20Rng::seed_from_u64(0x5841_524b_4d53_4d);
    for _ in 0..64 {
        let base_scalar = Fr::rand(&mut rng);
        let msm_scalar = Fr::rand(&mut rng);
        bases.push((G1Affine::generator() * base_scalar).into_affine());
        scalars.push(msm_scalar.into_bigint());
    }
    let mut encoded = Vec::new();
    for point in &bases {
        point.serialize_compressed(&mut encoded).unwrap();
    }

    let mut cuda = IcicleMsm;
    if !cuda.wants_msm() {
        if std::env::var_os("XARK_CUDA_REQUIRED").is_some() {
            panic!("XARK_CUDA_REQUIRED is set, but no CUDA backend is available");
        }
        eprintln!("skipping GPU comparison because CUDA is unavailable");
        return;
    }

    let got = cuda
        .msm(false, &encoded, true, &scalars)
        .expect("available CUDA device declined a valid G1 MSM");
    let expected_point = msm::<G1Projective>(&bases, &scalars).into_affine();
    let mut expected = Vec::new();
    expected_point
        .serialize_uncompressed(&mut expected)
        .unwrap();
    assert_eq!(got, expected);

    let mut encoded_uncompressed = Vec::new();
    for point in &bases {
        point
            .serialize_uncompressed(&mut encoded_uncompressed)
            .unwrap();
    }
    let got = cuda
        .msm(false, &encoded_uncompressed, false, &scalars)
        .expect("available CUDA device declined uncompressed G1 points");
    assert_eq!(got, expected);

    let got = cuda
        .msm(false, &[], true, &[])
        .expect("available CUDA device declined an empty MSM");
    let mut identity = Vec::new();
    G1Affine::zero()
        .serialize_uncompressed(&mut identity)
        .unwrap();
    assert_eq!(got, identity);
}

#[test]
fn g2_and_mismatched_buffers_decline_to_cpu() {
    let mut cuda = IcicleMsm;
    let scalar = Fr::from(1u64).into_bigint();

    assert!(cuda.msm(true, &[], true, &[scalar]).is_none());
    assert!(cuda.msm(false, &[0; 31], true, &[scalar]).is_none());
}
