//! The on-device MSM pipeline and coset transforms against the CPU.
//! Skips when no OpenCL device is usable unless `XARK_OPENCL_REQUIRED` is set.

use ark_bn254::{Fr, G1Affine, G1Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{FftField, Field, PrimeField, UniformRand};
use ark_serialize::{CanonicalSerialize, Compress};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use xark_groth16::{
    Accelerator, Domain, FftConfig,
    msm::{Scalar, msm},
};
use xark_groth16_opencl::{OpenClDeviceKind, OpenClMsm};

fn device() -> Option<OpenClMsm> {
    let mut backend = OpenClMsm::with_device_index(OpenClDeviceKind::Any, 0);
    if backend.initialize() {
        return Some(backend);
    }
    assert!(
        std::env::var_os("XARK_OPENCL_REQUIRED").is_none(),
        "no usable OpenCL device"
    );
    eprintln!("skipping: no usable OpenCL device");
    None
}

/// Random points (some at infinity, some repeated or negated) and a scalar mix:
/// uniform, small, zero, one, r − 1 and values just below the window edges.
fn inputs(n: usize, seed: u64) -> (Vec<G1Affine>, Vec<Scalar>) {
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let g = G1Affine::generator();
    let mut bases = Vec::with_capacity(n);
    for i in 0..n {
        bases.push(match i % 97 {
            0 => G1Affine::zero(),
            1 if i > 1 => bases[i - 1],
            2 if i > 2 => -bases[i - 1],
            _ => (g * Fr::rand(&mut rng)).into_affine(),
        });
    }
    let minus_one = -Fr::from(1u64);
    let scalars = (0..n)
        .map(|i| {
            let x = match i % 7 {
                0..=2 => Fr::rand(&mut rng),
                3 => Fr::from(rng.gen_range(0u64..4)),
                4 => Fr::from(rng.gen_range(0u64..1 << 20)),
                5 => minus_one,
                _ => Fr::from((1u64 << rng.gen_range(1..64)) - 1),
            };
            x.into_bigint()
        })
        .collect();
    (bases, scalars)
}

fn encode(points: &[G1Affine], compress: Compress) -> Vec<u8> {
    let mut out = Vec::new();
    for p in points {
        p.serialize_with_mode(&mut out, compress).unwrap();
    }
    out
}

#[test]
fn pipeline_msm_matches_the_cpu_for_both_encodings() {
    let Some(mut gpu) = device() else { return };
    for (n, seed) in [(256, 1), (1000, 2), (20_000, 3), (70_000, 4)] {
        let (bases, scalars) = inputs(n, seed);
        let expected = msm::<G1Projective>(&bases, &scalars).into_affine();
        let mut expected_bytes = Vec::new();
        expected
            .serialize_uncompressed(&mut expected_bytes)
            .unwrap();
        for compress in [Compress::No, Compress::Yes] {
            let got = gpu
                .msm(
                    false,
                    &encode(&bases, compress),
                    compress == Compress::Yes,
                    &scalars,
                )
                .expect("the GPU accepts a valid MSM");
            assert_eq!(
                got,
                expected_bytes,
                "n={n} compressed={}",
                compress == Compress::Yes
            );
        }
    }
}

#[test]
fn pipeline_msm_declines_invalid_inputs() {
    let Some(mut gpu) = device() else { return };
    let (bases, mut scalars) = inputs(512, 5);
    let mut raw = encode(&bases, Compress::No);
    // A point off the curve: bump x of the second point.
    raw[64] ^= 1;
    assert!(gpu.msm(false, &raw, false, &scalars).is_none());
    // A non-canonical scalar.
    let raw = encode(&bases, Compress::No);
    scalars[7] = ark_ff::BigInt([u64::MAX; 4]);
    assert!(gpu.msm(false, &raw, false, &scalars).is_none());
}

#[test]
fn coset_transforms_match_the_cpu_domain() {
    let Some(mut gpu) = device() else { return };
    let mut rng = ChaCha20Rng::seed_from_u64(6);
    for log in [12u32, 13, 16] {
        let dom = Domain::new(1 << log, FftConfig::default()).unwrap();
        let input: Vec<Fr> = (0..dom.n).map(|_| Fr::rand(&mut rng)).collect();

        let mut expected = input.clone();
        dom.to_coset(&mut expected, Fr::GENERATOR);
        let mut got = input.clone();
        assert!(gpu.to_coset(&dom, &mut got), "log {log}");
        assert!(got == expected, "to_coset log {log}");

        let mut expected = input.clone();
        dom.from_coset_to_t(&mut expected, Fr::GENERATOR.inverse().unwrap());
        let mut got = input;
        assert!(gpu.from_coset_to_t(&dom, &mut got), "log {log}");
        assert!(
            got == expected,
            "from_coset_to_t log {log} (n1={} n2={})",
            dom.n1,
            dom.n2
        );
    }
}
