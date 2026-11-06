#![cfg(feature = "custom-cuda")]

use std::collections::BTreeMap;

use ark_bn254::{Fr, G1Affine, G1Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{PrimeField, UniformRand};
use ark_serialize::{CanonicalSerialize, Compress};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use xark_groth16::{
    Accelerator, ConstraintSource, DomainKind, Local, ProgramSource, ProverConfig, SerializedPk,
    msm::{Scalar, msm},
    prove_accelerated, verify,
};
use xark_groth16_cuda::CustomCudaMsm;
use xark_ir::LinearCombination;
use xark_ir::r1cs::{FieldSpec, R1csConstraint, R1csProgram, Variable, Visibility};

#[test]
fn custom_cuda_g1_msm_matches_xark_cpu() {
    let mut rng = ChaCha20Rng::seed_from_u64(0x5841_524b_4355_5354);
    let mut bases = vec![
        G1Affine::generator(),
        -G1Affine::generator(),
        G1Affine::zero(),
        (G1Affine::generator() * Fr::from(2048u64)).into_affine(),
    ];
    let mut scalars: Vec<Scalar> = [
        Fr::from(0u64),
        Fr::from(1u64),
        -Fr::from(1u64),
        Fr::from(2049u64),
    ]
    .into_iter()
    .map(|value| value.into_bigint())
    .collect();
    for _ in 0..64 {
        bases.push((G1Affine::generator() * Fr::rand(&mut rng)).into_affine());
        scalars.push(Fr::rand(&mut rng).into_bigint());
    }

    let mut encoded = Vec::new();
    for point in &bases {
        point.serialize_compressed(&mut encoded).unwrap();
    }

    let mut custom = CustomCudaMsm;
    assert!(
        custom.wants_msm(),
        "custom CUDA feature is enabled but no CUDA device is available"
    );
    let got = custom
        .msm(false, &encoded, true, &scalars)
        .expect("custom CUDA MSM declined valid G1 inputs");
    let expected_point = msm::<G1Projective>(&bases, &scalars).into_affine();
    let mut expected = Vec::new();
    expected_point
        .serialize_uncompressed(&mut expected)
        .unwrap();
    assert_eq!(got, expected);

    let mut uncompressed = Vec::new();
    for point in &bases {
        point.serialize_uncompressed(&mut uncompressed).unwrap();
    }
    assert_eq!(
        custom
            .msm(false, &uncompressed, false, &scalars)
            .expect("custom CUDA MSM declined uncompressed points"),
        expected
    );

    let mut identity = Vec::new();
    G1Affine::zero()
        .serialize_uncompressed(&mut identity)
        .unwrap();
    assert_eq!(
        custom
            .msm(false, &[], true, &[])
            .expect("custom CUDA MSM declined empty input"),
        identity
    );
    assert!(custom.msm(true, &[], true, &[]).is_none());
    assert!(
        custom
            .msm(false, &[0; 31], true, &[Fr::from(1u64).into_bigint()])
            .is_none()
    );
}

struct RequiredCustomCuda {
    inner: CustomCudaMsm,
    nonempty_g1_calls: usize,
}

fn has_nonempty_g1_msm(points: &[u8], compressed: bool, scalars: &[Scalar]) -> bool {
    let encoding = if compressed {
        Compress::Yes
    } else {
        Compress::No
    };
    let point_size = G1Affine::generator().serialized_size(encoding);
    scalars
        .iter()
        .zip(points.chunks_exact(point_size))
        .any(|(scalar, bytes)| {
            let point = xark_groth16::decode::point::<G1Affine>(bytes, encoding)
                .expect("prover supplies valid G1 points");
            scalar.0.iter().any(|limb| *limb != 0) && !point.is_zero()
        })
}

impl Accelerator for RequiredCustomCuda {
    fn wants_msm(&self) -> bool {
        true
    }

    fn msm(
        &mut self,
        g2: bool,
        points: &[u8],
        compressed: bool,
        scalars: &[Scalar],
    ) -> Option<Vec<u8>> {
        let has_work = !g2 && has_nonempty_g1_msm(points, compressed, scalars);
        let result = self.inner.msm(g2, points, compressed, scalars);
        if !g2 {
            assert!(result.is_some(), "custom CUDA kernel declined a G1 chunk");
            if has_work {
                self.nonempty_g1_calls += 1;
            }
        }
        result
    }
}

#[test]
fn custom_cuda_msm_produces_a_verifying_groth16_proof() {
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
    let r = Fr::from(11u64);
    let s = Fr::from(13u64);
    let config = ProverConfig {
        msm_chunk: 2,
        self_check: true,
        ..ProverConfig::default()
    };
    let public_inputs = &witness[1..source.layout().num_instance()];

    let cpu_proof = prove_accelerated(
        &source,
        &witness,
        &mut SerializedPk::from_bytes(&key_bytes).unwrap(),
        r,
        s,
        &config,
        &mut (),
        &mut Local,
    )
    .expect("CPU proof generation succeeds");
    assert!(verify(&vk, public_inputs, &cpu_proof).unwrap());

    let mut required = RequiredCustomCuda {
        inner: CustomCudaMsm,
        nonempty_g1_calls: 0,
    };
    assert!(
        required.inner.wants_msm(),
        "CUDA device is required for this test"
    );
    let custom_proof = prove_accelerated(
        &source,
        &witness,
        &mut SerializedPk::from_bytes(&key_bytes).unwrap(),
        r,
        s,
        &config,
        &mut (),
        &mut required,
    )
    .expect("custom CUDA proof generation succeeds");

    assert!(required.nonempty_g1_calls > 0);
    assert_eq!(custom_proof, cpu_proof);
    assert!(verify(&vk, public_inputs, &custom_proof).unwrap());
}
