use std::collections::BTreeMap;

use ark_bn254::{Fr, G1Affine};
use ark_ec::AffineRepr;
use ark_serialize::{CanonicalSerialize, Compress};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use xark_groth16::{
    Accelerator, ConstraintSource, DomainKind, Local, ProgramSource, ProverConfig, SerializedPk,
    prove_accelerated, verify,
};
use xark_groth16_opencl::{OpenClDeviceKind, OpenClMsm};
use xark_ir::LinearCombination;
use xark_ir::r1cs::{FieldSpec, R1csConstraint, R1csProgram, Variable, Visibility};

struct RequiredOpenClMsm {
    inner: OpenClMsm,
    nonempty_calls: usize,
}

impl Accelerator for RequiredOpenClMsm {
    fn wants_msm(&self) -> bool {
        true
    }

    fn msm(
        &mut self,
        g2: bool,
        points: &[u8],
        compressed: bool,
        scalars: &[xark_groth16::msm::Scalar],
    ) -> Option<Vec<u8>> {
        let result = self.inner.msm(g2, points, compressed, scalars);
        if !g2 {
            assert!(
                result.is_some(),
                "OpenCL MSM declined a G1 proving-key chunk"
            );
            if scalars.iter().any(|s| s.0.iter().any(|limb| *limb != 0)) {
                self.nonempty_calls += 1;
            }
        }
        result
    }
}

#[test]
fn opencl_msm_produces_a_verifying_groth16_proof() {
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
    let cfg = ProverConfig {
        msm_chunk: 2,
        self_check: true,
        ..ProverConfig::default()
    };
    let cpu_proof = prove_accelerated(
        &source,
        &witness,
        &mut SerializedPk::from_bytes(&key_bytes).expect("serialized key parses"),
        r,
        s,
        &cfg,
        &mut (),
        &mut Local,
    )
    .expect("CPU proof generation succeeds");
    let public_inputs = &witness[1..source.layout().num_instance()];
    assert!(verify(&vk, public_inputs, &cpu_proof).expect("input count is valid"));

    let mut inner = OpenClMsm::with_device_kind(OpenClDeviceKind::Any);
    if !inner.initialize() {
        if std::env::var_os("XARK_OPENCL_REQUIRED").is_some() {
            panic!("OpenCL runtime or compiler is unavailable for required proof test");
        }
        eprintln!("CPU proof passed; skipping OpenCL proof because initialization failed");
        return;
    }
    let mut accelerator = RequiredOpenClMsm {
        inner,
        nonempty_calls: 0,
    };
    let opencl_proof = prove_accelerated(
        &source,
        &witness,
        &mut SerializedPk::from_bytes(&key_bytes).expect("serialized key parses"),
        r,
        s,
        &cfg,
        &mut (),
        &mut accelerator,
    )
    .expect("OpenCL-backed proof generation succeeds");
    assert!(accelerator.nonempty_calls > 0);
    assert_eq!(opencl_proof, cpu_proof);
    assert!(verify(&vk, public_inputs, &opencl_proof).expect("input count is valid"));
}
