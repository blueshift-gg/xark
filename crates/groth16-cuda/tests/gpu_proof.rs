use std::collections::BTreeMap;

use ark_bn254::Fr;
use ark_serialize::Compress;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use xark_groth16::r1cs::{FieldSpec, R1csConstraint, R1csProgram, Variable, Visibility};
use xark_groth16::{
    Accelerator, DomainKind, Local, ProgramSource, ProverConfig, SerializedPk, prove_accelerated,
    verify,
};
use xark_groth16_cuda::IcicleMsm;
use xark_ir::LinearCombination;

struct RequiredCudaMsm {
    inner: IcicleMsm,
    calls: usize,
}

impl Accelerator for RequiredCudaMsm {
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
            self.calls += 1;
            assert!(result.is_some(), "CUDA MSM declined a G1 proving-key chunk");
        }
        result
    }
}

#[test]
fn cuda_msm_produces_a_verifying_groth16_proof() {
    let inner = IcicleMsm;
    if !inner.wants_msm() {
        if std::env::var_os("XARK_CUDA_REQUIRED").is_some() {
            panic!("XARK_CUDA_REQUIRED is set, but no CUDA backend is available");
        }
        eprintln!("skipping proof-level GPU test because CUDA is unavailable");
        return;
    }
    let mut accelerator = RequiredCudaMsm { inner, calls: 0 };

    // The public output is 6. The private inputs 2 and 3 satisfy 2 * 3 = 6.
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
    let gpu_proof = prove_accelerated(
        &source,
        &witness,
        &mut SerializedPk::from_bytes(&key_bytes).expect("serialized key parses"),
        r,
        s,
        &cfg,
        &mut (),
        &mut accelerator,
    )
    .expect("GPU-accelerated proof generation succeeds");

    assert_eq!(
        gpu_proof, cpu_proof,
        "GPU and CPU proofs differ for fixed randomness"
    );
    let public_inputs = &witness[1..source.layout().num_instance()];
    assert!(verify(&vk, public_inputs, &gpu_proof).expect("public input count is valid"));
    assert!(
        accelerator.calls >= 2,
        "the proof path did not make multiple CUDA G1 MSM chunk calls"
    );
}
