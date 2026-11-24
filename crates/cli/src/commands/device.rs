//! `xark prove --prover`: the prover that makes the proof. A device's set-up
//! (loading the runtime, its tables and its buffers' pages: about 100 ms for
//! OpenCL on an Apple M3 Max) runs on its own thread from the start of the
//! command, beside the witness solve; the device then proves beside the CPU
//! ([`xark_groth16::Accelerated`]), or declines a domain too small to repay its
//! fixed cost and leaves the proof to the CPU. A device's proof is always
//! checked ([`prove_checked`]).

use anyhow::Result;
use ark_bn254::{Bn254, Fr};
use rand::RngCore;
use xark_groth16::{
    Accelerated, Accelerator, ConstraintSource, Cpu, PkSource, Proof, ProveError, ProverConfig,
    prove_with_rng,
};

/// Prove with `device` beside the CPU, checking the proof whatever `cfg` says:
/// a device can compute a wrong MSM (a driver or compiler bug on hardware we
/// haven't tested), and the check is one pairing. A proof that fails it although
/// the witness satisfies every row is the device's fault, so the CPU proves
/// again; one that fails on a row is the witness's, reported as `--verify`
/// reports it. Returns the result, the key and device back, and whether the
/// CPU had to prove again.
// Built without a device too, so its test runs in every build.
#[cfg_attr(not(feature = "opencl"), allow(dead_code))]
pub(crate) fn prove_checked<D: Accelerator + Send, P: PkSource>(
    name: &str,
    device: D,
    pk: P,
    mut cfg: ProverConfig,
    src: &dyn ConstraintSource,
    z: &[Fr],
    rng: &mut impl RngCore,
) -> (Result<Proof<Bn254>, ProveError>, P, D, bool) {
    cfg.self_check = true;
    let mut prover = Accelerated::new(name, device, pk, cfg.clone());
    let proved = prove_with_rng(&mut prover, src, z, rng);
    let Accelerated { device, pk, .. } = prover;
    match proved {
        Err(ProveError::SelfCheckFailed) => {
            let mut cpu = Cpu::new(pk, cfg);
            let again = prove_with_rng(&mut cpu, src, z, rng);
            (again, cpu.pk, device, true)
        }
        proved => (proved, pk, device, false),
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum ProverKind {
    /// xark's prover on the CPU.
    #[default]
    Cpu,
    /// The quotient and the H MSM on an OpenCL GPU, the rest on the CPU (an
    /// `xark` built with `--features opencl`).
    Opencl,
}

/// A device being set up.
pub enum Pending {
    #[cfg(feature = "opencl")]
    OpenCl(opencl::Pending),
}

impl Pending {
    /// Start setting up `kind`'s device, if it has one. A GPU runs variable-time
    /// code on the witness, so it needs `acknowledged`.
    pub fn start(kind: ProverKind, acknowledged: bool) -> Result<Option<Pending>> {
        match kind {
            ProverKind::Cpu => Ok(None),
            ProverKind::Opencl if !acknowledged => anyhow::bail!(
                "a GPU MSM is variable-time and its buffers aren't guaranteed to be erased: \
                 prove on the CPU for secret inputs on shared or untrusted hardware, or pass \
                 --acknowledge-gpu-side-channel-risk for a trusted single-tenant device"
            ),
            #[cfg(feature = "opencl")]
            ProverKind::Opencl => Ok(Some(Pending::OpenCl(opencl::Pending::start()))),
            #[cfg(not(feature = "opencl"))]
            ProverKind::Opencl => anyhow::bail!(
                "this xark was built without OpenCL: `cargo install xark-cli --features opencl`"
            ),
        }
    }

    /// The QAP domain the proof will use, once the rows are known: the device
    /// prepares for it, if it takes it.
    pub fn hint(&mut self, _domain_size: usize) {
        match *self {
            #[cfg(feature = "opencl")]
            Pending::OpenCl(ref mut p) => p.hint(_domain_size),
        }
    }

    /// Prove on the device beside the CPU (or on the CPU, if it declines), and
    /// say which did: the result, the key back, and a line for the user.
    pub fn prove<P: PkSource>(
        self,
        _src: &dyn ConstraintSource,
        _z: &[Fr],
        _pk: P,
        _rng: &mut impl RngCore,
        _cfg: ProverConfig,
    ) -> (Result<Proof<Bn254>, ProveError>, P, String) {
        match self {
            #[cfg(feature = "opencl")]
            Pending::OpenCl(p) => p.prove(_src, _z, _pk, _rng, _cfg),
        }
    }
}

#[cfg(feature = "opencl")]
mod opencl {
    use std::sync::{Mutex, OnceLock, mpsc};
    use std::thread::JoinHandle;

    use ark_bn254::{Bn254, Fr};
    use rand::RngCore;
    use xark_groth16::{
        Accelerator, ConstraintSource, PkSource, Proof, ProveError, ProverConfig, prove_with_rng,
    };
    use xark_groth16_opencl::OpenClMsm;

    /// The device and its name, or `None` where OpenCL can't start.
    type SetUp = Option<(OpenClMsm, String)>;

    pub struct Pending {
        hint: Option<mpsc::Sender<usize>>,
        handle: JoinHandle<SetUp>,
        /// The device's smallest domain, known before its set-up ends, so a
        /// proof it would decline doesn't wait for that.
        min_domain: usize,
    }

    impl Pending {
        pub fn start() -> Self {
            let (hint, hinted) = mpsc::channel::<usize>();
            let device = OpenClMsm::from_env();
            let min_domain = device.min_domain();
            let handle = std::thread::spawn(move || {
                let mut device = device;
                if !device.initialize() {
                    return None;
                }
                let name = device
                    .device_info()
                    .map_or_else(|| "OpenCL".to_string(), |d| d.name.clone());
                if let Ok(n) = hinted.recv()
                    && device.wants_proof(n)
                {
                    device.prepare(n);
                }
                Some((device, name))
            });
            Pending {
                hint: Some(hint),
                handle,
                min_domain,
            }
        }

        pub fn hint(&mut self, domain_size: usize) {
            if let Some(hint) = self.hint.take() {
                let _ = hint.send(domain_size);
            }
        }

        pub fn prove<P: PkSource>(
            mut self,
            src: &dyn ConstraintSource,
            z: &[Fr],
            pk: P,
            rng: &mut impl RngCore,
            cfg: ProverConfig,
        ) -> (Result<Proof<Bn254>, ProveError>, P, String) {
            // A domain the device declines proves on the CPU now, leaving the
            // set-up thread to the process's exit.
            let n = pk.header().h_len + 1;
            if n < self.min_domain {
                let mut cpu = xark_groth16::Cpu::new(pk, cfg);
                let proved = prove_with_rng(&mut cpu, src, z, rng);
                let report = format!(
                    "proved on the CPU: OpenCL takes domains from {} points, this one has {n}",
                    self.min_domain
                );
                return (proved, cpu.pk, report);
            }
            // An unsent hint ends the set-up thread's wait.
            drop(self.hint.take());
            let device = Lazy {
                min_domain: self.min_domain,
                handle: Mutex::new(Some(self.handle)),
                ready: OnceLock::new(),
            };
            let (proved, pk, device, again) =
                super::prove_checked("opencl", device, pk, cfg, src, z, rng);
            let report = match device.ready.get() {
                Some(Some((_, name))) if again => format!(
                    "warning: the proof from OpenCL on {name} didn't verify although the inputs \
                     satisfy the circuit; proved again on the CPU"
                ),
                Some(Some((_, name))) => format!("proved with OpenCL on {name}, and verified"),
                _ => "OpenCL isn't available here: proved on the CPU".into(),
            };
            (proved, pk, report)
        }
    }

    /// The device as the prover sees it: joined the first time the prover asks
    /// it for work, so the CPU's MSMs start at once and only the device's first
    /// transform waits for what is left of the set-up (the quotient evaluates
    /// its rows first, on the CPU). Without OpenCL every request declines and
    /// the CPU does the work.
    struct Lazy {
        min_domain: usize,
        handle: Mutex<Option<JoinHandle<SetUp>>>,
        ready: OnceLock<SetUp>,
    }

    impl Lazy {
        fn get(&self) -> Option<&OpenClMsm> {
            self.ready
                .get_or_init(|| {
                    let handle = self.handle.lock().ok()?.take()?;
                    handle
                        .join()
                        .unwrap_or_else(|e| std::panic::resume_unwind(e))
                })
                .as_ref()
                .map(|(d, _)| d)
        }

        fn get_mut(&mut self) -> Option<&mut OpenClMsm> {
            self.get()?;
            self.ready.get_mut()?.as_mut().map(|(d, _)| d)
        }
    }

    impl Accelerator for Lazy {
        fn wants_proof(&self, domain_size: usize) -> bool {
            domain_size >= self.min_domain
        }
        fn to_coset(&mut self, dom: &xark_groth16::Domain, buf: &mut [Fr]) -> bool {
            self.get_mut().is_some_and(|d| d.to_coset(dom, buf))
        }
        fn from_coset_to_t(&mut self, dom: &xark_groth16::Domain, buf: &mut [Fr]) -> bool {
            self.get_mut().is_some_and(|d| d.from_coset_to_t(dom, buf))
        }
        fn ifft_to_t(&mut self, dom: &xark_groth16::Domain, buf: &mut [Fr]) -> bool {
            self.get_mut().is_some_and(|d| d.ifft_to_t(dom, buf))
        }
        fn wants_msm(&self) -> bool {
            self.get().is_some_and(|d| d.wants_msm())
        }
        fn wants_msm_for(&self, g2: bool, scalars: &[xark_groth16::msm::Scalar]) -> bool {
            self.get().is_some_and(|d| d.wants_msm_for(g2, scalars))
        }
        fn msm(
            &mut self,
            g2: bool,
            points: &[u8],
            compressed: bool,
            scalars: &[xark_groth16::msm::Scalar],
        ) -> Option<Vec<u8>> {
            self.get_mut()?.msm(g2, points, compressed, scalars)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ark_bn254::{Fr, G1Affine};
    use ark_serialize::{CanonicalSerialize, Compress};
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use xark_groth16::{
        Accelerator, ConstraintSource, DomainKind, ProgramSource, ProverConfig, SerializedPk,
    };
    use xark_ir::LinearCombination;
    use xark_ir::r1cs::{FieldSpec, R1csConstraint, R1csProgram, Variable, Visibility};

    use super::prove_checked;

    /// A device whose every MSM is the generator: a wrong proof, as a faulty
    /// driver would make it.
    struct Faulty;

    impl Accelerator for Faulty {
        fn wants_msm(&self) -> bool {
            true
        }
        fn msm(
            &mut self,
            g2: bool,
            _: &[u8],
            _: bool,
            _: &[xark_groth16::msm::Scalar],
        ) -> Option<Vec<u8>> {
            (!g2).then(|| {
                let mut out = Vec::new();
                let g = G1Affine::new_unchecked(
                    ark_bn254::g1::G1_GENERATOR_X,
                    ark_bn254::g1::G1_GENERATOR_Y,
                );
                g.serialize_uncompressed(&mut out).unwrap();
                out
            })
        }
    }

    /// A device that does nothing, so the CPU does all of it.
    struct Idle;

    impl Accelerator for Idle {}

    fn circuit() -> R1csProgram {
        let var = |id, visibility| Variable {
            id,
            name: format!("v{id}"),
            visibility,
        };
        R1csProgram {
            field: FieldSpec::bn254(),
            variables: vec![
                var(0, Visibility::Public),
                var(1, Visibility::Private),
                var(2, Visibility::Private),
            ],
            constraints: vec![R1csConstraint::mul(
                0,
                LinearCombination::var(1),
                LinearCombination::var(2),
                0,
                "factors",
            )],
        }
    }

    #[test]
    fn a_device_proof_that_fails_its_check_is_proved_again_on_the_cpu() {
        let prog = circuit();
        let src = ProgramSource::new(&prog);
        let z = src.layout().assignment_from_map(&BTreeMap::from([
            (0, Fr::from(6u64)),
            (1, Fr::from(2u64)),
            (2, Fr::from(3u64)),
        ]));
        let mut key = Vec::new();
        let vk = xark_groth16::setup::dev_setup(
            &src,
            &mut ChaCha20Rng::seed_from_u64(1),
            &mut key,
            Compress::Yes,
            DomainKind::Radix2,
        )
        .unwrap();
        let public = &z[1..src.layout().num_instance()];
        let cfg = ProverConfig::default();
        let rng = &mut ChaCha20Rng::seed_from_u64(2);

        let pk = SerializedPk::from_bytes(&key).unwrap();
        let (proof, _, _, again) = prove_checked("faulty", Faulty, pk, cfg.clone(), &src, &z, rng);
        assert!(again, "the faulty device's proof must fail its check");
        assert!(xark_groth16::verify(&vk, public, &proof.unwrap()).unwrap());

        let pk = SerializedPk::from_bytes(&key).unwrap();
        let (proof, _, _, again) = prove_checked("idle", Idle, pk, cfg, &src, &z, rng);
        assert!(!again);
        assert!(xark_groth16::verify(&vk, public, &proof.unwrap()).unwrap());
    }
}
