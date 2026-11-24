//! `xark prove --prover`: the prover that makes the proof. A device's set-up
//! (loading the runtime and building its kernels, about 250 ms for OpenCL on an
//! Apple M3 Max) runs on its own thread from the start of the command, beside
//! the witness solve; the device then proves beside the CPU
//! ([`xark_groth16::Accelerated`]), or declines a domain too small to repay its
//! fixed cost and leaves the proof to the CPU.

use anyhow::Result;
use ark_bn254::{Bn254, Fr};
use rand::RngCore;
use xark_groth16::{ConstraintSource, PkSource, Proof, ProveError, ProverConfig};

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
    use std::sync::mpsc;
    use std::thread::JoinHandle;

    use ark_bn254::{Bn254, Fr};
    use rand::RngCore;
    use xark_groth16::{
        Accelerated, Accelerator, ConstraintSource, PkSource, Proof, ProveError, ProverConfig,
        prove_with_rng,
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
            let set_up = self
                .handle
                .join()
                .unwrap_or_else(|e| std::panic::resume_unwind(e));
            let Some((device, name)) = set_up else {
                let mut cpu = xark_groth16::Cpu::new(pk, cfg);
                let proved = prove_with_rng(&mut cpu, src, z, rng);
                return (
                    proved,
                    cpu.pk,
                    "OpenCL isn't available here: proved on the CPU".into(),
                );
            };
            let mut prover = Accelerated::new("opencl", device, pk, cfg);
            let report = format!("proved with OpenCL on {name}");
            let proved = prove_with_rng(&mut prover, src, z, rng);
            (proved, prover.pk, report)
        }
    }
}
