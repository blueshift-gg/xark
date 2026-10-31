use anyhow::{Context, Result};
use clap::{Args, Parser, Subcommand, ValueEnum};
use xark_cli::commands::prove::{ProveArgs, run_with_accelerator};
use xark_groth16::{Accelerator, Local};

#[derive(Parser)]
#[command(
    name = "xark-gpu",
    about = "Run Xark proving with an optional GPU MSM backend"
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Prove with Xark's existing setup artifacts.
    Prove(ProveCommand),
}

#[derive(Args)]
struct ProveCommand {
    #[command(flatten)]
    args: ProveArgs,

    /// MSM backend. CPU remains available when a GPU backend declines a chunk.
    #[arg(long, value_enum, default_value_t = Backend::Cpu)]
    accelerator: Backend,

    /// OpenCL device class. `any` includes CPU OpenCL runtimes such as POCL.
    #[arg(long, value_enum, default_value_t = OpenclDevice::Gpu)]
    opencl_device: OpenclDevice,

    /// Accept GPU MSM timing side-channel risk. GPU backends are not verified constant-time.
    #[arg(long)]
    acknowledge_gpu_side_channel_risk: bool,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
enum Backend {
    #[default]
    Cpu,
    Cuda,
    Opencl,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
enum OpenclDevice {
    #[default]
    Gpu,
    Any,
}

struct TrackedAccelerator {
    inner: Box<dyn Accelerator>,
    backend: Backend,
    available: bool,
    used_g1_chunks: usize,
    cpu_fallback_g1_chunks: usize,
}

impl TrackedAccelerator {
    fn new(
        backend: Backend,
        opencl_device: OpenclDevice,
        acknowledge_gpu_side_channel_risk: bool,
    ) -> Result<Self> {
        if backend != Backend::Cpu && !acknowledge_gpu_side_channel_risk {
            anyhow::bail!(
                "GPU MSM backends are not verified constant-time; use CPU or pass --acknowledge-gpu-side-channel-risk only on hardware you trust"
            );
        }
        let inner: Box<dyn Accelerator> = match backend {
            Backend::Cpu => Box::new(Local),
            Backend::Cuda => {
                #[cfg(feature = "custom-cuda-msm")]
                {
                    Box::new(xark_groth16_cuda::CustomCudaMsm)
                }
                #[cfg(all(feature = "cuda-msm", not(feature = "custom-cuda-msm")))]
                {
                    Box::new(xark_groth16_cuda::IcicleMsm)
                }
                #[cfg(not(feature = "cuda-msm"))]
                anyhow::bail!("CUDA MSM is not built in; enable `cuda-msm` or `custom-cuda-msm`");
            }
            Backend::Opencl => {
                #[cfg(feature = "opencl-msm")]
                {
                    let opencl = match opencl_device {
                        OpenclDevice::Gpu => xark_groth16_opencl::OpenClMsm::new(),
                        OpenclDevice::Any => xark_groth16_opencl::OpenClMsm::with_any_device(),
                    };
                    Box::new(opencl)
                }
                #[cfg(not(feature = "opencl-msm"))]
                anyhow::bail!("OpenCL MSM is not built in; enable `opencl-msm`");
            }
        };
        let available = inner.wants_msm();
        Ok(Self {
            inner,
            backend,
            available,
            used_g1_chunks: 0,
            cpu_fallback_g1_chunks: 0,
        })
    }

    fn report(&self) {
        if self.backend == Backend::Cpu {
            eprintln!("MSM backend: CPU Pippenger");
        } else if !self.available || self.used_g1_chunks == 0 {
            eprintln!(
                "requested {:?} backend handled no G1 chunks; CPU Pippenger handled the MSMs",
                self.backend
            );
        } else {
            eprintln!(
                "MSM backend: {:?} handled {} G1 chunks; {} G1 chunks used CPU fallback",
                self.backend, self.used_g1_chunks, self.cpu_fallback_g1_chunks
            );
        }
    }
}

impl Accelerator for TrackedAccelerator {
    fn wants_msm(&self) -> bool {
        self.available
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
            if result.is_some() {
                self.used_g1_chunks += 1;
            } else {
                self.cpu_fallback_g1_chunks += 1;
            }
        }
        result
    }
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Command::Prove(args) => {
            let mut accelerator = TrackedAccelerator::new(
                args.accelerator,
                args.opencl_device,
                args.acknowledge_gpu_side_channel_risk,
            )?;
            run_with_accelerator(args.args, &mut accelerator)
                .context("running Xark's streaming prover")?;
            accelerator.report();
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use clap::Parser;

    use super::{Backend, Cli, Command, OpenclDevice, TrackedAccelerator};
    use xark_groth16::Accelerator;

    #[test]
    fn parses_each_msm_backend() {
        for (name, expected) in [
            ("cpu", Backend::Cpu),
            ("cuda", Backend::Cuda),
            ("opencl", Backend::Opencl),
        ] {
            let cli = Cli::try_parse_from([
                "xark-gpu",
                "prove",
                "--accelerator",
                name,
                "--inputs",
                "{}",
                "--opencl-device",
                "any",
                "--acknowledge-gpu-side-channel-risk",
            ])
            .unwrap();
            let command = match cli.command {
                Command::Prove(command) => command,
            };
            assert_eq!(command.accelerator, expected);
        }
    }

    #[test]
    fn cpu_backend_works_without_gpu_features() {
        let backend = TrackedAccelerator::new(Backend::Cpu, OpenclDevice::Gpu, false).unwrap();
        assert!(!backend.wants_msm());
    }

    #[test]
    fn gpu_backends_require_explicit_side_channel_acknowledgment() {
        for backend in [Backend::Cuda, Backend::Opencl] {
            let error = TrackedAccelerator::new(backend, OpenclDevice::Gpu, false)
                .err()
                .unwrap()
                .to_string();
            assert!(error.contains("not verified constant-time"));
            assert!(error.contains("--acknowledge-gpu-side-channel-risk"));
        }
    }

    #[cfg(not(feature = "cuda-msm"))]
    #[test]
    fn cuda_selection_names_the_build_feature() {
        assert!(
            TrackedAccelerator::new(Backend::Cuda, OpenclDevice::Gpu, true)
                .err()
                .unwrap()
                .to_string()
                .contains("cuda-msm")
        );
    }

    #[cfg(not(feature = "opencl-msm"))]
    #[test]
    fn opencl_selection_names_the_build_feature() {
        assert!(
            TrackedAccelerator::new(Backend::Opencl, OpenclDevice::Gpu, true)
                .err()
                .unwrap()
                .to_string()
                .contains("opencl-msm")
        );
    }
}
