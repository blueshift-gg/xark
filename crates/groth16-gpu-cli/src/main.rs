use anyhow::{Context, Result};
use clap::{Args, Parser, Subcommand, ValueEnum};
use std::time::{Duration, Instant};
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

    /// Confirm use of a trusted, single-tenant GPU. GPU MSM is variable-time and device buffers are not guaranteed to be erased.
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
    stats: G1MsmStats,
}

#[derive(Default)]
struct G1MsmStats {
    used_g1_chunks: usize,
    cpu_fallback_g1_chunks: usize,
    used_g1_points: usize,
    cpu_fallback_g1_points: usize,
    accelerator_call_wall_time: Duration,
    declined_call_wall_time: Duration,
}

impl G1MsmStats {
    fn record(&mut self, point_count: usize, elapsed: Duration, accepted: bool) {
        self.accelerator_call_wall_time += elapsed;
        if accepted {
            self.used_g1_chunks += 1;
            self.used_g1_points += point_count;
        } else {
            self.cpu_fallback_g1_chunks += 1;
            self.cpu_fallback_g1_points += point_count;
            self.declined_call_wall_time += elapsed;
        }
    }
}

impl TrackedAccelerator {
    fn new(
        backend: Backend,
        opencl_device: OpenclDevice,
        acknowledge_gpu_side_channel_risk: bool,
    ) -> Result<Self> {
        if backend != Backend::Cpu && !acknowledge_gpu_side_channel_risk {
            anyhow::bail!(
                "GPU MSM is variable-time and device buffers are not guaranteed to be erased; use CPU for secret inputs on shared or untrusted hardware, or pass --acknowledge-gpu-side-channel-risk for a trusted single-tenant device"
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
            stats: G1MsmStats::default(),
        })
    }

    fn report(&self) {
        if self.backend == Backend::Cpu {
            eprintln!("MSM backend: CPU Pippenger");
        } else {
            let status = if !self.available {
                "unavailable"
            } else if self.stats.used_g1_chunks == 0 && self.stats.cpu_fallback_g1_chunks > 0 {
                "declined all G1 chunks"
            } else if self.stats.cpu_fallback_g1_chunks > 0 {
                "partially used; some chunks fell back"
            } else if self.stats.used_g1_chunks > 0 {
                "used for all G1 chunks"
            } else {
                "selected; no G1 chunks requested"
            };
            eprintln!(
                "MSM backend: {:?}; status={status}; GPU G1 chunks={} points={}; accelerator_call_wall_ms={:.3}; CPU fallback chunks={} points={}; declined_call_wall_ms={:.3}",
                self.backend,
                self.stats.used_g1_chunks,
                self.stats.used_g1_points,
                self.stats.accelerator_call_wall_time.as_secs_f64() * 1_000.0,
                self.stats.cpu_fallback_g1_chunks,
                self.stats.cpu_fallback_g1_points,
                self.stats.declined_call_wall_time.as_secs_f64() * 1_000.0
            );
        }
    }

    fn warn_gpu_security_limits(&self) {
        if self.backend != Backend::Cpu {
            eprintln!(
                "warning: GPU MSM is variable-time; device buffers are not guaranteed to be erased. Use only on trusted, single-tenant hardware"
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
        let start = Instant::now();
        let result = self.inner.msm(g2, points, compressed, scalars);
        let elapsed = start.elapsed();
        if !g2 && self.backend != Backend::Cpu {
            self.stats.record(scalars.len(), elapsed, result.is_some());
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
            accelerator.warn_gpu_security_limits();
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
    use std::time::Duration;

    use super::{Backend, Cli, Command, G1MsmStats, OpenclDevice, TrackedAccelerator};
    use xark_groth16::Accelerator;

    #[test]
    fn records_gpu_success_and_decline_totals_without_input_data() {
        let mut stats = G1MsmStats::default();
        stats.record(12, Duration::from_millis(5), true);
        stats.record(7, Duration::from_millis(3), false);

        assert_eq!(stats.used_g1_chunks, 1);
        assert_eq!(stats.used_g1_points, 12);
        assert_eq!(stats.cpu_fallback_g1_chunks, 1);
        assert_eq!(stats.cpu_fallback_g1_points, 7);
        assert_eq!(stats.accelerator_call_wall_time, Duration::from_millis(8));
        assert_eq!(stats.declined_call_wall_time, Duration::from_millis(3));
    }

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
            assert!(error.contains("variable-time"));
            assert!(error.contains("not guaranteed to be erased"));
            assert!(error.contains("single-tenant"));
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
