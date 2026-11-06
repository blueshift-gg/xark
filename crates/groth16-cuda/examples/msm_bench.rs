use std::time::{Duration, Instant};

use ark_bn254::{Fr, G1Affine, G1Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{PrimeField, UniformRand};
use ark_serialize::{CanonicalSerialize, Compress};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use rayon::prelude::*;
use xark_groth16::{Accelerator, msm::msm};
use xark_groth16_cuda::{CustomCudaMsm, IcicleMsm};

struct Options {
    sizes: Vec<usize>,
    repeats: usize,
    seed: u64,
    encodings: Vec<Compress>,
    backend: String,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let options = parse_options()?;
    let mut accelerator: Box<dyn Accelerator> = match options.backend.as_str() {
        "icicle" => Box::new(IcicleMsm),
        "custom" => {
            if !cfg!(feature = "custom-cuda") {
                return Err("custom backend requires --features custom-cuda".into());
            }
            Box::new(CustomCudaMsm)
        }
        _ => return Err("backend must be icicle or custom".into()),
    };
    if !accelerator.wants_msm() {
        return Err(format!(
            "{} CUDA backend and device are unavailable",
            options.backend
        ));
    }

    println!(
        "record,backend,n,encoding,seed,repeat,stat,cpu_msm_ms,cpu_decode_ms,cpu_chunk_ms,backend_ms"
    );
    for n in options.sizes {
        let (bases, scalars) = inputs(n, options.seed);
        let cpu_result = msm::<G1Projective>(&bases, &scalars).into_affine();
        let mut expected = Vec::new();
        cpu_result
            .serialize_uncompressed(&mut expected)
            .map_err(|error| error.to_string())?;

        for encoding in &options.encodings {
            let mut encoded_points = Vec::new();
            for point in &bases {
                point
                    .serialize_with_mode(&mut encoded_points, *encoding)
                    .map_err(|error| error.to_string())?;
            }
            let compressed = matches!(encoding, Compress::Yes);
            let point_size = G1Affine::generator().serialized_size(*encoding);
            let decoded_points = decode_cpu(&encoded_points, point_size, *encoding)?;
            if decoded_points != bases {
                return Err("CPU decoder changed a generated G1 point".into());
            }
            if msm::<G1Projective>(&decoded_points, &scalars).into_affine() != cpu_result {
                return Err("decoded CPU input differs from the generated-point MSM".into());
            }

            // Warm both paths before collecting the timed samples.
            let cpu_warmup = msm::<G1Projective>(&bases, &scalars).into_affine();
            if cpu_warmup != cpu_result {
                return Err("CPU Pippenger produced a non-deterministic result".into());
            }
            let cpu_chunk_warmup = decode_cpu(&encoded_points, point_size, *encoding)?;
            if msm::<G1Projective>(&cpu_chunk_warmup, &scalars).into_affine() != cpu_result {
                return Err("CPU decoded-input MSM produced a different result".into());
            }
            let gpu_warmup = accelerator
                .msm(false, &encoded_points, compressed, &scalars)
                .ok_or_else(|| format!("{} declined a valid G1 MSM", options.backend))?;
            if gpu_warmup != expected {
                return Err(format!(
                    "{} result differs from Xark CPU Pippenger",
                    options.backend
                ));
            }

            let mut cpu_msm_times = Vec::with_capacity(options.repeats);
            let mut cpu_decode_times = Vec::with_capacity(options.repeats);
            let mut cpu_chunk_times = Vec::with_capacity(options.repeats);
            let mut gpu_times = Vec::with_capacity(options.repeats);
            for repeat in 0..options.repeats {
                // Rotate the path order so each path gets a turn at each position.
                let mut sample = [Duration::ZERO; 4];
                for offset in 0..4 {
                    match (repeat + offset) % 4 {
                        0 => {
                            let start = Instant::now();
                            let result = msm::<G1Projective>(&bases, &scalars).into_affine();
                            sample[0] = start.elapsed();
                            if result != cpu_result {
                                return Err("timed CPU Pippenger result changed".into());
                            }
                        }
                        1 => {
                            let start = Instant::now();
                            let decoded = decode_cpu(&encoded_points, point_size, *encoding)?;
                            sample[1] = start.elapsed();
                            if decoded != bases {
                                return Err("timed CPU decoder changed a generated G1 point".into());
                            }
                            std::hint::black_box(decoded);
                        }
                        2 => {
                            let start = Instant::now();
                            let decoded = decode_cpu(&encoded_points, point_size, *encoding)?;
                            let result = msm::<G1Projective>(&decoded, &scalars).into_affine();
                            sample[2] = start.elapsed();
                            if result != cpu_result {
                                return Err("timed CPU decoded-input MSM result changed".into());
                            }
                        }
                        _ => {
                            let start = Instant::now();
                            let result = accelerator
                                .msm(false, &encoded_points, compressed, &scalars)
                                .ok_or_else(|| {
                                    format!("{} declined a valid G1 MSM", options.backend)
                                })?;
                            sample[3] = start.elapsed();
                            if result != expected {
                                return Err(format!(
                                    "timed {} result differs from Xark CPU Pippenger",
                                    options.backend
                                ));
                            }
                        }
                    }
                }
                cpu_msm_times.push(sample[0]);
                cpu_decode_times.push(sample[1]);
                cpu_chunk_times.push(sample[2]);
                gpu_times.push(sample[3]);
                println!(
                    "sample,{},{n},{},{},{},,{:.3},{:.3},{:.3},{:.3}",
                    options.backend,
                    encoding_name(*encoding),
                    options.seed,
                    repeat + 1,
                    millis(sample[0]),
                    millis(sample[1]),
                    millis(sample[2]),
                    millis(sample[3]),
                );
            }

            let cpu_msm_summary = range_summary(&mut cpu_msm_times);
            let cpu_decode_summary = range_summary(&mut cpu_decode_times);
            let cpu_chunk_summary = range_summary(&mut cpu_chunk_times);
            let gpu_summary = range_summary(&mut gpu_times);
            for (stat, column) in [("median", 0), ("min", 1), ("max", 2)] {
                println!(
                    "summary,{},{n},{},{},,{stat},{:.3},{:.3},{:.3},{:.3}",
                    options.backend,
                    encoding_name(*encoding),
                    options.seed,
                    summary_ms(cpu_msm_summary)[column],
                    summary_ms(cpu_decode_summary)[column],
                    summary_ms(cpu_chunk_summary)[column],
                    summary_ms(gpu_summary)[column],
                );
            }
        }
    }
    Ok(())
}

fn decode_cpu(
    bytes: &[u8],
    point_size: usize,
    encoding: Compress,
) -> Result<Vec<G1Affine>, String> {
    bytes
        .par_chunks_exact(point_size)
        .map(|chunk| xark_groth16::decode::point::<G1Affine>(chunk, encoding))
        .collect::<Result<_, _>>()
        .map_err(|error| error.to_string())
}

fn inputs(n: usize, seed: u64) -> (Vec<G1Affine>, Vec<<Fr as PrimeField>::BigInt>) {
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let mut bases = Vec::with_capacity(n);
    let mut scalars = Vec::with_capacity(n);
    for _ in 0..n {
        bases.push((G1Affine::generator() * Fr::rand(&mut rng)).into_affine());
        scalars.push(Fr::rand(&mut rng).into_bigint());
    }
    (bases, scalars)
}

fn parse_options() -> Result<Options, String> {
    parse_options_from(std::env::args().skip(1))
}

fn parse_options_from(args: impl Iterator<Item = String>) -> Result<Options, String> {
    let mut sizes = vec![1 << 10, 1 << 16, 1 << 19];
    let mut repeats = 7usize;
    let mut seed = 0x5841_524b_4d53_4d;
    let mut encodings = vec![Compress::Yes];
    let mut backend = "icicle".to_owned();
    let mut args = args;
    while let Some(arg) = args.next() {
        let value = args
            .next()
            .ok_or_else(|| format!("missing value after {arg}"))?;
        match arg.as_str() {
            "--sizes" => {
                sizes = value
                    .split(',')
                    .map(|item| {
                        let n = item
                            .parse::<usize>()
                            .map_err(|_| format!("invalid MSM size: {item}"))?;
                        if n == 0 {
                            return Err("MSM sizes must be positive".into());
                        }
                        Ok(n)
                    })
                    .collect::<Result<_, String>>()?;
                if sizes.is_empty() {
                    return Err("at least one MSM size is required".into());
                }
            }
            "--repeats" => {
                repeats = value
                    .parse()
                    .map_err(|_| format!("invalid repeat count: {value}"))?;
                if repeats == 0 {
                    return Err("repeat count must be positive".into());
                }
            }
            "--seed" => {
                seed = value
                    .parse()
                    .map_err(|_| format!("invalid seed: {value}"))?;
            }
            "--encoding" => {
                encodings = match value.as_str() {
                    "compressed" => vec![Compress::Yes],
                    "uncompressed" => vec![Compress::No],
                    "both" => vec![Compress::Yes, Compress::No],
                    _ => return Err("encoding must be compressed, uncompressed, or both".into()),
                };
            }
            "--backend" => {
                backend = value;
                if backend != "icicle" && backend != "custom" {
                    return Err("backend must be icicle or custom".into());
                }
            }
            _ => return Err(format!("unknown option: {arg}")),
        }
    }
    Ok(Options {
        sizes,
        repeats,
        seed,
        encodings,
        backend,
    })
}

fn range_summary(samples: &mut [Duration]) -> (f64, f64, f64) {
    samples.sort_unstable();
    let median = if samples.len() % 2 == 0 {
        (samples[samples.len() / 2 - 1].as_secs_f64() + samples[samples.len() / 2].as_secs_f64())
            / 2.0
    } else {
        samples[samples.len() / 2].as_secs_f64()
    };
    (
        median * 1_000.0,
        millis(samples[0]),
        millis(*samples.last().unwrap()),
    )
}

fn summary_ms(summary: (f64, f64, f64)) -> [f64; 3] {
    [summary.0, summary.1, summary.2]
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1_000.0
}

fn encoding_name(encoding: Compress) -> &'static str {
    if matches!(encoding, Compress::Yes) {
        "compressed"
    } else {
        "uncompressed"
    }
}

#[cfg(test)]
mod tests {
    use super::{parse_options_from, range_summary};
    use std::time::Duration;

    #[test]
    fn range_summary_uses_conventional_even_sample_median() {
        let mut samples = [
            Duration::from_millis(9),
            Duration::from_millis(1),
            Duration::from_millis(5),
            Duration::from_millis(3),
        ];

        assert_eq!(range_summary(&mut samples), (4.0, 1.0, 9.0));
    }

    #[test]
    fn benchmark_parser_selects_custom_backend() {
        let options = parse_options_from(
            ["--backend", "custom", "--sizes", "16"]
                .into_iter()
                .map(str::to_owned),
        )
        .expect("custom backend options parse");
        assert_eq!(options.backend, "custom");
        assert_eq!(options.sizes, [16]);
    }
}
