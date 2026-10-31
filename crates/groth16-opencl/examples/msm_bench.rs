use std::{env, time::Instant};

use ark_bn254::{Fr, G1Affine, G1Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{PrimeField, UniformRand};
use ark_serialize::{CanonicalSerialize, Compress};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use xark_groth16::{Accelerator, msm::msm};
use xark_groth16_opencl::{OpenClDeviceKind, OpenClMsm};

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let sizes = parse_sizes(
        env::var("XARK_OPENCL_MSM_SIZES").unwrap_or_else(|_| "64,256,1024,8192".into()),
    )?;
    let repeats = env::var("XARK_OPENCL_MSM_REPEATS")
        .unwrap_or_else(|_| "5".into())
        .parse::<usize>()
        .map_err(|error| format!("invalid XARK_OPENCL_MSM_REPEATS: {error}"))?;
    if repeats == 0 {
        return Err("XARK_OPENCL_MSM_REPEATS must be greater than zero".into());
    }
    let seed = env::var("XARK_OPENCL_MSM_SEED")
        .unwrap_or_else(|_| "6361401094495923533".into())
        .parse::<u64>()
        .map_err(|error| format!("invalid XARK_OPENCL_MSM_SEED: {error}"))?;
    let mut accelerator = OpenClMsm::with_device_kind(OpenClDeviceKind::Gpu);
    if !accelerator.initialize() {
        return Err("no available OpenCL GPU/compiler; benchmark requires a GPU device".into());
    }

    println!("record,n,seed,repeat,cpu_pippenger_ms,cpu_decode_ms,cpu_chunk_ms,opencl_total_ms");
    for n in sizes {
        let mut rng = ChaCha20Rng::seed_from_u64(seed ^ n as u64);
        let mut bases = Vec::with_capacity(n);
        let mut scalars = Vec::with_capacity(n);
        for _ in 0..n {
            bases.push((G1Affine::generator() * Fr::rand(&mut rng)).into_affine());
            scalars.push(Fr::rand(&mut rng).into_bigint());
        }
        let mut encoded = Vec::new();
        for point in &bases {
            point
                .serialize_with_mode(&mut encoded, Compress::Yes)
                .map_err(|error| error.to_string())?;
        }

        let expected = msm::<G1Projective>(&bases, &scalars).into_affine();
        let mut expected_bytes = Vec::new();
        expected
            .serialize_uncompressed(&mut expected_bytes)
            .map_err(|error| error.to_string())?;
        let warmup = accelerator
            .msm(false, &encoded, true, &scalars)
            .ok_or_else(|| format!("OpenCL declined valid input with {n} points"))?;
        if warmup != expected_bytes {
            return Err(format!("OpenCL result differs from CPU Pippenger at n={n}"));
        }

        for repeat in 1..=repeats {
            let start = Instant::now();
            let cpu = msm::<G1Projective>(&bases, &scalars).into_affine();
            let cpu_msm_elapsed = start.elapsed();
            if cpu != expected {
                return Err(format!("CPU Pippenger result changed at n={n}"));
            }

            let start = Instant::now();
            let decoded = encoded
                .chunks_exact(G1Affine::generator().serialized_size(Compress::Yes))
                .map(|bytes| xark_groth16::decode::point::<G1Affine>(bytes, Compress::Yes))
                .collect::<Result<Vec<_>, _>>()
                .map_err(|error| error.to_string())?;
            let cpu_decode_elapsed = start.elapsed();
            if decoded != bases {
                return Err(format!("CPU point decoding changed an input at n={n}"));
            }
            let start = Instant::now();
            let decoded_msm = msm::<G1Projective>(&decoded, &scalars).into_affine();
            let cpu_chunk_elapsed = start.elapsed() + cpu_decode_elapsed;
            if decoded_msm != expected {
                return Err(format!("CPU decoded-input MSM changed at n={n}"));
            }

            let start = Instant::now();
            let opencl = accelerator
                .msm(false, &encoded, true, &scalars)
                .ok_or_else(|| format!("OpenCL declined valid input with {n} points"))?;
            let opencl_elapsed = start.elapsed();
            if opencl != expected_bytes {
                return Err(format!("OpenCL result differs from CPU Pippenger at n={n}"));
            }
            println!(
                "sample,{n},{seed},{repeat},{:.3},{:.3},{:.3},{:.3}",
                cpu_msm_elapsed.as_secs_f64() * 1_000.0,
                cpu_decode_elapsed.as_secs_f64() * 1_000.0,
                cpu_chunk_elapsed.as_secs_f64() * 1_000.0,
                opencl_elapsed.as_secs_f64() * 1_000.0,
            );
        }
    }
    Ok(())
}

fn parse_sizes(value: String) -> Result<Vec<usize>, String> {
    value
        .split(',')
        .map(|part| {
            let size = part
                .parse::<usize>()
                .map_err(|error| format!("invalid size {part:?}: {error}"))?;
            if size == 0 {
                return Err("MSM sizes must be greater than zero".into());
            }
            Ok(size)
        })
        .collect()
}
