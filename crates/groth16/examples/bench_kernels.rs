//! Kernel benchmarks: the coset transform (blocked four-step at each tile size vs
//! plain radix-2 vs ark-poly), the tiled transpose, and our MSM vs arkworks', each
//! single-threaded and on all cores.
//!
//! `cargo run --release -p xark-groth16 --example bench_kernels [fft|msm]`

use std::time::Instant;

use ark_bn254::{Fr, G1Affine, G1Projective};
use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ff::{FftField, PrimeField, UniformRand, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use xark_groth16::fft::{Domain, FftConfig, transpose_map};
use xark_groth16::msm::{Scalar, msm, same_point};

fn time<F: FnMut()>(reps: usize, mut f: F) -> f64 {
    f();
    let t = Instant::now();
    for _ in 0..reps {
        f();
    }
    t.elapsed().as_secs_f64() * 1e3 / reps as f64
}

fn fft(threads: usize) {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
        .build()
        .unwrap();
    pool.install(|| {
        for log in [16u32, 18, 20, 22] {
            let n = 1usize << log;
            let mut rng = ChaCha20Rng::seed_from_u64(log as u64);
            let x: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
            let reps = if log >= 22 { 2 } else { 4 };
            let g = Fr::GENERATOR;
            let ark = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
            let coset = ark.get_coset(g).unwrap();
            let mut v = x.clone();
            let t_ark = time(reps, || {
                ark.ifft_in_place(&mut v);
                coset.fft_in_place(&mut v);
            });
            let plain = Domain::new(
                n,
                FftConfig {
                    tile: 1,
                    min_blocked_log: 64,
                },
            )
            .unwrap();
            let t_plain = time(reps, || plain.to_coset(&mut v, g));
            let mut row = format!(
                "{{\"threads\":{threads},\"log\":{log},\"ark\":{t_ark:.1},\"plain\":{t_plain:.1}"
            );
            for tile in [1usize, 2, 4, 8, 16, 32, 64] {
                let d = Domain::new(
                    n,
                    FftConfig {
                        tile,
                        min_blocked_log: 0,
                    },
                )
                .unwrap();
                let t = time(reps, || d.to_coset(&mut v, g));
                row += &format!(",\"tile{tile}\":{t:.1}");
            }
            let (n1, n2) = (1usize << (log / 2), 1usize << (log - log / 2));
            let mut out = vec![Fr::zero(); n];
            for tile in [1usize, 4, 8, 16, 32, 64] {
                let t = time(reps, || transpose_map(&x, &mut out, n1, n2, tile, |a| *a));
                row += &format!(",\"tr{tile}\":{t:.1}");
            }
            println!("{row}}}");
        }
    });
}

fn msm_bench(threads: usize) {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
        .build()
        .unwrap();
    pool.install(|| {
        let mut rng = ChaCha20Rng::seed_from_u64(1);
        for log in [16u32, 20] {
            let n = 1usize << log;
            let pts: Vec<G1Projective> = (0..1024).map(|_| G1Projective::rand(&mut rng)).collect();
            let pts = G1Projective::normalize_batch(&pts);
            let bases: Vec<G1Affine> = (0..n).map(|i| pts[i % 1024]).collect();
            // Witness-like (bits / small / negative-small / full) and all-full (h).
            let witness: Vec<Scalar> = (0..n)
                .map(|_| {
                    match rng.gen_range(0..6) {
                        0 => Fr::zero(),
                        1 => Fr::from(rng.gen_range(0..2u64)),
                        2 => Fr::from(rng.gen_range(0..1u64 << 16)),
                        3 => -Fr::from(rng.gen_range(1..1u64 << 32)),
                        4 => Fr::from(rng.r#gen::<u64>()),
                        _ => Fr::rand(&mut rng),
                    }
                    .into_bigint()
                })
                .collect();
            let full: Vec<Scalar> = (0..n).map(|_| Fr::rand(&mut rng).into_bigint()).collect();
            for (name, sc) in [("witness", &witness), ("full", &full)] {
                let reps = 3;
                let mut a = G1Projective::zero();
                let mut b = G1Projective::zero();
                let ba = &xark_groth16::msm::BATCH_AFFINE;
                let t_ark = time(reps, || a = G1Projective::msm_bigint(&bases, sc));
                ba.store(false, std::sync::atomic::Ordering::Relaxed);
                let t_xyzz = time(reps, || b = msm::<G1Projective>(&bases, sc));
                assert!(same_point(&a, &b));
                ba.store(true, std::sync::atomic::Ordering::Relaxed);
                let t_ba = time(reps, || b = msm::<G1Projective>(&bases, sc));
                assert!(same_point(&a, &b));
                println!(
                    "{{\"threads\":{threads},\"msm\":\"{name}\",\"log\":{log},\"ark\":{t_ark:.1},\"xyzz\":{t_xyzz:.1},\"batch_affine\":{t_ba:.1}}}"
                );
            }
        }
    });
}

fn main() {
    let what = std::env::args().nth(1).unwrap_or_else(|| "all".into());
    let all = std::thread::available_parallelism().map_or(1, |n| n.get());
    for threads in [1, all] {
        if what == "all" || what == "fft" {
            fft(threads);
        }
        if what == "all" || what == "msm" {
            msm_bench(threads);
        }
    }
}
