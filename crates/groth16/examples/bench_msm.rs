//! One MSM, timed: `bench_msm <log n> <full|bits> [runs]` (threads from
//! `RAYON_NUM_THREADS`), G1 and G2, the median of `runs`.

use std::time::Instant;

use ark_bn254::{Fr, G1Projective, G2Projective};
use ark_ec::{CurveGroup, PrimeGroup};
use ark_ff::{PrimeField, UniformRand};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use xark_groth16::msm::{Scalar, msm};

fn main() {
    if std::env::var("NO_BATCH_AFFINE").is_ok() {
        xark_groth16::msm::BATCH_AFFINE.store(false, std::sync::atomic::Ordering::Relaxed);
    }
    if std::env::var("NO_GLV").is_ok() {
        xark_groth16::msm::GLV.store(false, std::sync::atomic::Ordering::Relaxed);
    }
    let args: Vec<String> = std::env::args().collect();
    let log: u32 = args[1].parse().unwrap();
    let kind = args[2].as_str();
    let runs: usize = args.get(3).map_or(5, |r| r.parse().unwrap());
    let n = std::env::var("N")
        .ok()
        .and_then(|n| n.parse().ok())
        .unwrap_or(1usize << log);
    let mut rng = ChaCha20Rng::seed_from_u64(1);
    let (g1, g2) = (G1Projective::generator(), G2Projective::generator());
    // Distinct points from one walk: P_{i+1} = P_i + P_0·k, cheap to make.
    let step = Fr::rand(&mut rng);
    let mut p1 = Vec::with_capacity(n);
    let mut p2 = Vec::with_capacity(n);
    let (mut a1, mut a2) = (g1 * step, g2 * step);
    let (s1, s2) = (a1, a2);
    for _ in 0..n {
        p1.push(a1);
        p2.push(a2);
        a1 += s1 + g1;
        a2 += s2 + g2;
    }
    let p1 = G1Projective::normalize_batch(&p1);
    let p2 = G2Projective::normalize_batch(&p2);
    let sc: Vec<Scalar> = (0..n)
        .map(|_| match kind {
            "full" => Fr::rand(&mut rng).into_bigint(),
            _ => Fr::from(rng.gen_range(0u64..2)).into_bigint(),
        })
        .collect();
    let time = |f: &dyn Fn()| {
        let mut ts: Vec<f64> = (0..runs)
            .map(|_| {
                let t = Instant::now();
                f();
                t.elapsed().as_secs_f64() * 1e3
            })
            .collect();
        ts.sort_by(f64::total_cmp);
        ts[runs / 2]
    };
    let t1 = time(&|| {
        let _ = std::hint::black_box(msm::<G1Projective>(&p1, &sc));
    });
    println!("xark g1 log={log} {kind} {t1:.2} ms");
    let t2 = time(&|| {
        let _ = std::hint::black_box(msm::<G2Projective>(&p2, &sc));
    });
    println!("xark g2 log={log} {kind} {t2:.2} ms");
}
