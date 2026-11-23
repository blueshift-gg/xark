//! Field multiplication and one-thread FFT timings, against which gnark-crypto's
//! are compared: `bench_field`.

use std::time::Instant;

use ark_bn254::{Fq, Fr};
use ark_ff::{FftField, UniformRand};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use xark_groth16::{Domain, FftConfig};

fn main() {
    let mut rng = ChaCha20Rng::seed_from_u64(1);
    const N: usize = 50_000_000;
    let (mut a, b) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
    let t = Instant::now();
    for _ in 0..N {
        a *= b;
    }
    println!(
        "ark fr mul latency {:.2} ns {}",
        t.elapsed().as_nanos() as f64 / N as f64,
        std::hint::black_box(a) == b
    );
    let (mut x, y) = (Fq::rand(&mut rng), Fq::rand(&mut rng));
    let t = Instant::now();
    for _ in 0..N {
        x *= y;
    }
    println!(
        "ark fq mul latency {:.2} ns {}",
        t.elapsed().as_nanos() as f64 / N as f64,
        std::hint::black_box(x) == y
    );
    let v: Vec<Fr> = (0..1 << 17).map(|_| Fr::rand(&mut rng)).collect();
    let t = Instant::now();
    let w: Vec<Fr> = v.iter().map(|x| *x * b).collect();
    println!(
        "ark fr mul throughput {:.2} ns {}",
        t.elapsed().as_nanos() as f64 / v.len() as f64,
        std::hint::black_box(w)[0] == b
    );
    {
        let v: Vec<Fq> = (0..4096).map(|_| Fq::rand(&mut rng)).collect();
        let w: Vec<Fq> = (0..4096).map(|_| Fq::rand(&mut rng)).collect();
        let mut out = vec![Fq::from(0u64); 4096];
        let t = Instant::now();
        for _ in 0..2000 {
            for i in 0..4096 {
                out[i] = v[i] - w[i];
            }
            std::hint::black_box(&mut out);
        }
        println!(
            "ark fq sub throughput {:.2} ns",
            t.elapsed().as_nanos() as f64 / (2000.0 * 4096.0)
        );
        let t = Instant::now();
        for _ in 0..2000 {
            for i in 0..4096 {
                out[i] = v[i] * w[i];
            }
            std::hint::black_box(&mut out);
        }
        println!(
            "ark fq mul throughput {:.2} ns",
            t.elapsed().as_nanos() as f64 / (2000.0 * 4096.0)
        );
        let t = Instant::now();
        for _ in 0..2000 {
            for i in 0..4096 {
                out[i] = ark_ff::Field::square(&v[i]);
            }
            std::hint::black_box(&mut out);
        }
        println!(
            "ark fq square throughput {:.2} ns",
            t.elapsed().as_nanos() as f64 / (2000.0 * 4096.0)
        );
    }
    {
        use ark_bn254::Fq2;
        let v: Vec<Fq2> = (0..4096).map(|_| Fq2::rand(&mut rng)).collect();
        let w: Vec<Fq2> = (0..4096).map(|_| Fq2::rand(&mut rng)).collect();
        let mut out = vec![Fq2::from(0u64); 4096];
        for (name, f) in [
            ("mul", (|a: &Fq2, b: &Fq2| *a * b) as fn(&Fq2, &Fq2) -> Fq2),
            ("square", |a: &Fq2, _: &Fq2| ark_ff::Field::square(a)),
            ("sub", |a: &Fq2, b: &Fq2| *a - b),
        ] {
            let t = Instant::now();
            for _ in 0..1000 {
                for i in 0..4096 {
                    out[i] = f(&v[i], &w[i]);
                }
                std::hint::black_box(&mut out);
            }
            println!(
                "ark fq2 {name} throughput {:.2} ns",
                t.elapsed().as_nanos() as f64 / (1000.0 * 4096.0)
            );
        }
    }
    for log in [8u32, 9, 10] {
        let l = 1usize << log;
        let w = Fr::get_root_of_unity(l as u64).unwrap();
        let mut tw = vec![Fr::from(1u64); l / 2];
        for j in 1..l / 2 {
            tw[j] = tw[j - 1] * w;
        }
        let mut v: Vec<Fr> = (0..l).map(|_| Fr::rand(&mut rng)).collect();
        let reps = (1 << 20) / l;
        let t = Instant::now();
        for _ in 0..reps {
            xark_groth16::fft::radix2_fft(&mut v, &tw);
        }
        let ns = t.elapsed().as_nanos() as f64 / reps as f64;
        println!(
            "radix2 2^{log}: {:.1} us, {:.2} ns per butterfly",
            ns / 1e3,
            ns / (l as f64 / 2.0 * log as f64)
        );
    }
    {
        use ark_bn254::{Bn254, G1Projective, G2Projective};
        use ark_ec::pairing::Pairing;
        use ark_ec::{CurveGroup, PrimeGroup};
        let p = (G1Projective::generator() * Fr::rand(&mut rng)).into_affine();
        let q = (G2Projective::generator() * Fr::rand(&mut rng)).into_affine();
        let t = Instant::now();
        for _ in 0..100 {
            std::hint::black_box(<Bn254 as Pairing>::G2Prepared::from(q));
        }
        println!("g2 prepare {:.1} us", t.elapsed().as_secs_f64() * 1e4);
        let pq = <Bn254 as Pairing>::G2Prepared::from(q);
        let t = Instant::now();
        let mut ml = None;
        for _ in 0..100 {
            ml = Some(Bn254::multi_miller_loop([p], [pq.clone()]));
        }
        println!(
            "miller loop (prepared) {:.1} us",
            t.elapsed().as_secs_f64() * 1e4
        );
        let ml = ml.unwrap();
        let t = Instant::now();
        for _ in 0..100 {
            std::hint::black_box(Bn254::final_exponentiation(ml));
        }
        println!(
            "final exponentiation {:.1} us",
            t.elapsed().as_secs_f64() * 1e4
        );
    }
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .unwrap();
    pool.install(|| {
        for log in [17u32, 20] {
            let dom = Domain::with_size(1 << log, FftConfig::default()).unwrap();
            let mut v: Vec<Fr> = (0..1 << log).map(|_| Fr::rand(&mut rng)).collect();
            let best = (0..5)
                .map(|_| {
                    let t = Instant::now();
                    dom.fft_to_t(&mut v);
                    t.elapsed().as_secs_f64() * 1e3
                })
                .fold(f64::MAX, f64::min);
            println!("xark fft 2^{log} 1 thread {best:.2} ms");
        }
    });
}
