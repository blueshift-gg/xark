//! Coset transform time: radix-2 `2^22` vs the smooth domains a 2.36M-row circuit
//! (Ed25519) fits in. `cargo run --release --example bench_smooth`
use ark_bn254::Fr;
use ark_ff::{FftField, UniformRand};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use std::time::Instant;
use xark_groth16::fft::{Domain, FftConfig};

fn main() {
    let mut rng = ChaCha20Rng::seed_from_u64(1);
    for n in [1usize << 22, 3 << 20, 9 << 18, 1 << 20, 3 << 18, 9 << 16] {
        let d = Domain::with_size(n, FftConfig::default()).unwrap();
        let x: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
        let mut best = f64::MAX;
        for _ in 0..4 {
            let mut v = x.clone();
            let t = Instant::now();
            d.to_coset(&mut v, Fr::GENERATOR);
            best = best.min(t.elapsed().as_secs_f64() * 1e3);
        }
        println!(
            "n={n:>8} ({}x{}) to_coset {best:7.1} ms  {:.1} ns/elem",
            d.n1,
            d.n2,
            best * 1e6 / n as f64
        );
    }
}
