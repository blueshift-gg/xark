//! Compressed point decoding: ours vs arkworks, one thread.
//! `cargo run --release --example bench_decode`
use ark_bn254::{G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::CurveGroup;
use ark_ff::UniformRand;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use rand::SeedableRng;
use std::time::Instant;

fn main() {
    let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(1);
    let n = 20_000;
    let (mut b1, mut b2) = (Vec::new(), Vec::new());
    for _ in 0..n {
        G1Projective::rand(&mut rng)
            .into_affine()
            .serialize_compressed(&mut b1)
            .unwrap();
        G2Projective::rand(&mut rng)
            .into_affine()
            .serialize_compressed(&mut b2)
            .unwrap();
    }
    let time = |f: &dyn Fn() -> usize| {
        let t = Instant::now();
        let k = f();
        (t.elapsed().as_secs_f64() * 1e9 / n as f64, k)
    };
    let (a1, _) = time(&|| {
        b1.chunks(32)
            .map(|b| {
                std::hint::black_box(
                    G1Affine::deserialize_with_mode(b, Compress::Yes, Validate::No).unwrap(),
                )
            })
            .fold(0usize, |n, _| n + 1)
    });
    let (o1, _) = time(&|| {
        b1.chunks(32)
            .map(|b| std::hint::black_box(xark_groth16::decode::g1(b).unwrap()))
            .fold(0usize, |n, _| n + 1)
    });
    let (a2, _) = time(&|| {
        b2.chunks(64)
            .map(|b| {
                std::hint::black_box(
                    G2Affine::deserialize_with_mode(b, Compress::Yes, Validate::No).unwrap(),
                )
            })
            .fold(0usize, |n, _| n + 1)
    });
    let (o2, _) = time(&|| {
        b2.chunks(64)
            .map(|b| std::hint::black_box(xark_groth16::decode::g2(b).unwrap()))
            .fold(0usize, |n, _| n + 1)
    });
    println!(
        "G1 decompress: arkworks {a1:.0} ns, ours {o1:.0} ns ({:.2}x)",
        a1 / o1
    );
    println!(
        "G2 decompress: arkworks {a2:.0} ns, ours {o2:.0} ns ({:.2}x)",
        a2 / o2
    );
}
