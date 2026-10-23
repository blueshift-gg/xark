//! Phase 2/3 validation: the blocked four-step FFT (every tile size, square and
//! rectangular splits) is bit-identical to ark-poly's radix-2 domain.

use ark_bn254::Fr;
use ark_ff::{FftField, Field, UniformRand};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use xark_groth16::fft::{Domain, FftConfig, transpose_map};

fn rand_vec(n: usize, seed: u64) -> Vec<Fr> {
    let mut r = ChaCha20Rng::seed_from_u64(seed);
    (0..n).map(|_| Fr::rand(&mut r)).collect()
}

fn blocked(tile: usize) -> FftConfig {
    FftConfig {
        tile,
        min_blocked_log: 1,
    }
}

#[test]
fn natural_fft_and_ifft_match_ark_poly() {
    for log in 0..=14u32 {
        let n = 1usize << log;
        let ark = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
        let x = rand_vec(n, log as u64);
        let want_f = ark.fft(&x);
        let want_i = ark.ifft(&x);
        for tile in [1usize, 3, 8, 16, 64] {
            let d = Domain::new(n, blocked(tile)).unwrap();
            let mut v = x.clone();
            d.fft(&mut v);
            assert_eq!(v, want_f, "fft log={log} tile={tile} ({}x{})", d.n1, d.n2);
            let mut v = x.clone();
            d.ifft(&mut v);
            assert_eq!(v, want_i, "ifft log={log} tile={tile}");
        }
        // Plain (unblocked) path too.
        let d = Domain::new(n, FftConfig::default()).unwrap();
        let mut v = x.clone();
        d.fft(&mut v);
        assert_eq!(v, want_f, "plain fft log={log}");
    }
}

#[test]
fn t_layout_round_trips_and_feeds_from_t() {
    // fft_to_t → (T-layout) → ifft_from_t is the identity, and
    // ifft_to_t → fft_from_t is the identity, for odd and even logs.
    for log in [5u32, 6, 9, 12, 13] {
        let n = 1usize << log;
        let d = Domain::new(n, blocked(8)).unwrap();
        let x = rand_vec(n, 100 + log as u64);
        let mut v = x.clone();
        d.fft_to_t(&mut v);
        d.ifft_from_t(&mut v);
        assert_eq!(v, x, "fft_to_t/ifft_from_t log={log}");
        let mut v = x.clone();
        d.ifft_to_t(&mut v);
        d.fft_from_t(&mut v);
        assert_eq!(v, x, "ifft_to_t/fft_from_t log={log}");
    }
}

#[test]
fn coset_pipeline_matches_ark_poly() {
    // evals → coefficients → coset evals, as the QAP step does it.
    for log in [4u32, 11, 12, 15] {
        let n = 1usize << log;
        let ark = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
        let coset = ark.get_coset(Fr::GENERATOR).unwrap();
        let x = rand_vec(n, 200 + log as u64);
        let mut want = ark.ifft(&x);
        coset.fft_in_place(&mut want);

        let d = Domain::new(n, blocked(16)).unwrap();
        let mut v = x.clone();
        d.ifft_to_t(&mut v);
        d.coset_scale_t(&mut v, Fr::GENERATOR);
        d.fft_from_t(&mut v);
        assert_eq!(v, want, "log={log}");
    }
}

#[test]
fn tiled_transpose_any_shape_any_tile() {
    for (rows, cols) in [
        (1, 7),
        (7, 1),
        (4, 4),
        (8, 16),
        (16, 8),
        (13, 29),
        (64, 128),
    ] {
        let src: Vec<u32> = (0..rows * cols).map(|i| i as u32).collect();
        for tile in [1usize, 2, 3, 8, 32, 1000] {
            let mut dst = vec![0u32; rows * cols];
            transpose_map(&src, &mut dst, rows, cols, tile, |x| *x);
            for r in 0..rows {
                for c in 0..cols {
                    assert_eq!(
                        dst[c * rows + r],
                        src[r * cols + c],
                        "{rows}x{cols} tile={tile}"
                    );
                }
            }
        }
    }
}

#[test]
fn smooth_domains_match_ark_mixed_radix() {
    use ark_poly::MixedRadixEvaluationDomain;
    use xark_groth16::fft::smooth_size;
    assert_eq!(smooth_size(2_358_839), 9 << 18);
    assert_eq!(smooth_size(3 << 10), 3 << 10);
    assert_eq!(smooth_size(1025), 1152);
    assert_eq!(smooth_size(1 << 20), 1 << 20);
    for (q, k) in [
        (3usize, 0u32),
        (9, 0),
        (3, 1),
        (9, 3),
        (3, 6),
        (9, 7),
        (3, 12),
        (9, 11),
        (3, 13),
    ] {
        let n = q << k;
        let ark = MixedRadixEvaluationDomain::<Fr>::new(n).unwrap();
        assert_eq!(ark.size(), n);
        let coset = ark.get_coset(Fr::GENERATOR).unwrap();
        let x = rand_vec(n, 300 + n as u64);
        let want_f = ark.fft(&x);
        let want_i = ark.ifft(&x);
        let mut want_c = ark.ifft(&x);
        coset.fft_in_place(&mut want_c);
        let mut want_h = want_c.clone();
        coset.ifft_in_place(&mut want_h);
        for cfg in [FftConfig::default(), blocked(1), blocked(4), blocked(16)] {
            let d = Domain::with_size(n, cfg).unwrap();
            let tag = format!("n={q}·2^{k} {}x{} tile={}", d.n1, d.n2, d.tile);
            let mut v = x.clone();
            d.fft(&mut v);
            assert_eq!(v, want_f, "fft {tag}");
            let mut v = x.clone();
            d.ifft(&mut v);
            assert_eq!(v, want_i, "ifft {tag}");
            let mut v = x.clone();
            d.to_coset(&mut v, Fr::GENERATOR);
            assert_eq!(v, want_c, "to_coset {tag}");
            d.from_coset_to_t(&mut v, Fr::GENERATOR.inverse().unwrap());
            assert_eq!(d.t_to_natural(&v, |x| *x), want_h, "from_coset {tag}");
            let mut v = x.clone();
            d.fft_to_t(&mut v);
            d.ifft_from_t(&mut v);
            assert_eq!(v, x, "t round trip {tag}");
            // Workers rebuild the domain from its split.
            let w = Domain::with_split(d.n1, d.n2, d.tile).unwrap();
            assert_eq!((w.n, w.n1, w.n2), (d.n, d.n1, d.n2));
        }
    }
    assert!(Domain::with_size(5 << 4, FftConfig::default()).is_none());
    assert!(Domain::with_size(27 << 4, FftConfig::default()).is_none());
}
