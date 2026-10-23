//! Phase 1 MSM validation: our Pippenger and the streaming accumulator against
//! TWO oracles — arkworks' `msm_bigint` and the convention-free naive
//! double-and-add — compared in normalized (canonical affine) form, with
//! randomized sizes, scalar distributions, and chunk seams, plus seeded edge cases.

use ark_bn254::{Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{BigInteger, PrimeField, UniformRand};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use xark_groth16::msm::{Scalar, StreamingMsm, msm, naive_msm, same_point};

fn rng(seed: u64) -> ChaCha20Rng {
    ChaCha20Rng::seed_from_u64(seed)
}

/// Scalars drawn from the distributions a real witness has: zero, ±1, bits,
/// small/negative-small limbs (≤16/32/64/128 bits), and full-width values.
fn witness_like(r: &mut impl Rng, n: usize) -> Vec<Scalar> {
    (0..n)
        .map(|_| {
            let f = match r.gen_range(0..9) {
                0 => Fr::from(0u64),
                1 => Fr::from(1u64),
                2 => -Fr::from(1u64),
                3 => Fr::from(r.gen_range(0..1u64 << 16)),
                4 => -Fr::from(r.gen_range(1..1u64 << 32)),
                5 => Fr::from(r.r#gen::<u64>()),
                6 => -Fr::from(r.r#gen::<u128>()),
                7 => Fr::from(r.r#gen::<u128>()),
                _ => Fr::rand(r),
            };
            f.into_bigint()
        })
        .collect()
}

fn random_points<A: AffineRepr>(r: &mut impl Rng, n: usize) -> Vec<A>
where
    A::Group: UniformRand,
{
    let pts: Vec<A::Group> = (0..n).map(|_| A::Group::rand(r)).collect();
    A::Group::normalize_batch(&pts)
}

fn ark<G: CurveGroup<ScalarField = Fr> + VariableBaseMSM<MulBase = G::Affine>>(
    b: &[G::Affine],
    s: &[Scalar],
) -> G {
    G::msm_bigint(b, s)
}

/// Feed `bases/scalars` through the streaming accumulator at random seams.
fn streamed<G: xark_groth16::msm::SwCurve>(r: &mut impl Rng, b: &[G::Affine], s: &[Scalar]) -> G {
    let mut acc = StreamingMsm::<G>::new();
    let mut i = 0;
    while i < b.len() {
        let step = r.gen_range(1..=b.len() - i);
        acc.feed(&b[i..i + step], &s[i..i + step]);
        i += step;
    }
    assert_eq!(acc.terms(), b.len());
    acc.finish()
}

#[test]
fn matches_both_oracles_small_g1() {
    let mut r = rng(1);
    for trial in 0..40 {
        let n = r.gen_range(0..120);
        let b: Vec<G1Affine> = random_points(&mut r, n);
        let s = witness_like(&mut r, n);
        let ours: G1Projective = msm(&b, &s);
        let naive: G1Projective = naive_msm(&b, &s);
        let arkw: G1Projective = ark(&b, &s);
        assert!(same_point(&ours, &naive), "trial {trial}: vs naive (n={n})");
        assert!(
            same_point(&ours, &arkw),
            "trial {trial}: vs arkworks (n={n})"
        );
        assert!(same_point(
            &streamed::<G1Projective>(&mut r, &b, &s),
            &naive
        ));
    }
}

#[test]
fn matches_both_oracles_small_g2() {
    let mut r = rng(2);
    for _ in 0..12 {
        let n = r.gen_range(1..60);
        let b: Vec<G2Affine> = random_points(&mut r, n);
        let s = witness_like(&mut r, n);
        let ours: G2Projective = msm(&b, &s);
        assert!(same_point(&ours, &naive_msm::<G2Projective>(&b, &s)));
        assert!(same_point(&ours, &ark::<G2Projective>(&b, &s)));
        assert!(same_point(&streamed::<G2Projective>(&mut r, &b, &s), &ours));
    }
}

#[test]
fn matches_arkworks_large_random_seams() {
    // Sizes that exercise multi-window, multi-slice Pippenger in every class.
    let mut r = rng(3);
    for &n in &[1usize << 10, 5_000, 1 << 15, 70_001] {
        let b: Vec<G1Affine> = random_points(&mut r, n);
        let s = witness_like(&mut r, n);
        let arkw: G1Projective = ark(&b, &s);
        assert!(same_point(&msm::<G1Projective>(&b, &s), &arkw), "n={n}");
        assert!(
            same_point(&streamed::<G1Projective>(&mut r, &b, &s), &arkw),
            "n={n} streamed"
        );
        // All-full-width scalars (the `h` vector's distribution).
        let full: Vec<Scalar> = (0..n).map(|_| Fr::rand(&mut r).into_bigint()).collect();
        assert!(same_point(
            &msm::<G1Projective>(&b, &full),
            &ark::<G1Projective>(&b, &full)
        ));
    }
}

#[test]
fn edge_cases_against_naive() {
    let mut r = rng(4);
    let g = G1Affine::generator();
    let p: G1Affine = random_points(&mut r, 1)[0];
    let inf = G1Affine::zero();
    let order: Scalar = Fr::MODULUS; // r ≡ 0
    let r_minus_1 = (-Fr::from(1u64)).into_bigint();
    let mut big_256 = Scalar::from(0u64); // 2^256 − 1 (≥ r): integer semantics
    for l in big_256.0.iter_mut() {
        *l = u64::MAX;
    }
    let cases: Vec<(&str, Vec<G1Affine>, Vec<Scalar>)> = vec![
        ("empty", vec![], vec![]),
        (
            "point at infinity",
            vec![inf, p],
            vec![Fr::rand(&mut r).into_bigint(); 2],
        ),
        (
            "zero scalar",
            vec![p, g],
            vec![Scalar::from(0u64), Scalar::from(7u64)],
        ),
        (
            "scalar == group order",
            vec![p, g],
            vec![order, Scalar::from(3u64)],
        ),
        ("scalar == r-1", vec![p], vec![r_minus_1]),
        (
            "scalar 2^256-1",
            vec![p, g],
            vec![big_256, Scalar::from(1u64)],
        ),
        (
            "repeated base points",
            vec![p; 50],
            (0..50).map(|_| Fr::rand(&mut r).into_bigint()).collect(),
        ),
        (
            "repeated + cancelling",
            vec![p, p],
            vec![Scalar::from(5u64), (-Fr::from(5u64)).into_bigint()],
        ),
        (
            "length mismatch uses min",
            vec![p, g, p],
            vec![Scalar::from(2u64)],
        ),
    ];
    for (name, b, s) in cases {
        let naive: G1Projective = naive_msm(&b, &s);
        let ours: G1Projective = msm(&b, &s);
        assert!(same_point(&ours, &naive), "{name}: ours vs naive");
        let mut st = StreamingMsm::<G1Projective>::new();
        st.feed(&b, &s);
        assert!(
            same_point(&st.finish(), &naive),
            "{name}: streamed vs naive"
        );
        // arkworks reduces scalars mod r; compare only where the integer is < r.
        if s.iter().all(|x| *x < Fr::MODULUS) {
            assert!(
                same_point(&ours, &ark::<G1Projective>(&b, &s)),
                "{name}: vs arkworks"
            );
        }
    }
    // Sanity: the naive oracle itself is convention-free (bit i ↔ 2^i).
    let s = Scalar::from(0b1011u64);
    assert!(s.get_bit(0) && s.get_bit(1) && !s.get_bit(2) && s.get_bit(3));
    let n: G1Projective = naive_msm(&[g], &[s]);
    assert!(same_point(&n, &(g * Fr::from(11u64))));
}

#[test]
fn batch_affine_handles_doubling_cancellation_and_conflicts() {
    use std::sync::atomic::Ordering;
    let mut r = rng(7);
    // Few distinct bases, so batches constantly hit the same bucket with equal
    // points (doubling) and opposite points (cancellation), and defer conflicts.
    let pool: Vec<G1Affine> = random_points(&mut r, 3);
    for &n in &[1usize << 12, 1 << 15] {
        let b: Vec<G1Affine> = (0..n).map(|i| pool[i % 3]).collect();
        let s: Vec<Scalar> = (0..n)
            .map(|i| {
                match i % 4 {
                    0 => Fr::from(5u64),
                    1 => -Fr::from(5u64),
                    2 => Fr::rand(&mut r),
                    _ => Fr::from((i as u64) % 300),
                }
                .into_bigint()
            })
            .collect();
        let want: G1Projective = ark(&b, &s);
        for on in [true, false] {
            xark_groth16::msm::BATCH_AFFINE.store(on, Ordering::Relaxed);
            assert!(
                same_point(&msm::<G1Projective>(&b, &s), &want),
                "n={n} batch_affine={on}"
            );
        }
        let b2: Vec<G2Affine> = {
            let p: Vec<G2Affine> = random_points(&mut r, 2);
            (0..n).map(|i| p[i % 2]).collect()
        };
        xark_groth16::msm::BATCH_AFFINE.store(true, Ordering::Relaxed);
        assert!(
            same_point(&msm::<G2Projective>(&b2, &s), &ark::<G2Projective>(&b2, &s)),
            "G2 n={n}"
        );
    }
}
