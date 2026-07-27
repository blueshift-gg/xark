use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{AdditiveGroup, BigInteger, PrimeField, Zero};
use ark_grumpkin::{Affine, Fq, Fr, Projective};
use num_bigint::BigUint;
use std::str::FromStr;

fn dec(x: &Fq) -> String {
    x.into_bigint().to_string()
}

// -(2^n · O) via n integer doublings (matches the gadget's offset accumulator).
fn neg_2n_o(o: Affine, n: usize) -> Affine {
    let mut acc = o.into_group();
    for _ in 0..n {
        acc.double_in_place();
    }
    (-acc).into_affine()
}

// Scalar (Grumpkin Fr, < p < 2^254) → (lo, hi) 127-bit limbs; value = lo + hi·2^127.
fn limbs127(s: &Fr) -> (String, String) {
    let v = BigUint::from_bytes_le(&s.into_bigint().to_bytes_le());
    let mask = (BigUint::from(1u8) << 127u32) - 1u8;
    let lo = &v & &mask;
    let hi = &v >> 127u32;
    (lo.to_string(), hi.to_string())
}

fn main() {
    // --- offset constants ---
    let o = Affine::new_unchecked(
        Fq::from(5u64),
        Fq::from_str("26447525821777463057023244913909144251512587297343525263882").unwrap(),
    );
    assert!(o.is_on_curve(), "O off curve");
    let c128 = neg_2n_o(o, 128);
    assert_eq!(
        dec(&c128.x),
        "15091588220200540439587434062098309947749547413125795808386331904279218024383",
        "corr128 mismatch — reference not trustworthy"
    );
    let c254 = neg_2n_o(o, 254);
    println!("// corr254 = -(2^254 · O)  [VALIDATED: corr128 reproduced exactly]");
    println!("//   x = {}", dec(&c254.x));
    println!("//   y = {}", dec(&c254.y));
    println!();

    // --- n=4 accumulator MSM vector: Q = Σ s_j · G_j ---
    let g = Affine::generator();
    let n = 4usize;
    let mut q = Projective::zero();
    println!("// ==== grumpkin_ipa n=4 deferred-MSM accumulator vector ====");
    for j in 0..n {
        // distinct on-curve generator G_j = (j+2)·GEN
        let gj = (g * Fr::from((j + 2) as u64)).into_affine();
        // full-width (~253-bit) pseudo-random scalar (all bytes j,k-dependent)
        let mut seed = [0u8; 32];
        for k in 0..32usize {
            seed[k] = (0xB7u8)
                .wrapping_add((j as u8).wrapping_mul(53))
                .wrapping_add((k as u8).wrapping_mul(101))
                ^ ((k as u8).wrapping_mul((j as u8).wrapping_add(1)));
        }
        seed[31] &= 0x1f; // keep it comfortably below p (avoid top-bit reduction noise)
        let sj = Fr::from_le_bytes_mod_order(&seed);
        q += gj * sj;
        let (lo, hi) = limbs127(&sj);
        println!("// G{j}: ({}, {})", dec(&gj.x), dec(&gj.y));
        println!("const G{j}X: &str = \"{}\";", dec(&gj.x));
        println!("const G{j}Y: &str = \"{}\";", dec(&gj.y));
        println!("const S{j}LO: &str = \"{lo}\";");
        println!("const S{j}HI: &str = \"{hi}\";");
    }
    let q = q.into_affine();
    println!("const QX: &str = \"{}\";", dec(&q.x));
    println!("const QY: &str = \"{}\";", dec(&q.y));
}
