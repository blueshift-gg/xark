//! Real Halo/Bulletproofs IPA transcript over Grumpkin, n=4 / k=2 rounds, with
//! Poseidon2 Fiat-Shamir challenges (host `poseidon2` crate == the in-circuit
//! `xark-poseidon2` gadget). SELF-VALIDATING: asserts the final IPA relation
//! `P_final == a*·G* + (a*·b*)·U` and `G* == Σ sⱼ·Gⱼ`, then emits the values the
//! Milestone-2 circuit will verify. Challenges are the low 128 bits of the
//! Poseidon2 output (Halo-style short challenge), reused verbatim in-circuit.

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, Field as _, PrimeField, Zero};
use ark_grumpkin::{Affine, Fq as Base, Fr as Scalar, Projective};
use num_bigint::BigUint;

fn base_dec(x: &Base) -> String {
    x.into_bigint().to_string()
}
fn scalar_dec(x: &Scalar) -> String {
    x.into_bigint().to_string()
}
// Grumpkin scalar (< p < 2^254) → (lo, hi) 127-bit limbs.
fn limbs127(s: &Scalar) -> (String, String) {
    let v = BigUint::from_bytes_le(&s.into_bigint().to_bytes_le());
    let mask = (BigUint::from(1u8) << 127u32) - 1u8;
    ((&v & &mask).to_string(), (&v >> 127u32).to_string())
}
// A Grumpkin scalar's canonical integer < 2^128, as a base-field element (for hashing).
fn scalar_to_base(s: &Scalar) -> Base {
    Base::from(BigUint::from_bytes_le(&s.into_bigint().to_bytes_le()))
}

// Poseidon2(inputs) → challenge = low 128 bits, as a Grumpkin scalar.
fn challenge(inputs: &[Base]) -> Scalar {
    // host poseidon2::hash needs a fixed-size array; we only ever pass 5 or 6.
    let h: Base = match inputs.len() {
        6 => poseidon2::hash([inputs[0], inputs[1], inputs[2], inputs[3], inputs[4], inputs[5]]),
        5 => poseidon2::hash([inputs[0], inputs[1], inputs[2], inputs[3], inputs[4]]),
        _ => unreachable!(),
    };
    let hbig = BigUint::from_bytes_le(&h.into_bigint().to_bytes_le());
    let mask = (BigUint::from(1u8) << 128u32) - 1u8;
    Scalar::from(&hbig & &mask)
}

fn msm(scalars: &[Scalar], points: &[Affine]) -> Projective {
    scalars
        .iter()
        .zip(points)
        .fold(Projective::zero(), |acc, (s, p)| acc + *p * s)
}
fn inner(a: &[Scalar], b: &[Scalar]) -> Scalar {
    a.iter().zip(b).map(|(x, y)| *x * y).sum()
}

fn main() {
    let g = Affine::generator();
    // Public generators G_0..G_3 and U (distinct multiples of the base point).
    let gens: Vec<Affine> = (0..4).map(|j| (g * Scalar::from((j + 2) as u64)).into_affine()).collect();
    let u = (g * Scalar::from(99u64)).into_affine();

    // Secret vector a, public vector b (powers of an evaluation point z).
    let a: Vec<Scalar> = (0..4).map(|j| Scalar::from((7 * j + 3) as u64)).collect();
    let z = Scalar::from(5u64);
    let b: Vec<Scalar> = (0..4).map(|j| z.pow([j as u64])).collect();

    // Commitment P = <a,G> + <a,b>·U.
    let p0 = msm(&a, &gens) + u * inner(&a, &b);

    // --- fold k=2 rounds ---
    let mut av = a.clone();
    let mut bv = b.clone();
    let mut gv = gens.clone();
    let mut p = p0;
    let mut ls = Vec::new();
    let mut rs = Vec::new();
    let mut xs = Vec::new();
    let mut xinvs = Vec::new();
    let mut prev_x_base: Option<Base> = None;

    while av.len() > 1 {
        let m = av.len() / 2;
        let (alo, ahi) = av.split_at(m);
        let (blo, bhi) = bv.split_at(m);
        let (glo, ghi) = gv.split_at(m);

        let l = (msm(alo, ghi) + u * inner(alo, bhi)).into_affine();
        let r = (msm(ahi, glo) + u * inner(ahi, blo)).into_affine();

        // FS: x = challenge(transcript). Round 0 binds P; later rounds bind prev x.
        let seed = prev_x_base.unwrap_or(base_from(p.into_affine().x));
        let x = challenge(&[seed, l.x, l.y, r.x, r.y]);
        let xinv = x.inverse().unwrap();
        prev_x_base = Some(scalar_to_base(&x));

        // fold vectors/points/commitment
        let anew: Vec<Scalar> = (0..m).map(|i| alo[i] * x + ahi[i] * xinv).collect();
        let bnew: Vec<Scalar> = (0..m).map(|i| blo[i] * xinv + bhi[i] * x).collect();
        let gnew: Vec<Affine> = (0..m).map(|i| (glo[i] * xinv + ghi[i] * x).into_affine()).collect();
        let x2 = x * x;
        let xinv2 = xinv * xinv;
        p = l * x2 + p + r * xinv2;

        av = anew;
        bv = bnew;
        gv = gnew;
        ls.push(l);
        rs.push(r);
        xs.push(x);
        xinvs.push(xinv);
    }

    let a_star = av[0];
    let b_star = bv[0];
    let g_star = gv[0];
    let c = a_star * b_star;
    let p_final = p.into_affine();

    // challenge-product vector s: G* = Σ sⱼ·Gⱼ. j's bits pick x (hi) / xinv (lo).
    let s: Vec<Scalar> = (0..4)
        .map(|j| {
            // round 0 split is by the HIGH bit, round 1 by the LOW bit.
            let e_r0 = if (j >> 1) & 1 == 1 { xs[0] } else { xinvs[0] };
            let e_r1 = if j & 1 == 1 { xs[1] } else { xinvs[1] };
            e_r0 * e_r1
        })
        .collect();

    // --- SELF-VALIDATE the IPA relations before emitting anything ---
    assert_eq!(msm(&s, &gens).into_affine(), g_star, "G* != <s,G>");
    assert_eq!(inner(&s, &b), b_star, "b* != <s,b>");
    let rhs = (g_star * a_star + u * c).into_affine();
    assert_eq!(p_final, rhs, "IPA final relation failed");
    eprintln!("[ok] IPA relations validated: P_final == a*·G* + (a*·b*)·U, G* == <s,G>");

    // --- emit circuit inputs ---
    println!("// ==== grumpkin_ipa_fold n=4 k=2 (validated) ====");
    for (j, gj) in gens.iter().enumerate() {
        println!("const G{j}X: &str = \"{}\";", base_dec(&gj.x));
        println!("const G{j}Y: &str = \"{}\";", base_dec(&gj.y));
    }
    println!("const UX: &str = \"{}\";", base_dec(&u.x));
    println!("const UY: &str = \"{}\";", base_dec(&u.y));
    println!("const PX: &str = \"{}\";", base_dec(&p0.into_affine().x));
    println!("const PY: &str = \"{}\";", base_dec(&p0.into_affine().y));
    for (i, (l, r)) in ls.iter().zip(&rs).enumerate() {
        println!("const L{i}X: &str = \"{}\";", base_dec(&l.x));
        println!("const L{i}Y: &str = \"{}\";", base_dec(&l.y));
        println!("const R{i}X: &str = \"{}\";", base_dec(&r.x));
        println!("const R{i}Y: &str = \"{}\";", base_dec(&r.y));
        println!("const X{i}: &str = \"{}\";       // in-circuit-derived (128-bit)", scalar_dec(&xs[i]));
        let (lo, hi) = limbs127(&xinvs[i]);
        println!("const X{i}INV_LO: &str = \"{lo}\";");
        println!("const X{i}INV_HI: &str = \"{hi}\";");
    }
    for (j, sj) in s.iter().enumerate() {
        let (lo, hi) = limbs127(sj);
        println!("const S{j}LO: &str = \"{lo}\";");
        println!("const S{j}HI: &str = \"{hi}\";");
    }
    let (alo, ahi) = limbs127(&a_star);
    println!("const ASTAR_LO: &str = \"{alo}\";");
    println!("const ASTAR_HI: &str = \"{ahi}\";");
    let (clo, chi) = limbs127(&c);
    println!("const C_LO: &str = \"{clo}\";");
    println!("const C_HI: &str = \"{chi}\";");
    for (j, bj) in b.iter().enumerate() {
        println!("const B{j}: &str = \"{}\";", scalar_dec(bj));
    }
}

fn base_from(x: Base) -> Base {
    x
}
