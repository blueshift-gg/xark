//! Minimal 2-step folding IVC over Grumpkin. Chains the Nova folding step twice
//! while running a computation `z_{i+1} = F(z_i)` (`F(z) = z² + 5`), binding the
//! computation into each fold's Fiat–Shamir challenge. Emits everything the
//! `grumpkin_ivc` circuit verifies: the base accumulator `U0`, the two per-step
//! fresh instances `u0,u1` + cross-terms `T0,T1`, the claimed final accumulator
//! `U2`, and the endpoints `z0,z2`.

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use ark_grumpkin::{Affine, Fq as Base, Fr as Scalar};
use num_bigint::BigUint;

fn bd(x: &Base) -> String {
    x.into_bigint().to_string()
}
fn pt(k: u64) -> Affine {
    (Affine::generator() * Scalar::from(k)).into_affine()
}
fn f(z: Base) -> Base {
    z * z + Base::from(5u64)
}

#[derive(Clone, Copy)]
struct Inst {
    cw: Affine,
    ce: Affine,
    u: Base,
    x: Base,
}

// fold U1,U2 with cross-term T, challenge bound to `z_next`.
fn fold(a: &Inst, b: &Inst, t: &Affine, z_next: Base) -> Inst {
    let tr: [Base; 15] = [
        a.cw.x, a.cw.y, a.ce.x, a.ce.y, a.u, a.x, b.cw.x, b.cw.y, b.ce.x, b.ce.y, b.u, b.x, t.x,
        t.y, z_next,
    ];
    let h = poseidon2::hash(tr);
    let hbig = BigUint::from_bytes_le(&h.into_bigint().to_bytes_le());
    let r_big = &hbig & &((BigUint::from(1u8) << 128u32) - 1u8);
    let r_s = Scalar::from(r_big.clone());
    let r_b = Base::from(r_big);
    Inst {
        cw: (a.cw + b.cw * r_s).into_affine(),
        ce: (a.ce + *t * r_s + b.ce * (r_s * r_s)).into_affine(),
        u: a.u + r_b * b.u,
        x: a.x + r_b * b.x,
    }
}

fn main() {
    let z0 = Base::from(3u64);
    let z1 = f(z0); // 14
    let z2 = f(z1); // 201

    let u0acc = Inst { cw: pt(11), ce: pt(22), u: Base::from(7u64), x: Base::from(13u64) };
    let s0 = Inst { cw: pt(31), ce: pt(41), u: Base::from(1u64), x: Base::from(5u64) };
    let t0 = pt(51);
    let s1 = Inst { cw: pt(61), ce: pt(71), u: Base::from(1u64), x: Base::from(9u64) };
    let t1 = pt(81);

    let u1acc = fold(&u0acc, &s0, &t0, z1);
    let u2acc = fold(&u1acc, &s1, &t1, z2);

    eprintln!("[ok] 2-step IVC: z0={}, z1={}, z2={}", bd(&z0), bd(&z1), bd(&z2));
    println!("// ==== grumpkin_ivc 2-step reference ====");
    let p = |n: &str, a: &Affine| {
        println!("const {n}X: &str = \"{}\";", bd(&a.x));
        println!("const {n}Y: &str = \"{}\";", bd(&a.y));
    };
    let inst = |n: &str, i: &Inst| {
        println!("const {n}_CWX: &str = \"{}\";", bd(&i.cw.x));
        println!("const {n}_CWY: &str = \"{}\";", bd(&i.cw.y));
        println!("const {n}_CEX: &str = \"{}\";", bd(&i.ce.x));
        println!("const {n}_CEY: &str = \"{}\";", bd(&i.ce.y));
        println!("const {n}_U: &str = \"{}\";", bd(&i.u));
        println!("const {n}_X: &str = \"{}\";", bd(&i.x));
    };
    inst("U0", &u0acc);
    inst("S0", &s0);
    p("T0", &t0);
    inst("S1", &s1);
    p("T1", &t1);
    inst("U2", &u2acc);
    println!("const Z0: &str = \"{}\";", bd(&z0));
    println!("const Z2: &str = \"{}\";", bd(&z2));
}
