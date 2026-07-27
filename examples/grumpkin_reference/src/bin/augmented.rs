//! Reference for one Nova AUGMENTED STEP `F'` with Poseidon2 IO compression.
//! Runs `z_{i+1} = F(z_i)` (`F(z)=z²+5`), folds the running instance `U_i` with a
//! fresh instance `s` (cross-term `T`) into `U_{i+1}`, and compresses the whole
//! step state into two hashes:
//!   io = Poseidon2(i, z0, z, comm_W.x, comm_W.y, comm_E.x, comm_E.y, u, x)
//! so the circuit's only public inputs are `io_in` and `io_out`.

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

fn io_hash(i: u64, z0: Base, z: Base, inst: &Inst) -> Base {
    poseidon2::hash([
        Base::from(i),
        z0,
        z,
        inst.cw.x,
        inst.cw.y,
        inst.ce.x,
        inst.ce.y,
        inst.u,
        inst.x,
    ])
}

fn main() {
    let z0 = Base::from(3u64);
    let zi = z0; // step 0 input state
    let z_next = f(zi); // 14

    let ui = Inst { cw: pt(11), ce: pt(22), u: Base::from(7u64), x: Base::from(13u64) };
    let s = Inst { cw: pt(31), ce: pt(41), u: Base::from(1u64), x: Base::from(5u64) };
    let t = pt(51);

    let u_next = fold(&ui, &s, &t, z_next);
    let io_in = io_hash(0, z0, zi, &ui);
    let io_out = io_hash(1, z0, z_next, &u_next);

    eprintln!("[ok] augmented step: z {} -> {}", bd(&zi), bd(&z_next));
    println!("// ==== grumpkin_augmented_step reference ====");
    println!("const IO_IN: &str = \"{}\";", bd(&io_in));
    println!("const IO_OUT: &str = \"{}\";", bd(&io_out));
    println!("const Z0: &str = \"{}\";", bd(&z0));
    println!("const ZI: &str = \"{}\";", bd(&zi));
    let inst = |n: &str, i: &Inst| {
        println!("const {n}_CWX: &str = \"{}\";", bd(&i.cw.x));
        println!("const {n}_CWY: &str = \"{}\";", bd(&i.cw.y));
        println!("const {n}_CEX: &str = \"{}\";", bd(&i.ce.x));
        println!("const {n}_CEY: &str = \"{}\";", bd(&i.ce.y));
        println!("const {n}_U: &str = \"{}\";", bd(&i.u));
        println!("const {n}_X: &str = \"{}\";", bd(&i.x));
    };
    inst("UI", &ui);
    inst("S", &s);
    println!("const TX: &str = \"{}\";", bd(&t.x));
    println!("const TY: &str = \"{}\";", bd(&t.y));
}
