//! Nova/CycleFold committed-relaxed-R1CS **folding step** over Grumpkin. Folds
//! two committed instances (comm_W, comm_E, u, x) with a Poseidon2 challenge `r`:
//!
//!   comm_W = comm_W1 + r·comm_W2
//!   comm_E = comm_E1 + r·comm_T + r²·comm_E2
//!   u      = u1 + r·u2
//!   x      = x1 + r·x2
//!
//! Only positive powers of `r` → no inverses → fully self-contained in-circuit.
//! `r` is the low 128 bits of Poseidon2(transcript), used as a Grumpkin scalar
//! (for the point folds) AND an Fr element (for u,x) — same 128-bit integer, so
//! canonical in both fields. Emits the values the folding-verifier circuit checks.

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

fn main() {
    // two committed relaxed instances + the cross-term commitment
    let cw1 = pt(11);
    let ce1 = pt(22);
    let u1 = Base::from(7u64);
    let x1 = Base::from(13u64);
    let cw2 = pt(33);
    let ce2 = pt(44);
    let u2 = Base::from(3u64);
    let x2 = Base::from(17u64);
    let ct = pt(55);

    // r = low128(Poseidon2(transcript)), same host crate as the in-circuit gadget
    let transcript: [Base; 14] = [
        cw1.x, cw1.y, ce1.x, ce1.y, u1, x1, cw2.x, cw2.y, ce2.x, ce2.y, u2, x2, ct.x, ct.y,
    ];
    let h = poseidon2::hash(transcript);
    let hbig = BigUint::from_bytes_le(&h.into_bigint().to_bytes_le());
    let r_big = &hbig & &((BigUint::from(1u8) << 128u32) - 1u8);
    let r_s = Scalar::from(r_big.clone()); // Grumpkin scalar
    let r_b = Base::from(r_big.clone()); // Fr element

    // fold
    let cw = (cw1 + cw2 * r_s).into_affine();
    let ce = (ce1 + ct * r_s + ce2 * (r_s * r_s)).into_affine();
    let u = u1 + r_b * u2;
    let x = x1 + r_b * x2;

    eprintln!("[ok] nova fold computed; r(128-bit) = {}", r_big);
    println!("// ==== grumpkin_nova_fold instances + folded result ====");
    let p = |n: &str, a: &Affine| {
        println!("const {n}X: &str = \"{}\";", bd(&a.x));
        println!("const {n}Y: &str = \"{}\";", bd(&a.y));
    };
    p("CW1", &cw1);
    p("CE1", &ce1);
    p("CW2", &cw2);
    p("CE2", &ce2);
    p("CT", &ct);
    println!("const U1: &str = \"{}\";", bd(&u1));
    println!("const X1: &str = \"{}\";", bd(&x1));
    println!("const U2: &str = \"{}\";", bd(&u2));
    println!("const X2: &str = \"{}\";", bd(&x2));
    p("CW", &cw);
    p("CE", &ce);
    println!("const U: &str = \"{}\";", bd(&u));
    println!("const X: &str = \"{}\";", bd(&x));
}
