//! Reference for a COMPLETE (identity-safe) Grumpkin affine addition — the
//! prerequisite for real Nova folding (fresh instances have comm_E = ∞). Emits
//! the five exceptional cases as flagged triples (x, y, inf); inf=1 ⇒ (0,0,1).

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{PrimeField, Zero};
use ark_grumpkin::{Affine, Fq as Base, Fr as Scalar, Projective};

fn bd(x: &Base) -> String {
    x.into_bigint().to_string()
}
fn pt(k: u64) -> Affine {
    (Affine::generator() * Scalar::from(k)).into_affine()
}
// print a flagged triple for a projective point (handles ∞)
fn emit(name: &str, p: Projective) {
    let a = p.into_affine();
    if a.is_zero() {
        println!("const {name}: (&str,&str,&str) = (\"0\",\"0\",\"1\");");
    } else {
        println!("const {name}: (&str,&str,&str) = (\"{}\",\"{}\",\"0\");", bd(&a.x), bd(&a.y));
    }
}

fn main() {
    let p = pt(7);
    let q = pt(9);
    let zero = Projective::zero();

    println!("// ==== complete-add cases: P=7·G, Q=9·G ====");
    // operands
    emit("P", p.into_group());
    emit("Q", q.into_group());
    emit("NEG_P", (-p).into_group());
    // results
    emit("P_PLUS_ZERO", p.into_group() + zero); // = P
    emit("ZERO_PLUS_Q", zero + q.into_group()); // = Q
    emit("P_PLUS_NEGP", p.into_group() + (-p).into_group()); // = ∞
    emit("P_PLUS_P", p.into_group() + p.into_group()); // = 2P
    emit("P_PLUS_Q", p.into_group() + q.into_group()); // = P+Q
    emit("ZERO_PLUS_ZERO", zero + zero); // = ∞
}
