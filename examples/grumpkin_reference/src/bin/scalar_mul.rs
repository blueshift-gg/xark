//! Reference vectors for `xark_grumpkin::{scalar_mul, wide_scalar_mul,
//! multi_scalar_mul}`: prints the constants in `gadgets/xark-grumpkin/tests/vec.rs`.
//! `P = 7·G`, `Q = 9·G`; `O = (5, …)` is the gadgets' offset point.

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

fn mul(p: Affine, s: &BigUint) -> Affine {
    (p * Scalar::from(s.clone())).into_affine()
}

fn emit(name: &str, a: Affine) {
    assert!(!a.is_zero(), "{name} is the identity");
    println!("const {name}: (&str, &str) = (\"{}\", \"{}\");", bd(&a.x), bd(&a.y));
}

fn main() {
    let p = pt(7);
    let q = pt(9);
    let o = Affine::new(
        Base::from(5u8),
        Base::from(
            BigUint::parse_bytes(b"26447525821777463057023244913909144251512587297343525263882", 10)
                .unwrap(),
        ),
    );
    let one = BigUint::from(1u8);
    let max128: BigUint = (BigUint::from(1u8) << 128u32) - 1u8;
    let max254: BigUint = (BigUint::from(1u8) << 254u32) - 1u8;
    let r = BigUint::from_bytes_le(&Base::MODULUS.to_bytes_le());
    let n = BigUint::from_bytes_le(&Scalar::MODULUS.to_bytes_le());
    let mid = BigUint::parse_bytes(b"338770000845734292534325025077361652240", 10).unwrap();

    println!("// P = 7·G, Q = 9·G, O = the offset");
    emit("P", p);
    emit("Q", q);
    emit("O", o);
    emit("NEG_O", -o);
    emit("NEG_P", -p);
    println!("const R_MINUS_1: &str = \"{}\";", &r - 1u8);
    println!("const N_MINUS_1: &str = \"{}\";", &n - 1u8);
    println!("// scalar_mul (128-bit)");
    emit("P_X1", mul(p, &one));
    emit("P_X2", mul(p, &BigUint::from(2u8)));
    emit("P_XMID", mul(p, &mid));
    emit("P_XMAX128", mul(p, &max128));
    println!("// wide_scalar_mul (254-bit): scalars as their 127-bit limbs `(lo, hi)`");
    let mask: BigUint = (BigUint::from(1u8) << 127u32) - 1u8;
    for (name, s) in [("R1", &r - 1u8), ("N1", &n - 1u8), ("MAX254", max254.clone())] {
        println!("const {name}_LIMBS: (&str, &str) = (\"{}\", \"{}\");", &s & &mask, &s >> 127u32);
    }
    emit("P_XR1", mul(p, &(&r - 1u8)));
    emit("P_XN1", mul(p, &(&n - 1u8)));
    emit("P_XMAX254", mul(p, &max254));
    println!("// multi_scalar_mul");
    emit("MSM_0_MID", mul(q, &mid));
    emit("MSM_MAX_1", (mul(p, &max128) + q).into_affine());
    emit("MSM_O_P", (mul(o, &mid) + mul(p, &BigUint::from(3u8))).into_affine());
    // The true results of the degenerate MSM inputs the circuit rejects.
    emit("P_X12", mul(p, &BigUint::from(12u8)));
    emit("NEG_P_X2", -mul(p, &BigUint::from(2u8)));
    let q1 = Affine::new(
        Base::from(10u8),
        Base::from(
            BigUint::parse_bytes(
                b"3764497608137669826449761938357951019955713832105137848030504861970310222496",
                10,
            )
            .unwrap(),
        ),
    );
    let s1 = BigUint::parse_bytes(b"338770000845734292534325025077361652240", 10).unwrap();
    emit("S1_Q1", mul(q1, &s1));
}
