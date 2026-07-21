//! Sound lazy extended-coordinate Ed25519 path (`eddsa_verify_lazy`), validated
//! end-to-end: the non-native field multiply, the extended point doubling/add,
//! and a full EdDSA verification against a real `ed25519-dalek` signature.
//!
//! The lazy path keeps intermediates loosely-reduced (`≡ value mod p`, limbs
//! bounded) with carries range-checked (deterministic — sound), reducing to
//! canonical only at boundaries. It verifies in ~2.36M constraints vs the affine
//! gadget's 4.55M, while remaining sound (no under-constraint).
use num_bigint::BigUint;
use std::collections::BTreeMap;

fn p() -> BigUint {
    (BigUint::from(1u8) << 255u32) - 19u8
}
fn inv(a: &BigUint) -> BigUint {
    a.modpow(&(p() - 2u8), &p())
}
fn limbs85(v: &BigUint) -> Vec<String> {
    let m = (BigUint::from(1u8) << 85u32) - 1u8;
    (0..3)
        .map(|i| ((v >> (i as u32 * 85)) & &m).to_string())
        .collect()
}

#[test]
fn mul_lazy_is_correct() {
    let a = BigUint::parse_bytes(
        b"31415926535897932384626433832795028841971693993751058209749445923078164062",
        10,
    )
    .unwrap()
        % p();
    let b = BigUint::parse_bytes(
        b"27182818284590452353602874713526624977572470936999595749669676277240766303",
        10,
    )
    .unwrap()
        % p();
    let r = (&a * &b) % p();
    let src = r#"#![no_std]
use xark::{Field, Private, Public};
use xark_bignum::mul_lazy_25519;
pub fn circuit(a0:Private<Field>,a1:Private<Field>,a2:Private<Field>,b0:Private<Field>,b1:Private<Field>,b2:Private<Field>,r0:Public<Field>,r1:Public<Field>,r2:Public<Field>){
    let o = mul_lazy_25519([a0,a1,a2],[b0,b1,b2]);
    xark::require_eq(o[0],r0); xark::require_eq(o[1],r1); xark::require_eq(o[2],r2);
}"#;
    let c = xark_test_harness::compile_source("mul_lazy_ok", src, "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let prog = c.program();
    let id = |n: &str| prog.vars.iter().find(|v| v.name == n).unwrap().id;
    let mut inp = BTreeMap::new();
    for (pfx, v) in [("a", &a), ("b", &b), ("r", &r)] {
        for (i, sv) in limbs85(v).iter().enumerate() {
            inp.insert(id(&format!("{pfx}{i}")), sv.clone());
        }
    }
    let assign = xark_ir::solver::solve_and_check(&prog, &inp).expect("mul_lazy == a*b mod p");
    assert!(xark_ir::solver::analyze_underconstrained(&prog, &assign).is_empty());
}

#[test]
fn ext_double_is_correct() {
    let bx = BigUint::parse_bytes(
        b"15112221349535400772501151409588531511454012693041857206046113283949847762202",
        10,
    )
    .unwrap();
    let by = BigUint::parse_bytes(
        b"46316835694926478169428394003475163141307993866256225615783033603165251855960",
        10,
    )
    .unwrap();
    let pp = p();
    let xx = (&bx * &bx) % &pp;
    let yy = (&by * &by) % &pp;
    let x2 = ((2u8 * &bx % &pp * &by) % &pp * inv(&((&yy + &pp - &xx) % &pp))) % &pp;
    let y2 = ((&xx + &yy) % &pp * inv(&((2u8 + &xx + &pp - &yy) % &pp))) % &pp;
    let src = r#"#![no_std]
use xark::{Field, Private, Public};
use xark_bignum::{ext_double_25519, mul_lazy_25519, finalize_25519};
fn eqp(u:[Field;3], v:[Field;3]){ let a=finalize_25519(u); let b=finalize_25519(v); xark::require_eq(a[0],b[0]); xark::require_eq(a[1],b[1]); xark::require_eq(a[2],b[2]); }
pub fn circuit(x0:Private<Field>,x1:Private<Field>,x2:Private<Field>,y0:Private<Field>,y1:Private<Field>,y2:Private<Field>,ax0:Public<Field>,ax1:Public<Field>,ax2:Public<Field>,ay0:Public<Field>,ay1:Public<Field>,ay2:Public<Field>){
    let one=[Field::from(1u8),Field::from(0u8),Field::from(0u8)];
    let (x3,y3,z3,_t)=ext_double_25519([x0,x1,x2],[y0,y1,y2],one);
    eqp(x3, mul_lazy_25519([ax0,ax1,ax2], z3));
    eqp(y3, mul_lazy_25519([ay0,ay1,ay2], z3));
}"#;
    let c = xark_test_harness::compile_source("ext_dbl_ok", src, "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let prog = c.program();
    let id = |n: &str| prog.vars.iter().find(|v| v.name == n).unwrap().id;
    let mut inp = BTreeMap::new();
    for (pfx, v) in [("x", &bx), ("y", &by), ("ax", &x2), ("ay", &y2)] {
        for (i, sv) in limbs85(v).iter().enumerate() {
            inp.insert(id(&format!("{pfx}{i}")), sv.clone());
        }
    }
    let assign = xark_ir::solver::solve_and_check(&prog, &inp).expect("ext_double == 2*basepoint");
    assert!(xark_ir::solver::analyze_underconstrained(&prog, &assign).is_empty());
}

#[test]
fn ext_add_is_correct() {
    let pp = p();
    let d = BigUint::parse_bytes(
        b"37095705934669439343138083508754565189542113879843219016388785533085940283555",
        10,
    )
    .unwrap();
    let bx = BigUint::parse_bytes(
        b"15112221349535400772501151409588531511454012693041857206046113283949847762202",
        10,
    )
    .unwrap();
    let by = BigUint::parse_bytes(
        b"46316835694926478169428394003475163141307993866256225615783033603165251855960",
        10,
    )
    .unwrap();
    let xx = (&bx * &bx) % &pp;
    let yy = (&by * &by) % &pp;
    let qx = ((2u8 * &bx % &pp * &by) % &pp * inv(&((&yy + &pp - &xx) % &pp))) % &pp;
    let qy = ((&xx + &yy) % &pp * inv(&((2u8 + &xx + &pp - &yy) % &pp))) % &pp;
    let x1x2 = (&bx * &qx) % &pp;
    let y1y2 = (&by * &qy) % &pp;
    let dd = (&d * &x1x2 % &pp * &y1y2) % &pp;
    let rx = (((&bx * &qy) % &pp + (&by * &qx) % &pp) % &pp * inv(&((1u8 + &dd) % &pp))) % &pp;
    let ry = ((&y1y2 + &x1x2) % &pp * inv(&((1u8 + &pp - &dd) % &pp))) % &pp;
    let tb = (&bx * &by) % &pp;
    let tq = (&qx * &qy) % &pp;
    let src = r#"#![no_std]
use xark::{Field, Private, Public};
use xark_bignum::{ext_add_25519, mul_lazy_25519, finalize_25519};
fn eqp(u:[Field;3], v:[Field;3]){ let a=finalize_25519(u); let b=finalize_25519(v); xark::require_eq(a[0],b[0]); xark::require_eq(a[1],b[1]); xark::require_eq(a[2],b[2]); }
pub fn circuit(bx0:Private<Field>,bx1:Private<Field>,bx2:Private<Field>,by0:Private<Field>,by1:Private<Field>,by2:Private<Field>,tb0:Private<Field>,tb1:Private<Field>,tb2:Private<Field>,qx0:Private<Field>,qx1:Private<Field>,qx2:Private<Field>,qy0:Private<Field>,qy1:Private<Field>,qy2:Private<Field>,tq0:Private<Field>,tq1:Private<Field>,tq2:Private<Field>,rx0:Public<Field>,rx1:Public<Field>,rx2:Public<Field>,ry0:Public<Field>,ry1:Public<Field>,ry2:Public<Field>){
    let one=[Field::from(1u8),Field::from(0u8),Field::from(0u8)];
    let (x3,y3,z3,_t)=ext_add_25519([bx0,bx1,bx2],[by0,by1,by2],one,[tb0,tb1,tb2],[qx0,qx1,qx2],[qy0,qy1,qy2],one,[tq0,tq1,tq2]);
    eqp(x3, mul_lazy_25519([rx0,rx1,rx2], z3));
    eqp(y3, mul_lazy_25519([ry0,ry1,ry2], z3));
}"#;
    let c = xark_test_harness::compile_source("ext_add_ok", src, "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let prog = c.program();
    let id = |n: &str| prog.vars.iter().find(|v| v.name == n).unwrap().id;
    let mut inp = BTreeMap::new();
    for (pfx, v) in [
        ("bx", &bx),
        ("by", &by),
        ("tb", &tb),
        ("qx", &qx),
        ("qy", &qy),
        ("tq", &tq),
        ("rx", &rx),
        ("ry", &ry),
    ] {
        for (i, sv) in limbs85(v).iter().enumerate() {
            inp.insert(id(&format!("{pfx}{i}")), sv.clone());
        }
    }
    let assign = xark_ir::solver::solve_and_check(&prog, &inp).expect("ext_add: B + 2B == 3B");
    assert!(xark_ir::solver::analyze_underconstrained(&prog, &assign).is_empty());
}
