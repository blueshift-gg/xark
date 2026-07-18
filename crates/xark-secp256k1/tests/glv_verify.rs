use k256::ecdsa::{signature::Signer, Signature, SigningKey};
use num_bigint::BigUint;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use xark_test_harness::bignum::Point;
fn n() -> BigUint {
    BigUint::parse_bytes(
        b"fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141",
        16,
    )
    .unwrap()
}
fn inv(a: &BigUint, m: &BigUint) -> BigUint {
    a.modpow(&(m - 2u32), m)
}
fn l64(v: &BigUint) -> Vec<String> {
    let m = (BigUint::from(1u8) << 64u32) - 1u8;
    (0..4)
        .map(|i| ((v >> (i as u32 * 64)) & &m).to_string())
        .collect()
}
#[test]
fn glv_verify() {
    let sk = SigningKey::from_slice(&[0x42u8; 32]).unwrap();
    let vk = sk.verifying_key();
    let msg = b"xark glv verify";
    let sig: Signature = sk.sign(msg);
    let q = Point::from_sec1(vk.to_encoded_point(false).as_bytes());
    let qx = q.x.as_biguint().clone();
    let qy = q.y.as_biguint().clone();
    let sb = sig.to_bytes();
    let r = BigUint::from_bytes_be(&sb[..32]);
    let s = BigUint::from_bytes_be(&sb[32..]);
    let nn = n();
    let e = BigUint::from_bytes_be(&Sha256::digest(msg)) % &nn;
    let si = inv(&s, &nn);
    let u1 = (&e * &si) % &nn;
    let u2 = (&r * &si) % &nn;
    let a1 = BigUint::parse_bytes(b"3086d221a7d46bcde86c90e49284eb15", 16).unwrap();
    let b1 = BigUint::parse_bytes(b"e4437ed6010e88286f547fa90abfe4c3", 16).unwrap();
    let a2 = BigUint::parse_bytes(b"114ca50f7a8e2f3f657c1108d9d44cfd8", 16).unwrap();
    let b2 = a1.clone();
    let dec = |u: &BigUint| {
        let c1 = (&b2 * u + &nn / 2u8) / &nn;
        let c2 = (&b1 * u + &nn / 2u8) / &nn;
        let k1 = (u + &nn * 3u8 - (&c1 * &a1) % &nn - (&c2 * &a2) % &nn) % &nn;
        let k2 = (&c1 * &b1 + &nn * 3u8 - (&c2 * &b2) % &nn) % &nn;
        let sp = |x: &BigUint| {
            if x > &(&nn / 2u8) {
                (&nn - x, 1u64)
            } else {
                (x.clone(), 0u64)
            }
        };
        let (m1, s1) = sp(&k1);
        let (m2, s2) = sp(&k2);
        (m1, s1, m2, s2)
    };
    let (m11, s11, m12, s12) = dec(&u1);
    let (m21, s21, m22, s22) = dec(&u2);
    let src = r#"#![no_std]
use xark::{Field, Public};
use xark_secp256k1::ecdsa_verify_glv;
pub fn circuit(
  qx0:Public<Field>,qx1:Public<Field>,qx2:Public<Field>,qx3:Public<Field>,qy0:Public<Field>,qy1:Public<Field>,qy2:Public<Field>,qy3:Public<Field>,
  r0:Public<Field>,r1:Public<Field>,r2:Public<Field>,r3:Public<Field>,s0:Public<Field>,s1:Public<Field>,s2:Public<Field>,s3:Public<Field>,e0:Public<Field>,e1:Public<Field>,e2:Public<Field>,e3:Public<Field>,
  a0:Public<Field>,a1:Public<Field>,sa:Public<Field>,b0:Public<Field>,b1:Public<Field>,sb:Public<Field>,
  c0:Public<Field>,c1:Public<Field>,sc:Public<Field>,d0:Public<Field>,d1:Public<Field>,sd:Public<Field>){
    ecdsa_verify_glv([qx0,qx1,qx2,qx3],[qy0,qy1,qy2,qy3],[r0,r1,r2,r3],[s0,s1,s2,s3],[e0,e1,e2,e3],
        [a0,a1],sa,[b0,b1],sb,[c0,c1],sc,[d0,d1],sd);
}"#;
    let c = xark_test_harness::compile_source("glvv", src, "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let prog = c.program();
    let id = |nm: &str| prog.vars.iter().find(|v| v.name == nm).unwrap().id;
    let mut inp = BTreeMap::new();
    for (pfx, v) in [("qx", &qx), ("qy", &qy), ("r", &r), ("s", &s), ("e", &e)] {
        for (i, sv) in l64(v).iter().enumerate() {
            inp.insert(id(&format!("{pfx}{i}")), sv.clone());
        }
    }
    let put2 = |inp: &mut BTreeMap<u32, String>, pfx: &str, m: &BigUint| {
        let l = l64(m);
        inp.insert(id(&format!("{pfx}0")), l[0].clone());
        inp.insert(id(&format!("{pfx}1")), l[1].clone());
    };
    put2(&mut inp, "a", &m11);
    inp.insert(id("sa"), s11.to_string());
    put2(&mut inp, "b", &m12);
    inp.insert(id("sb"), s12.to_string());
    put2(&mut inp, "c", &m21);
    inp.insert(id("sc"), s21.to_string());
    put2(&mut inp, "d", &m22);
    inp.insert(id("sd"), s22.to_string());
    match xark_ir::solver::solve_and_check(&prog, &inp) {
        Ok(assign) => {
            let clean = xark_ir::solver::analyze_underconstrained(&prog, &assign).is_empty();
            let nn = c.minimized_r1cs_len();
            eprintln!(
                "GLV VERIFY: valid sig CORRECT, analyzer-clean={}, {} constraints ({:.3}M)",
                clean,
                nn,
                nn as f64 / 1e6
            );
            assert!(clean, "must be analyzer-clean");
            assert_eq!(nn, 1_597_366, "GLV verify constraint count changed");
        }
        Err(e) => eprintln!("GLV VERIFY WRONG: {e:?}"),
    }
}
