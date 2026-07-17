//! Full sound lazy secp256k1 ECDSA verify (`ecdsa_verify_lazy`, 4×64 lazy-affine)
//! against a real `k256` signature: valid accepts, tampered rejects.
use k256::ecdsa::{signature::Signer, Signature, SigningKey};
use num_bigint::BigUint;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use xark_test_harness::bignum::Point;

fn limbs64(v: &BigUint) -> Vec<String> {
    let m = (BigUint::from(1u8) << 64u32) - 1u8;
    (0..4)
        .map(|i| ((v >> (i as u32 * 64)) & &m).to_string())
        .collect()
}

#[test]
fn ecdsa_lazy_matches_k256() {
    let sk = SigningKey::from_slice(&[0x42u8; 32]).unwrap();
    let vk = sk.verifying_key();
    let msg = b"xark secp256k1 lazy ecdsa vector";
    let sig: Signature = sk.sign(msg);
    let q = Point::from_sec1(vk.to_encoded_point(false).as_bytes());
    let qx = q.x.as_biguint().clone();
    let qy = q.y.as_biguint().clone();
    let sig_bytes = sig.to_bytes();
    let r = BigUint::from_bytes_be(&sig_bytes[..32]);
    let s = BigUint::from_bytes_be(&sig_bytes[32..]);
    let n = BigUint::parse_bytes(
        b"fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141",
        16,
    )
    .unwrap();
    let e = BigUint::from_bytes_be(&Sha256::digest(msg)) % &n;

    let src = r#"#![no_std]
use xark::{Field, Public};
use xark_secp256k1::ecdsa_verify_lazy;
pub fn circuit(
  qx0:Public<Field>,qx1:Public<Field>,qx2:Public<Field>,qx3:Public<Field>, qy0:Public<Field>,qy1:Public<Field>,qy2:Public<Field>,qy3:Public<Field>,
  r0:Public<Field>,r1:Public<Field>,r2:Public<Field>,r3:Public<Field>, s0:Public<Field>,s1:Public<Field>,s2:Public<Field>,s3:Public<Field>,
  e0:Public<Field>,e1:Public<Field>,e2:Public<Field>,e3:Public<Field>){
    ecdsa_verify_lazy([qx0,qx1,qx2,qx3],[qy0,qy1,qy2,qy3],[r0,r1,r2,r3],[s0,s1,s2,s3],[e0,e1,e2,e3]);
}"#;
    let c = xark_test_harness::compile_source("ecdsa_lazy_vec", src, "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let prog = c.program();
    let id = |n: &str| prog.vars.iter().find(|v| v.name == n).unwrap().id;
    let build = |r_val: &BigUint| {
        let mut inp = BTreeMap::new();
        for (pfx, v) in [("qx", &qx), ("qy", &qy), ("r", r_val), ("s", &s), ("e", &e)] {
            for (i, sv) in limbs64(v).iter().enumerate() {
                inp.insert(id(&format!("{pfx}{i}")), sv.clone());
            }
        }
        inp
    };
    let good = build(&r);
    let assign =
        xark_ir::solver::solve_and_check(&prog, &good).expect("valid k256 signature must verify");
    assert!(xark_ir::solver::analyze_underconstrained(&prog, &assign).is_empty());
    let bad = build(&BigUint::from(1u8));
    assert!(
        xark_ir::solver::solve_and_check(&prog, &bad).is_err(),
        "tampered signature must be rejected"
    );

    let n_c = c.minimized_r1cs_len();
    eprintln!(
        "lazy secp256k1 ecdsa_verify: {n_c} ({:.3}M)",
        n_c as f64 / 1e6
    );
    assert_eq!(
        n_c, 2_322_174,
        "lazy secp256k1 ecdsa_verify constraint count changed"
    );
}
