//! A generated RSA-2048 PKCS#1 v1.5 SHA-256 signature.
//!
//! The host hashes the test message with SHA-256, decodes the big-endian
//! modulus and signature, and passes those three values to the circuit.

use std::collections::BTreeMap;

use num_bigint::BigUint;
use sha2::{Digest, Sha256};
use xark_ir::{primitive, solver};

const N_HEX: &str = "B4AFCE0C2B5961134236B5BA13AD4F12588F46BA02BA0724B9FBDC14800ECEE5FD90FA573EBBE10613B48A6784FBB85FF2DD527B765BB9041168DF35E45BCD8244E689C32F2829D0EB323761A3F1BC6F71DBDC96D08D8CBDF12264941219178B2A93A8963DABB80679D8613DC346E0D29420E97F889216C9555AC533904B4364E8C06FA81C44C7DC70ECE28372D543FE7CD14B2A9D5516D6A299FBEC68CA553305EBD79C5F113812A785C1CE679513AC234F7786A1E871833FED75A8778CF741452915F4A979792C9FA22AF82F60785CFB9CA0A3437A9F90C657E8590340958A6A8C2CEDD7E7714135C030844542A9EC88137346A97EDDE441630B7D2B6AD3AF";
const SIG_HEX: &str = "7cde0ace8e6e4f3e4b55c6902d73d092a3581f04ec44f9cccd0bf5e1838b66e46a0927bd52ad223547c0e757175641c07ae543319f69644c27a6151cc228a900f29f23c2178ac0b319de2a1887815592805d0f52298fd7d0bad7a71e803aeff3e628b397355e66ecf4cddfa730f5e25e5ab93438611e68bf147a18e0cbe051346f5450c91e554d99eea8d3f6055f380a2ab9f969f20d971391f6a578f6e139c6ecff44884d46891cde5bfc61a2cf438f20f9a82f76e6bdd0c206498598197005e96bddbb80a65733ccb9111206b4e6a7658499900c285fd0f304128e5f1143ebb013762acda4c3681b4c03859dd336a3b0abe959a6e02cb24147f8d06d127b0a";
const DIGEST_HEX: &str = "715976a685083f4be3a60e926f9e31a5b671a4a389b4cf709afb4c0c41c96baa";
const MESSAGE: &[u8] = b"xark RSA-2048 PKCS#1 v1.5 SHA-256 generic test vector";

fn load() -> primitive::PrimitiveProgram {
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/rsa2048.rs");
    let c = xark_test_harness::compile_file(&src, "rsa2048", "bn254");
    assert!(
        c.status_success,
        "compiling rsa2048 fixture failed: {}",
        c.stderr
    );
    let gates = c.mul_gate_count();
    let p = c.program();
    println!(
        "rsa2048: {} primitive constraints, {} multiplication gates",
        p.constraints.len(),
        gates
    );
    p
}

fn load_bytes() -> primitive::PrimitiveProgram {
    let src =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/rsa2048_bytes.rs");
    let c = xark_test_harness::compile_file(&src, "rsa2048_bytes", "bn254");
    assert!(
        c.status_success,
        "compiling rsa2048_bytes fixture failed: {}",
        c.stderr
    );
    let gates = c.mul_gate_count();
    let p = c.program();
    println!(
        "rsa2048_bytes: {} primitive constraints, {} multiplication gates",
        p.constraints.len(),
        gates
    );
    p
}

fn n_bytes() -> [u8; 256] {
    hex::decode(N_HEX).unwrap().try_into().unwrap()
}

fn sig_bytes() -> [u8; 256] {
    hex::decode(SIG_HEX).unwrap().try_into().unwrap()
}

fn inputs_bytes(p: &primitive::PrimitiveProgram, digest: [u8; 32]) -> BTreeMap<u32, String> {
    let id = |n: &str| {
        p.vars
            .iter()
            .find(|v| v.name == n)
            .unwrap_or_else(|| panic!("missing `{n}`"))
            .id
    };
    let mut out = BTreeMap::new();
    for (i, b) in n_bytes().iter().enumerate() {
        out.insert(id(&format!("n[{i}]")), b.to_string());
    }
    for (i, b) in sig_bytes().iter().enumerate() {
        out.insert(id(&format!("sig[{i}]")), b.to_string());
    }
    for (i, b) in digest.iter().enumerate() {
        out.insert(id(&format!("digest[{i}]")), b.to_string());
    }
    out
}

fn limbs_121(x: &BigUint) -> Vec<String> {
    let mask = (BigUint::from(1u8) << 121u32) - 1u8;
    (0..17)
        .map(|i| ((x >> (121u32 * i)) & &mask).to_string())
        .collect()
}

fn inputs(p: &primitive::PrimitiveProgram, digest: [u8; 32]) -> BTreeMap<u32, String> {
    let id = |n: &str| {
        p.vars
            .iter()
            .find(|v| v.name == n)
            .unwrap_or_else(|| panic!("missing `{n}`"))
            .id
    };
    let n = BigUint::parse_bytes(N_HEX.as_bytes(), 16).unwrap();
    let s = BigUint::parse_bytes(SIG_HEX.as_bytes(), 16).unwrap();
    let mut out = BTreeMap::new();
    for (i, l) in limbs_121(&n).into_iter().enumerate() {
        out.insert(id(&format!("n[{i}]")), l);
    }
    for (i, l) in limbs_121(&s).into_iter().enumerate() {
        out.insert(id(&format!("sig[{i}]")), l);
    }
    for (i, b) in digest.iter().enumerate() {
        out.insert(id(&format!("digest[{i}]")), b.to_string());
    }
    out
}

fn digest() -> [u8; 32] {
    hex::decode(DIGEST_HEX).unwrap().try_into().unwrap()
}

#[test]
fn digest_is_sha256_of_the_test_message() {
    let d: [u8; 32] = Sha256::digest(MESSAGE).into();
    assert_eq!(hex::encode(d), DIGEST_HEX);
    assert_eq!(d, digest());
}

#[test]
fn accepts_the_generated_rsa_signature() {
    let p = load();
    let assign = solver::solve_and_check(&p, &inputs(&p, digest()))
        .unwrap_or_else(|e| panic!("honest RSA signature must solve: {e:?}"));
    assert!(solver::analyze_underconstrained(&p, &assign).is_empty());
}

#[test]
fn rejects_a_tampered_digest() {
    let p = load();
    let mut d = digest();
    d[0] ^= 1;
    assert!(solver::solve_and_check(&p, &inputs(&p, d)).is_err());
}

#[test]
fn accepts_the_generated_rsa_signature_bytes() {
    let p = load_bytes();
    let assign = solver::solve_and_check(&p, &inputs_bytes(&p, digest()))
        .unwrap_or_else(|e| panic!("honest byte-input RSA signature must solve: {e:?}"));
    assert!(solver::analyze_underconstrained(&p, &assign).is_empty());
}

#[test]
fn rejects_a_tampered_digest_bytes() {
    let p = load_bytes();
    let mut d = digest();
    d[0] ^= 1;
    assert!(solver::solve_and_check(&p, &inputs_bytes(&p, d)).is_err());
}
