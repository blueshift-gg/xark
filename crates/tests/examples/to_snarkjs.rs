//! Convert an xark/arkworks Groth16 fixture (verifying_key.bin, proof.bin,
//! public_inputs.json) into snarkjs's JSON formats so an *independent*
//! implementation can verify our proofs:
//!
//! cargo run -p xark-backend --example to_snarkjs -- <fixture_dir> <out_dir>
//! snarkjs groth16 verify <out>/vkey.json <out>/public.json <out>/proof.json
//!
//! snarkjs's verifier (different language, different library) checking our
//! arkworks-produced proof validates both our proof encoding and the Groth16
//! verification equation against a fully separate stack.

use std::path::Path;

use ark_bn254::{Bn254, Fq, Fq2, G1Affine, G2Affine};
use ark_groth16::VerifyingKey;

use xark_backend::keys::Groth16Keys;
use xark_backend::proof::ProofBundle;
use xark_backend::serialization::PublicInputsJson;

fn fq(x: &Fq) -> String {
    // Arkworks `Fp` Display is the canonical decimal integer (not Montgomery).
    x.to_string()
}

fn g1(p: &G1Affine) -> serde_json::Value {
    serde_json::json!([fq(&p.x), fq(&p.y), "1"])
}

fn fq2(x: &Fq2) -> serde_json::Value {
    // snarkjs Fp2 element is [c0, c1] (a + b·u), matching arkworks'.c0/.c1.
    serde_json::json!([fq(&x.c0), fq(&x.c1)])
}

fn g2(p: &G2Affine) -> serde_json::Value {
    serde_json::json!([fq2(&p.x), fq2(&p.y), ["1", "0"]])
}

fn main() {
    let mut args = std::env::args().skip(1);
    let dir = args
        .next()
        .expect("usage: to_snarkjs <fixture_dir> <out_dir>");
    let out = args
        .next()
        .expect("usage: to_snarkjs <fixture_dir> <out_dir>");
    let dir = Path::new(&dir);
    let out = Path::new(&out);
    std::fs::create_dir_all(out).unwrap();

    let vk: VerifyingKey<Bn254> =
        Groth16Keys::read_verifying_key(&dir.join("verifying_key.bin")).expect("read vk");
    let proof = ProofBundle::read_proof(&dir.join("proof.bin")).expect("read proof");
    let pi_json: PublicInputsJson =
        serde_json::from_slice(&std::fs::read(dir.join("public_inputs.json")).expect("read pi"))
            .expect("parse pi");
    let public = pi_json.into_fr().expect("decode pi");

    let vkey = serde_json::json!({
    "protocol": "groth16",
    "curve": "bn128",
    "nPublic": public.len(),
    "vk_alpha_1": g1(&vk.alpha_g1),
    "vk_beta_2": g2(&vk.beta_g2),
    "vk_gamma_2": g2(&vk.gamma_g2),
    "vk_delta_2": g2(&vk.delta_g2),
    "IC": vk.gamma_abc_g1.iter().map(g1).collect::<Vec<_>>(),
    });
    let proof_json = serde_json::json!({
    "pi_a": g1(&proof.a), // original A (snarkjs negates it in the equation)
    "pi_b": g2(&proof.b),
    "pi_c": g1(&proof.c),
    "protocol": "groth16",
    "curve": "bn128",
    });
    let public_json = serde_json::Value::Array(
        public
            .iter()
            .map(|f| serde_json::Value::String(f.to_string()))
            .collect(),
    );

    std::fs::write(
        out.join("vkey.json"),
        serde_json::to_string_pretty(&vkey).unwrap(),
    )
    .unwrap();
    std::fs::write(
        out.join("proof.json"),
        serde_json::to_string_pretty(&proof_json).unwrap(),
    )
    .unwrap();
    std::fs::write(
        out.join("public.json"),
        serde_json::to_string_pretty(&public_json).unwrap(),
    )
    .unwrap();
    eprintln!(
        "wrote {}/{{vkey,proof,public}}.json (nPublic={})",
        out.display(),
        public.len()
    );
}
