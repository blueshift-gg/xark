//! Convert an xark/arkworks Groth16 fixture (verifying_key.bin, proof.bin,
//! public_inputs.bin) into snarkjs's JSON formats so an *independent*
//! implementation can verify our proofs:
//!
//! cargo run -p xark-backend --example to_snarkjs -- <fixture_dir> <out_dir>
//! snarkjs groth16 verify <out>/vkey.json <out>/public.json <out>/proof.json
//!
//! snarkjs's verifier (different language, different library) checking our
//! arkworks-produced proof validates both our proof encoding and the Groth16
//! verification equation against a fully separate stack.

use std::path::Path;

use ark_bn254::Bn254;
use ark_groth16::VerifyingKey;

use xark_backend::keys::Groth16Keys;
use xark_backend::proof::ProofBundle;
use xark_backend::serialization::{
    proof_to_snarkjs, public_inputs_to_snarkjs, read_public_inputs, vk_to_snarkjs,
};

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
    let public = read_public_inputs(&dir.join("public_inputs.bin")).expect("read public inputs");

    let vkey = vk_to_snarkjs(&vk, public.len());
    let proof_json = proof_to_snarkjs(&proof);
    let public_json = public_inputs_to_snarkjs(&public);

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
