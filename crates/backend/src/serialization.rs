//! Arkworks canonical (binary) and JSON serialization helpers.

use std::fs;
use std::path::Path;

use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_groth16::{Proof, VerifyingKey};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use num_bigint::BigUint;

pub fn canonical_write_to_file<T: CanonicalSerialize>(
    value: &T,
    path: &Path,
) -> std::io::Result<()> {
    let mut buf = Vec::with_capacity(value.serialized_size(Compress::Yes));
    value
        .serialize_with_mode(&mut buf, Compress::Yes)
        .map_err(|e| std::io::Error::other(e.to_string()))?;
    fs::write(path, buf)
}

pub fn canonical_read_from_file<T: CanonicalDeserialize>(path: &Path) -> std::io::Result<T> {
    let bytes = fs::read(path)?;
    T::deserialize_with_mode(bytes.as_slice(), Compress::Yes, Validate::Yes)
        .map_err(|e| std::io::Error::other(e.to_string()))
}

// -- snarkjs-compatible JSON --------------------------------------------------

fn fq_to_decimal(value: &Fq) -> String {
    let big: BigUint = (*value).into();
    big.to_str_radix(10)
}

/// `[x, y, "1"]` — G1 affine point. `["0", "0", "0"]` at infinity.
fn g1_snarkjs(p: &G1Affine) -> serde_json::Value {
    if p.is_zero() {
        serde_json::json!(["0", "0", "0"])
    } else {
        let (x, y) = p.xy().expect("g1 not at infinity");
        serde_json::json!([fq_to_decimal(&x), fq_to_decimal(&y), "1"])
    }
}

/// `[[x0, x1], [y0, y1], ["1", "0"]]` — G2 affine point.
/// Each coordinate is a pair because G2 lives in a field extension.
/// All zeros at infinity.
fn g2_snarkjs(p: &G2Affine) -> serde_json::Value {
    if p.is_zero() {
        serde_json::json!([["0", "0"], ["0", "0"], ["0", "0"]])
    } else {
        let (x, y) = p.xy().expect("g2 not at infinity");
        let (Fq2 { c0: x0, c1: x1 }, Fq2 { c0: y0, c1: y1 }) = (x, y);
        serde_json::json!([
            [fq_to_decimal(&x0), fq_to_decimal(&x1)],
            [fq_to_decimal(&y0), fq_to_decimal(&y1)],
            ["1", "0"],
        ])
    }
}

pub fn proof_to_snarkjs(proof: &Proof<Bn254>) -> serde_json::Value {
    serde_json::json!({
        "pi_a": g1_snarkjs(&proof.a),
        "pi_b": g2_snarkjs(&proof.b),
        "pi_c": g1_snarkjs(&proof.c),
        "protocol": "groth16",
        "curve": "bn128",
    })
}

pub fn vk_to_snarkjs(vk: &VerifyingKey<Bn254>, n_public: usize) -> serde_json::Value {
    serde_json::json!({
        "protocol": "groth16",
        "curve": "bn128",
        "nPublic": n_public,
        "vk_alpha_1": g1_snarkjs(&vk.alpha_g1),
        "vk_beta_2": g2_snarkjs(&vk.beta_g2),
        "vk_gamma_2": g2_snarkjs(&vk.gamma_g2),
        "vk_delta_2": g2_snarkjs(&vk.delta_g2),
        "IC": vk.gamma_abc_g1.iter().map(g1_snarkjs).collect::<Vec<_>>(),
    })
}

pub fn public_inputs_to_snarkjs(inputs: &[Fr]) -> serde_json::Value {
    serde_json::Value::Array(
        inputs
            .iter()
            .map(|f| {
                let big: BigUint = (*f).into();
                serde_json::Value::String(big.to_str_radix(10))
            })
            .collect(),
    )
}

// -- Public input binary ------------------------------------------------------

/// Read public inputs from canonical binary.
pub fn read_public_inputs(path: &Path) -> std::io::Result<Vec<Fr>> {
    canonical_read_from_file(path)
}

/// Write public inputs as canonical binary.
pub fn write_public_inputs(inputs: &[Fr], path: &Path) -> std::io::Result<()> {
    canonical_write_to_file(&inputs.to_vec(), path)
}
