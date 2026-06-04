//! Arkworks canonical (binary) and JSON serialization helpers.

use std::fs;
use std::path::Path;

use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_groth16::{Proof, VerifyingKey};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};

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

// -- JSON ---------------------------------------------------------------------

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct G1Json {
    pub x: String,
    pub y: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct G2Json {
    pub x: [String; 2],
    pub y: [String; 2],
}

fn fq_to_decimal(value: &Fq) -> String {
    let big: BigUint = (*value).into();
    big.to_str_radix(10)
}

fn g1_to_json(p: &G1Affine) -> G1Json {
    if p.is_zero() {
        G1Json {
            x: "0".into(),
            y: "0".into(),
        }
    } else {
        let (x, y) = p.xy().expect("g1 not at infinity");
        G1Json {
            x: fq_to_decimal(&x),
            y: fq_to_decimal(&y),
        }
    }
}

fn g2_to_json(p: &G2Affine) -> G2Json {
    if p.is_zero() {
        G2Json {
            x: ["0".into(), "0".into()],
            y: ["0".into(), "0".into()],
        }
    } else {
        let (x, y) = p.xy().expect("g2 not at infinity");
        let (Fq2 { c0: x0, c1: x1 }, Fq2 { c0: y0, c1: y1 }) = (x, y);
        G2Json {
            x: [fq_to_decimal(&x0), fq_to_decimal(&x1)],
            y: [fq_to_decimal(&y0), fq_to_decimal(&y1)],
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofJson {
    pub curve: String,
    pub protocol: String,
    pub a: G1Json,
    pub b: G2Json,
    pub c: G1Json,
}

impl ProofJson {
    pub fn from_proof(proof: &Proof<Bn254>) -> Self {
        Self {
            curve: "bn254".into(),
            protocol: "groth16".into(),
            a: g1_to_json(&proof.a),
            b: g2_to_json(&proof.b),
            c: g1_to_json(&proof.c),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyingKeyJson {
    pub curve: String,
    pub protocol: String,
    pub alpha_g1: G1Json,
    pub beta_g2: G2Json,
    pub gamma_g2: G2Json,
    pub delta_g2: G2Json,
    pub gamma_abc_g1: Vec<G1Json>,
}

impl VerifyingKeyJson {
    pub fn from_vk(vk: &VerifyingKey<Bn254>) -> Self {
        Self {
            curve: "bn254".into(),
            protocol: "groth16".into(),
            alpha_g1: g1_to_json(&vk.alpha_g1),
            beta_g2: g2_to_json(&vk.beta_g2),
            gamma_g2: g2_to_json(&vk.gamma_g2),
            delta_g2: g2_to_json(&vk.delta_g2),
            gamma_abc_g1: vk.gamma_abc_g1.iter().map(g1_to_json).collect(),
        }
    }
}

// -- Public input JSON --------------------------------------------------------

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PublicInputsJson {
    pub curve: String,
    pub field: String,
    pub encoding: String,
    pub inputs: Vec<String>,
}

impl PublicInputsJson {
    pub fn from_fr(inputs: &[Fr]) -> Self {
        Self {
            curve: "bn254".into(),
            field: "fr".into(),
            encoding: "decimal-string".into(),
            inputs: inputs
                .iter()
                .map(|f| {
                    let big: BigUint = (*f).into();
                    big.to_str_radix(10)
                })
                .collect(),
        }
    }

    pub fn into_fr(&self) -> Result<Vec<Fr>, std::io::Error> {
        if self.encoding != "decimal-string" {
            return Err(std::io::Error::other(format!(
                "unsupported public input encoding `{}`",
                self.encoding
            )));
        }
        let mut out = Vec::with_capacity(self.inputs.len());
        for s in &self.inputs {
            let big: BigUint = s
                .trim()
                .parse()
                .map_err(|e: num_bigint::ParseBigIntError| std::io::Error::other(e.to_string()))?;
            use ark_ff::PrimeField;
            out.push(Fr::from_be_bytes_mod_order(&big.to_bytes_be()));
        }
        Ok(out)
    }
}
