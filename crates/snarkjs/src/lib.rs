//! snarkjs-compatible JSON encodings of a Groth16 (BN254) proof, verifying key,
//! and public inputs.
//!
//! This is the single source of truth for the snarkjs wire shapes, shared by the
//! host toolchain (`xark prove` / `xark setup` via `xark-cli`, and the
//! `to_snarkjs` example) and the wasm bindings (`xark-wasm`).
//!
//! It is a deliberately tiny, wasm-safe leaf crate — pure `arkworks type →
//! serde_json::Value` construction with no `rayon` / `std::time` / `chrono` — so
//! both the host `xark-backend` (which pulls those host-only deps) and
//! `xark-wasm` (which compiles for `wasm32-unknown-unknown` and cannot) can
//! depend on it without duplicating the encodings.

use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_groth16::{Proof, VerifyingKey};
use num_bigint::BigUint;

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

/// snarkjs `proof.json` shape for a Groth16/BN254 proof.
pub fn proof_to_snarkjs(proof: &Proof<Bn254>) -> serde_json::Value {
    serde_json::json!({
        "pi_a": g1_snarkjs(&proof.a),
        "pi_b": g2_snarkjs(&proof.b),
        "pi_c": g1_snarkjs(&proof.c),
        "protocol": "groth16",
        "curve": "bn128",
    })
}

/// snarkjs `verification_key.json` shape for a Groth16/BN254 verifying key.
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

/// snarkjs `public.json` shape — an array of decimal strings, in Groth16
/// public-input order.
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
