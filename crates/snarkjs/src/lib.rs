//! snarkjs-compatible JSON shapes for a Groth16 (BN254) proof, verifying key,
//! and public inputs, as **typed `Serialize` structs**.
//!
//! This is the single source of truth for the snarkjs wire shapes, shared by the
//! host toolchain (`xark prove` / `xark setup` via `xark-cli`, and the
//! `to_snarkjs` example) and the wasm bindings (`xark-wasm`). Returning typed
//! structs (rather than `serde_json::Value`) means each consumer serializes the
//! *same* value its own way and gets a faithful result:
//!
//! * the host does `serde_json::to_string_pretty(&proof_to_snarkjs(...))` → the
//!   exact bytes of snarkjs's `proof.json`, and
//! * `xark-wasm` does `serde_wasm_bindgen::to_value(...)` → a plain JS object
//!   (a `serde_json::Value` would cross the wasm boundary as a JS `Map`, not an
//!   object, so callers would need `.get(...)` instead of property access).
//!
//! It is a deliberately tiny, wasm-safe leaf crate — pure `arkworks type → typed
//! struct` construction with no `rayon` / `std::time` / `chrono` — so both the
//! host `xark-backend` (which pulls those host-only deps) and `xark-wasm` (which
//! compiles for `wasm32-unknown-unknown` and cannot) can depend on it without
//! duplicating the encodings.

use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_groth16::{Proof, VerifyingKey};
use num_bigint::BigUint;
use serde::Serialize;

fn fq_to_decimal(value: &Fq) -> String {
    let big: BigUint = (*value).into();
    big.to_str_radix(10)
}

/// `[x, y, "1"]` — G1 affine point. `["0", "0", "0"]` at infinity.
fn g1_snarkjs(p: &G1Affine) -> [String; 3] {
    if p.is_zero() {
        ["0".to_string(), "0".to_string(), "0".to_string()]
    } else {
        let (x, y) = p.xy().expect("g1 not at infinity");
        [fq_to_decimal(&x), fq_to_decimal(&y), "1".to_string()]
    }
}

/// `[[x0, x1], [y0, y1], ["1", "0"]]` — G2 affine point.
/// Each coordinate is a pair because G2 lives in a field extension.
/// All zeros at infinity.
fn g2_snarkjs(p: &G2Affine) -> [[String; 2]; 3] {
    if p.is_zero() {
        [
            ["0".to_string(), "0".to_string()],
            ["0".to_string(), "0".to_string()],
            ["0".to_string(), "0".to_string()],
        ]
    } else {
        let (x, y) = p.xy().expect("g2 not at infinity");
        let (Fq2 { c0: x0, c1: x1 }, Fq2 { c0: y0, c1: y1 }) = (x, y);
        [
            [fq_to_decimal(&x0), fq_to_decimal(&x1)],
            [fq_to_decimal(&y0), fq_to_decimal(&y1)],
            ["1".to_string(), "0".to_string()],
        ]
    }
}

/// snarkjs `proof.json` shape for a Groth16/BN254 proof.
///
/// Field order is the snarkjs wire order, so `serde_json::to_string_pretty`
/// reproduces snarkjs's `proof.json` byte-for-byte.
#[derive(Serialize)]
pub struct SnarkjsProof {
    pub pi_a: [String; 3],
    pub pi_b: [[String; 2]; 3],
    pub pi_c: [String; 3],
    pub protocol: &'static str,
    pub curve: &'static str,
}

/// Build the snarkjs `proof.json` object for a Groth16/BN254 proof.
pub fn proof_to_snarkjs(proof: &Proof<Bn254>) -> SnarkjsProof {
    SnarkjsProof {
        pi_a: g1_snarkjs(&proof.a),
        pi_b: g2_snarkjs(&proof.b),
        pi_c: g1_snarkjs(&proof.c),
        protocol: "groth16",
        curve: "bn128",
    }
}

/// snarkjs `verification_key.json` shape for a Groth16/BN254 verifying key.
///
/// `nPublic` and `IC` keep their snarkjs camel/upper-case spellings via
/// `#[serde(rename = ...)]`; the rest already match the wire keys.
#[derive(Serialize)]
pub struct SnarkjsVerifyingKey {
    pub protocol: &'static str,
    pub curve: &'static str,
    #[serde(rename = "nPublic")]
    pub n_public: usize,
    pub vk_alpha_1: [String; 3],
    pub vk_beta_2: [[String; 2]; 3],
    pub vk_gamma_2: [[String; 2]; 3],
    pub vk_delta_2: [[String; 2]; 3],
    #[serde(rename = "IC")]
    pub ic: Vec<[String; 3]>,
}

/// Build the snarkjs `verification_key.json` object for a Groth16/BN254
/// verifying key. `n_public` is the number of public inputs (snarkjs's
/// `nPublic`), i.e. `vk.gamma_abc_g1.len() - 1`.
pub fn vk_to_snarkjs(
    vk: &VerifyingKey<Bn254>,
    n_public: usize,
) -> SnarkjsVerifyingKey {
    SnarkjsVerifyingKey {
        protocol: "groth16",
        curve: "bn128",
        n_public,
        vk_alpha_1: g1_snarkjs(&vk.alpha_g1),
        vk_beta_2: g2_snarkjs(&vk.beta_g2),
        vk_gamma_2: g2_snarkjs(&vk.gamma_g2),
        vk_delta_2: g2_snarkjs(&vk.delta_g2),
        ic: vk.gamma_abc_g1.iter().map(g1_snarkjs).collect(),
    }
}

/// snarkjs `public.json` shape — an array of decimal strings, in Groth16
/// public-input order.
pub fn public_inputs_to_snarkjs(inputs: &[Fr]) -> Vec<String> {
    inputs
        .iter()
        .map(|f| {
            let big: BigUint = (*f).into();
            big.to_str_radix(10)
        })
        .collect()
}
