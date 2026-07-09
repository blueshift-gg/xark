//! WebAssembly bindings for generating xark Groth16 (BN254) proofs.
//!
//! This is the browser/Node entry point for the *proving* half of the xark
//! toolchain. It mirrors what `xark prove` does on the host — but with no
//! filesystem: every artifact is passed in over the JS boundary.
//!
//! ## What you need (produced offline by the host toolchain)
//!
//! | artifact       | produced by    | passed as                                     |
//! |----------------|----------------|-----------------------------------------------|
//! | `r1cs.json`    | `xark build`   | `r1cs_json: string`                           |
//! | `circuit.json` | `xark build`   | `circuit_json: string`                        |
//! | `pk.bin`       | `xark setup`   | `pk_bytes: Uint8Array`                        |
//! | witness inputs | (your circuit) | `inputs_json: string` (`{"name":"value", …}`) |
//!
//! The compile (`xark build`) and setup (`xark setup`) steps require the host
//! rustc driver / ceremony tooling and cannot run in wasm — produce those
//! artifacts on the server, ship them to the client, and prove client-side.
//!
//! ## JS usage (`--target web`)
//!
//! ```js,ignore
//! import init, { prove } from "./pkg/xark_wasm.js";
//! await init();    // instantiate the module
//!
//! const r1csJson   = await (await fetch("/circuit/r1cs.json")).text();
//! const circuitJson= await (await fetch("/circuit/circuit.json")).text();
//! const pkBytes    = new Uint8Array(await (await fetch("/circuit/pk.bin")).arrayBuffer());
//! const inputsJson = JSON.stringify({ secret: "3", result: "27" });
//!
//! const out = prove(r1csJson, circuitJson, pkBytes, inputsJson);
//! // => {
//! //   proof:            Uint8Array,   // canonical compressed bytes (== proof.bin)
//! //   publicInputs:     Uint8Array,   // canonical compressed bytes (== public_inputs.bin)
//! //   snarkjsProof:     string,       // == snarkjs-proof.json
//! //   snarkjsPublic:    string,       // == snarkjs-public.json
//! //   numPublicInputs:  number,
//! // }
//! ```
//!
//! ## Security
//!
//! Prover randomness is drawn from the platform CSPRNG (`OsRng`, backed by
//! `crypto.getRandomValues`) — the same source the host `xark prove`
//! production path uses. There is **no**
//! deterministic-RNG escape hatch here on purpose: reproducible prover
//! randomness breaks zero-knowledge.

#![allow(clippy::needless_borrow)]

use std::cell::RefCell;
use std::collections::BTreeMap;

use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_groth16::{Groth16, Proof, ProvingKey, VerifyingKey};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use ark_snark::SNARK;
use num_bigint::BigUint;
use wasm_bindgen::prelude::*;

use xark_ir::primitive::{self, PrimitiveProgram, VarRole};
use xark_ir::{json as ir_json, solver, VarId};
use xark_prover::{fr_from_decimal, try_fr_from_decimal, XarkCircuit};

// ---- preload: parse the heavy artifacts once, prove many times -------------

struct PreState {
    prog: xark_ir::R1csProgram,
    prim: PrimitiveProgram,
    by_name: BTreeMap<String, VarId>,
    pk: ProvingKey<Bn254>,
}

thread_local! {
    static PRESTATE: RefCell<Option<PreState>> = RefCell::new(None);
}

/// Parse a circuit's `r1cs.json` + `circuit.json` + `pk.bin` once so
/// subsequent calls to [`prove_fast`] skip all heavy deserialization.
/// Call once per circuit; subsequent calls silently replace the cached state.
#[wasm_bindgen]
pub fn preload(r1cs_json: &str, circuit_json: &str, pk_bytes: &[u8]) -> Result<(), JsValue> {
    console_error_panic_hook::set_once();
    let prog = ir_json::from_json(r1cs_json)
        .map_err(|e| js(&format!("parsing r1cs.json: {e}")))?;
    let prim = primitive::from_json(circuit_json)
        .map_err(|e| js(&format!("parsing circuit.json: {e}")))?;
    let by_name: BTreeMap<String, VarId> = prim
        .vars
        .iter()
        .map(|v| (v.name.clone(), v.id))
        .collect();
    let pk = ProvingKey::<Bn254>::deserialize_with_mode(pk_bytes, Compress::Yes, Validate::Yes)
        .map_err(|e| js(&format!("deserializing proving key: {e}")))?;
    PRESTATE.with(|cell| {
        *cell.borrow_mut() = Some(PreState { prog, prim, by_name, pk });
    });
    Ok(())
}

/// Like [`prove`], but uses the parsed artifacts cached by a prior [`preload`]
/// call — skipping the ~7 MB JSON + 537 KB pk.bin deserialization on every cell.
///
/// Returns the same shape as [`prove`]. Throws if [`preload`] hasn't been
/// called for this circuit.
#[wasm_bindgen]
pub fn prove_fast(inputs_json: &str) -> Result<JsValue, JsValue> {
    console_error_panic_hook::set_once();

    // Take ownership of the pre-loaded state (clone on the way out so
    // subsequent calls can still use it).
    let (prog, prim, by_name, pk) = PRESTATE.with(|cell| {
        let state = cell.borrow();
        let s = state.as_ref().ok_or_else(|| js("call preload() first"))?;
        Ok::<_, JsValue>((s.prog.clone(), s.prim.clone(), s.by_name.clone(), s.pk.clone()))
    })?;

    // Parse inputs (small — only ~87 key-value pairs).
    let inputs: BTreeMap<String, String> = serde_json::from_str(inputs_json)
        .map_err(|e| js(&format!("parsing inputs JSON: {e}")))?;
    let mut id_inputs: BTreeMap<VarId, String> = BTreeMap::new();
    for (k, v) in &inputs {
        let id = *by_name
            .get(k.as_str())
            .ok_or_else(|| js(&format!("unknown input `{k}`")))?;
        try_fr_from_decimal(v)
            .map_err(|e| js(&format!("invalid value for input `{k}`: {e}")))?;
        id_inputs.insert(id, v.clone());
    }

    // Solve the witness and lower field-prime values → arkworks `Fr`.
    let assign_fp = solver::solve_and_check(&prim, &id_inputs)
        .map_err(|e| js(&format!("witness does not satisfy the circuit: {e:?}")))?;
    let assign: BTreeMap<VarId, Fr> = assign_fp
        .iter()
        .map(|(k, v)| (*k, fr_from_decimal(&v.to_decimal())))
        .collect();

    let circuit = XarkCircuit::for_proving(prog, assign);
    circuit
        .validate()
        .map_err(|e| js(&format!("malformed circuit: {e}")))?;
    let public = circuit.public_inputs();

    let mut rng = rand::rngs::OsRng;
    let proof = Groth16::<Bn254>::prove(&pk, circuit, &mut rng)
        .map_err(|e| js(&format!("proving: {e}")))?;

    // Self-check.
    let ok = Groth16::<Bn254>::verify(&pk.vk, &public, &proof)
        .map_err(|e| js(&format!("self-verify: {e}")))?;
    if !ok {
        return Err(js("proof did not self-verify (witness does not satisfy the circuit)"));
    }

    let mut proof_buf = Vec::new();
    proof
        .serialize_with_mode(&mut proof_buf, Compress::Yes)
        .map_err(|e| js(&format!("serializing proof: {e}")))?;
    let mut public_buf = Vec::new();
    public
        .serialize_with_mode(&mut public_buf, Compress::Yes)
        .map_err(|e| js(&format!("serializing public inputs: {e}")))?;
    let snarkjs_proof = serde_json::to_string_pretty(&proof_to_snarkjs(&proof))
        .map_err(|e| js(&format!("encoding snarkjs proof: {e}")))?;
    let snarkjs_public = serde_json::to_string_pretty(&public_inputs_to_snarkjs(&public))
        .map_err(|e| js(&format!("encoding snarkjs public inputs: {e}")))?;

    let obj = js_sys::Object::new();
    set(&obj, "proof", &js_sys::Uint8Array::from(&proof_buf[..]))?;
    set(
        &obj,
        "publicInputs",
        &js_sys::Uint8Array::from(&public_buf[..]),
    )?;
    set(&obj, "snarkjsProof", &JsValue::from_str(&snarkjs_proof))?;
    set(&obj, "snarkjsPublic", &JsValue::from_str(&snarkjs_public))?;
    set(
        &obj,
        "numPublicInputs",
        &JsValue::from_f64(public.len() as f64),
    )?;
    Ok(obj.into())
}
///
/// See the crate docs for the shape of each argument and the return object.
/// Throws a `JsValue` (string) on any error: bad JSON, unknown input, an
/// unsatisfiable witness, a malformed proving key, or a proof that fails to
/// self-verify.
#[wasm_bindgen]
pub fn prove(
    r1cs_json: &str,
    circuit_json: &str,
    pk_bytes: &[u8],
    inputs_json: &str,
) -> Result<JsValue, JsValue> {
    console_error_panic_hook::set_once();

    // 1. Parse the compiled artifacts (produced by `xark build`).
    let prog = ir_json::from_json(r1cs_json)
        .map_err(|e| js(&format!("parsing r1cs.json: {e}")))?;
    let prim = primitive::from_json(circuit_json)
        .map_err(|e| js(&format!("parsing circuit.json: {e}")))?;

    // 2. Parse inputs (`{"name":"value", …}`) and resolve names → variable ids.
    let inputs: BTreeMap<String, String> = serde_json::from_str(inputs_json)
        .map_err(|e| js(&format!("parsing inputs JSON (expect object name→value): {e}")))?;
    let by_name: BTreeMap<&str, VarId> =
        prim.vars.iter().map(|v| (v.name.as_str(), v.id)).collect();
    let mut id_inputs: BTreeMap<VarId, String> = BTreeMap::new();
    for (k, v) in &inputs {
        let &id = by_name
            .get(k.as_str())
            .ok_or_else(|| js(&format!("unknown input `{k}`")))?;
        // strict decimal validation (mirrors `xark prove`): a malformed value
        // is a clean error, not a silently-zeroed witness.
        try_fr_from_decimal(v)
            .map_err(|e| js(&format!("invalid value for input `{k}`: {e}")))?;
        id_inputs.insert(id, v.clone());
    }

    // 3. Solve the witness and lower field-prime values → arkworks `Fr`.
    let assign_fp = solver::solve_and_check(&prim, &id_inputs)
        .map_err(|e| js(&format!("witness does not satisfy the circuit: {e:?}")))?;
    let assign: BTreeMap<VarId, Fr> = assign_fp
        .iter()
        .map(|(k, v)| (*k, fr_from_decimal(&v.to_decimal())))
        .collect();

    // 4. Build the synthesizable circuit + pre-flight validation of constants.
    let circuit = XarkCircuit::for_proving(prog, assign);
    circuit.validate().map_err(|e| js(&format!("malformed circuit: {e}")))?;
    let public = circuit.public_inputs();

    // 5. Read the proving key (canonical compressed bytes, exactly what
    //    `xark setup` writes to `pk.bin`).
    let pk = ProvingKey::<Bn254>::deserialize_with_mode(pk_bytes, Compress::Yes, Validate::Yes)
        .map_err(|e| js(&format!("deserializing proving key: {e}")))?;

    // 6. Prove. Prover randomness comes straight from the platform CSPRNG
    //    (`OsRng`), exactly as the host `xark prove` production path does —
    //    no DRBG, no deterministic option (reproducible randomness breaks ZK).
    let mut rng = rand::rngs::OsRng;
    let proof = Groth16::<Bn254>::prove(&pk, circuit, &mut rng)
        .map_err(|e| js(&format!("proving: {e}")))?;

    // 7. Self-check (matches `xark_backend::prove`): a proof for an
    //    unsatisfying assignment would otherwise only fail downstream at
    //    verify time. A handful of pairings — negligible next to proving.
    let ok = Groth16::<Bn254>::verify(&pk.vk, &public, &proof)
        .map_err(|e| js(&format!("self-verify: {e}")))?;
    if !ok {
        return Err(js("proof did not self-verify (witness does not satisfy the circuit)"));
    }

    // 8. Serialize: canonical binary (== the .bin files `xark prove` writes)
    //    and snarkjs-compatible JSON (== the snarkjs-*.json files).
    let mut proof_buf = Vec::new();
    proof
        .serialize_with_mode(&mut proof_buf, Compress::Yes)
        .map_err(|e| js(&format!("serializing proof: {e}")))?;
    let mut public_buf = Vec::new();
    public
        .serialize_with_mode(&mut public_buf, Compress::Yes)
        .map_err(|e| js(&format!("serializing public inputs: {e}")))?;
    let snarkjs_proof = serde_json::to_string_pretty(&proof_to_snarkjs(&proof))
        .map_err(|e| js(&format!("encoding snarkjs proof: {e}")))?;
    let snarkjs_public = serde_json::to_string_pretty(&public_inputs_to_snarkjs(&public))
        .map_err(|e| js(&format!("encoding snarkjs public inputs: {e}")))?;

    // 9. Assemble the return object.
    let obj = js_sys::Object::new();
    set(&obj, "proof", &js_sys::Uint8Array::from(&proof_buf[..]))?;
    set(&obj, "publicInputs", &js_sys::Uint8Array::from(&public_buf[..]))?;
    set(&obj, "snarkjsProof", &JsValue::from_str(&snarkjs_proof))?;
    set(&obj, "snarkjsPublic", &JsValue::from_str(&snarkjs_public))?;
    set(&obj, "numPublicInputs", &JsValue::from_f64(public.len() as f64))?;
    Ok(obj.into())
}

/// Verify a Groth16 proof against its public inputs, in memory.
///
/// Mirrors the host `xark verify` (the `public_inputs.bin` path): each argument
/// is the canonical compressed binary written by `xark setup` / `xark prove` —
/// `proof` and `public_inputs` are exactly what [`prove`] returns, and
/// `vk_bytes` is the contents of `vk.bin`.
///
/// Returns `true` if the proof is valid for `public_inputs` under `vk_bytes`,
/// `false` if it is well-formed but does not verify. Throws a string on a
/// deserialization error (malformed key / proof / public inputs).
#[wasm_bindgen]
pub fn verify(
    vk_bytes: &[u8],
    proof_bytes: &[u8],
    public_inputs_bytes: &[u8],
) -> Result<bool, JsValue> {
    console_error_panic_hook::set_once();
    let vk = VerifyingKey::<Bn254>::deserialize_with_mode(vk_bytes, Compress::Yes, Validate::Yes)
        .map_err(|e| js(&format!("deserializing verifying key: {e}")))?;
    let proof = Proof::<Bn254>::deserialize_with_mode(proof_bytes, Compress::Yes, Validate::Yes)
        .map_err(|e| js(&format!("deserializing proof: {e}")))?;
    let public: Vec<Fr> =
        Vec::<Fr>::deserialize_with_mode(public_inputs_bytes, Compress::Yes, Validate::Yes)
            .map_err(|e| js(&format!("deserializing public inputs: {e}")))?;
    Groth16::<Bn254>::verify(&vk, &public, &proof).map_err(|e| js(&format!("verifying: {e}")))
}

/// List a circuit's declared inputs (the values `prove`'s `inputs_json` must
/// supply) as a JSON string: `[{"name":"…","role":"public"|"private"}, …]` in
/// declaration (variable-id) order. Convenience for the JS caller.
#[wasm_bindgen]
pub fn circuit_inputs(circuit_json: &str) -> Result<String, JsValue> {
    console_error_panic_hook::set_once();
    let prim: PrimitiveProgram = primitive::from_json(circuit_json)
        .map_err(|e| js(&format!("parsing circuit.json: {e}")))?;
    let mut vars: Vec<&xark_ir::primitive::Var> = prim
        .vars
        .iter()
        .filter(|v| matches!(v.role, VarRole::PublicInput | VarRole::PrivateInput))
        .collect();
    vars.sort_by_key(|v| v.id);
    let out: Vec<serde_json::Value> = vars
        .iter()
        .map(|v| {
            serde_json::json!({
                "name": v.name,
                "role": match v.role {
                    VarRole::PublicInput => "public",
                    VarRole::PrivateInput => "private",
                    _ => "other",
                },
            })
        })
        .collect();
    serde_json::to_string(&out).map_err(|e| js(&format!("encoding inputs: {e}")))
}

/// xark-wasm package version.
#[wasm_bindgen]
pub fn version() -> String {
    env!("CARGO_PKG_VERSION").to_string()
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn js(msg: &str) -> JsValue {
    JsValue::from_str(msg)
}

fn set(obj: &js_sys::Object, key: &str, val: &JsValue) -> Result<(), JsValue> {
    js_sys::Reflect::set(obj.as_ref(), &JsValue::from_str(key), val).map(|_| ())
}

// ---------------------------------------------------------------------------
// snarkjs-compatible serialization (mirrored from `xark_backend::serialization`
// so we don't pull `xark-backend` — and its `parallel`/rayon + `chrono` deps —
// into the wasm build graph). Keep in sync if that module changes.
// ---------------------------------------------------------------------------

fn fq_to_decimal(value: &Fq) -> String {
    let big: BigUint = (*value).into();
    big.to_str_radix(10)
}

/// `[x, y, "1"]` — G1 affine point. `["0","0","0"]` at infinity.
fn g1_snarkjs(p: &G1Affine) -> serde_json::Value {
    if p.is_zero() {
        serde_json::json!(["0", "0", "0"])
    } else {
        let (x, y) = p.xy().expect("g1 not at infinity");
        serde_json::json!([fq_to_decimal(&x), fq_to_decimal(&y), "1"])
    }
}

/// `[[x0,x1],[y0,y1],["1","0"]]` — G2 affine point. All zeros at infinity.
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

fn proof_to_snarkjs(proof: &Proof<Bn254>) -> serde_json::Value {
    serde_json::json!({
        "pi_a": g1_snarkjs(&proof.a),
        "pi_b": g2_snarkjs(&proof.b),
        "pi_c": g1_snarkjs(&proof.c),
        "protocol": "groth16",
        "curve": "bn128",
    })
}

fn public_inputs_to_snarkjs(inputs: &[Fr]) -> serde_json::Value {
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
