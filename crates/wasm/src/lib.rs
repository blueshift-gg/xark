//! WebAssembly bindings for generating xark Groth16 (BN254) proofs.
//!
//! ## What you need (produced offline by the host toolchain)
//!
//! | artifact       | produced by    | passed as                                          |
//! |----------------|----------------|----------------------------------------------------|
//! | `circuit.xbc`  | `xark build`   | `circuit_xbc: Uint8Array` (binary)                 |
//! | `pk.bin`       | `xark setup`   | `pk_bytes: Uint8Array`                             |
//! | witness inputs | (your circuit) | `inputs: { name: value, … }` (a plain JS object; nested OK) |
//!
//! The compile (`xark build`) and setup (`xark setup`) steps require the host
//! rustc driver / ceremony tooling and cannot run in wasm — produce those
//! artifacts on the server, ship them to the client, and prove client-side.
//!
//! `circuit.xbc` is the self-contained binary artifact `xark build` always
//! writes. From it the prover streams both what it needs, as `xark prove` does:
//! the witness (solved by streaming the hint program) and the constraint rows the
//! key was made for (the template-reduced rows straight from the bytecode, or the
//! minimized circuit, rebuilt when the key is in that form). The proving key is
//! read a chunk of points at a time, so neither it nor the constraint system is
//! ever expanded whole.
//!
//! Every artifact — circuit, proving/verifying key, proof, public inputs — is
//! binary. Only the witness inputs (a tiny `name → value` map) stay JSON.
//!
//! ## JS usage (`--target web`)
//!
//! ```js,ignore
//! import init, { prove } from "./dist/web/xark_wasm.js";
//! await init();    // instantiate the module
//!
//! // byte args accept a Uint8Array OR an ArrayBuffer:
//! const xbc        = await (await fetch("/circuit/circuit.xbc")).arrayBuffer();
//! const pkBytes    = await (await fetch("/circuit/pk.bin")).arrayBuffer();
//! const out = prove(xbc, pkBytes, { secret: "3", result: "27" });
//! // => ProofBundle {
//! //   proof:            Uint8Array,
//! //   publicInputs:     Uint8Array,
//! //   numPublicInputs:  number,
//! // }
//!
//! // The public inputs as decimal strings, in proof order:
//! //   decode_public_inputs(out.publicInputs)      // e.g. ["27"]
//! ```
//!
//! ## Security
//!
//! Prover randomness is drawn from the platform CSPRNG (`OsRng`, backed by
//! `crypto.getRandomValues`).

use std::cell::RefCell;
use std::collections::BTreeMap;

use ark_bn254::{Bn254, Fr};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use wasm_bindgen::prelude::*;
use xark_groth16::{Proof, ProvingKey, VerifyingKey};

use xark_ir::VarId;
use xark_prover::{flatten_inputs, resolve_input_ids, InputValue};

mod streaming;
pub use streaming::{
    begin_streaming_proof, kernel_cols, kernel_msm, kernel_rows, preload_streaming,
    prove_streaming, prove_streaming_preloaded, wasm_memory_bytes, StreamingProof,
};

// ---- byte inputs: accept a `Uint8Array` or a raw `ArrayBuffer` -------------

/// The input type for every binary argument (`circuit.xbc`, `pk.bin`, `vk.bin`,
/// a proof, …). Accepting an [`ArrayBuffer`] in addition to a `Uint8Array` lets
/// callers hand the result of fetch response `await response.arrayBuffer()`
/// straight to `prove` / `verify`.
#[wasm_bindgen(typescript_custom_section)]
const BYTES_TS: &str = r#"
/** A binary payload: a `Uint8Array`, or a raw `ArrayBuffer` */
export type Bytes = Uint8Array | ArrayBuffer;
"#;

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(typescript_type = "Bytes")]
    pub type Bytes;
}

// ---- preload: parse the circuit artifacts once, prove many times -------------

thread_local! {
    static ARTIFACTS: RefCell<Option<streaming::Prepared>> = const { RefCell::new(None) };
}

/// Resolve a JS inputs object to `VarId → decimal` for the solver
/// ([`xark_prover::resolve_input_ids`]): leaf names, or nested objects/arrays
/// mirroring the input's shape. Values may be strings (decimal or `0x`-hex), integer
/// numbers, bigints, or booleans; natural forms (dates, bytes, points) go through
/// [`encode_inputs`] first.
fn resolve_inputs(
    vars: &[xark_ir::primitive::Var],
    inputs: JsValue,
) -> Result<BTreeMap<VarId, String>, String> {
    let InputValue::Map(entries) =
        js_to_input(&inputs).map_err(|e| format!("parsing inputs: {e}"))?
    else {
        return Err("inputs must be an object of name → value".into());
    };
    resolve_input_ids(vars, &flatten_inputs(entries))
}

/// A JS value → [`InputValue`]. Numbers must be safe integers (so nothing is silently
/// rounded); pass anything larger as a bigint or a string.
fn js_to_input(v: &JsValue) -> Result<InputValue, String> {
    if let Some(s) = v.as_string() {
        return Ok(InputValue::Scalar(s));
    }
    if v.is_bigint() {
        let s: String = js_sys::BigInt::from(v.clone())
            .to_string(10)
            .map_err(|_| "unprintable bigint".to_string())?
            .into();
        return Ok(InputValue::Scalar(s));
    }
    if let Some(n) = v.as_f64() {
        if !js_sys::Number::is_safe_integer(v) {
            return Err(format!(
                "number {n} is not a safe integer; pass large values as a bigint or string"
            ));
        }
        return Ok(InputValue::Scalar(format!("{}", n as i64)));
    }
    if let Some(b) = v.as_bool() {
        return Ok(InputValue::Scalar(if b { "1" } else { "0" }.into()));
    }
    if js_sys::Array::is_array(v) {
        return js_sys::Array::from(v)
            .iter()
            .map(|x| js_to_input(&x))
            .collect::<Result<_, _>>()
            .map(InputValue::List);
    }
    if let Some(bytes) = v.dyn_ref::<js_sys::Uint8Array>() {
        // A byte array (`[u8; N]` input): one leaf per byte.
        return Ok(InputValue::List(
            bytes
                .to_vec()
                .into_iter()
                .map(|b| InputValue::Scalar(b.to_string()))
                .collect(),
        ));
    }
    if v.is_object() {
        return js_sys::Object::entries(v.unchecked_ref())
            .iter()
            .map(|e| {
                let e = js_sys::Array::from(&e);
                let k = e.get(0).as_string().unwrap_or_default();
                let x = js_to_input(&e.get(1)).map_err(|err| format!("`{k}`: {err}"))?;
                Ok((k, x))
            })
            .collect::<Result<_, String>>()
            .map(InputValue::Map);
    }
    Err(format!("unsupported input value {v:?}"))
}

/// The result of [`prove`] / [`prove_preloaded`]: the canonical compressed
/// proof + public-input bytes (identical to the host's `proof.bin` /
/// `public_inputs.bin`), plus the public-input count.
// `getter_with_clone` only on the byte fields: the count is `Copy`.
#[wasm_bindgen]
pub struct ProofBundle {
    /// Canonical compressed proof bytes (`== proof.bin`).
    #[wasm_bindgen(getter_with_clone)]
    pub proof: Vec<u8>,
    /// Canonical compressed public-input bytes (`== public_inputs.bin`).
    #[wasm_bindgen(getter_with_clone, js_name = publicInputs)]
    pub public_inputs: Vec<u8>,
    /// Number of public inputs.
    #[wasm_bindgen(js_name = numPublicInputs)]
    pub num_public_inputs: usize,
}

fn encode_result(proof: &Proof<Bn254>, public: &[Fr]) -> Result<ProofBundle, js_sys::Error> {
    let mut proof_buf = Vec::new();
    proof
        .serialize_with_mode(&mut proof_buf, Compress::Yes)
        .map_err(|e| js_error(&format!("serializing proof: {e}")))?;
    let mut public_buf = Vec::new();
    public
        .serialize_with_mode(&mut public_buf, Compress::Yes)
        .map_err(|e| js_error(&format!("serializing public inputs: {e}")))?;

    Ok(ProofBundle {
        proof: proof_buf,
        public_inputs: public_buf,
        num_public_inputs: public.len(),
    })
}

/// Parse and cache a circuit's `circuit.xbc` + `pk.bin` once for
/// [`prove_preloaded`]. Call once per circuit; subsequent calls silently
/// replace the cached state.
///
/// `circuit_xbc` is the self-contained binary artifact `xark build` always
/// writes; `pk_bytes` is the `pk.bin` from `xark setup`. The key is decoded once
/// into wasm memory (about 2.2× its compressed size) so repeat proofs skip point
/// decompression; for the largest circuits prefer `preloadStreaming`, which
/// leaves it in its JS buffer. `sources`: as for [`prove`].
#[wasm_bindgen]
pub fn preload(
    circuit_xbc: &Bytes,
    pk_bytes: &Bytes,
    sources: Option<String>,
) -> Result<(), js_sys::Error> {
    let prepared = streaming::prepare_auto(circuit_xbc, pk_bytes, true, sources)?;
    ARTIFACTS.with(|cell| *cell.borrow_mut() = Some(prepared));
    Ok(())
}

/// Prove using the artifacts cached by a prior [`preload`] call — skipping the
/// `.xbc` parse, row-source build and `pk.bin` decode on every call.
///
/// Returns the same shape as [`prove`]. Throws if [`preload`] hasn't been called.
#[wasm_bindgen]
pub fn prove_preloaded(inputs: JsValue) -> Result<ProofBundle, js_sys::Error> {
    ARTIFACTS.with(|cell| -> Result<ProofBundle, js_sys::Error> {
        let mut state = cell.borrow_mut();
        let p = state
            .as_mut()
            .ok_or_else(|| js_error("call preload() first"))?;
        streaming::prove_auto(p, inputs)
    })
}

/// A circuit's `circuit.xbc` and `pk.bin`, parsed and decoded once, for many proofs:
/// what [`preload`] caches, as an object of its own, so each prover keeps its own.
/// The key is decoded into wasm memory (about 2.2× `pk.bin`), so a proof skips the
/// `.xbc` parse, row-source build and point decompression [`prove`] does each time.
/// `sources`: as for [`prove`].
#[wasm_bindgen]
pub struct ProvingSession(streaming::Prepared);

#[wasm_bindgen]
impl ProvingSession {
    #[wasm_bindgen(constructor)]
    pub fn new(
        circuit_xbc: &Bytes,
        pk_bytes: &Bytes,
        sources: Option<String>,
    ) -> Result<ProvingSession, js_sys::Error> {
        streaming::prepare_auto(circuit_xbc, pk_bytes, true, sources).map(ProvingSession)
    }

    /// Prove: the same arguments (bar the artifacts) and result as [`prove`].
    pub fn prove(&mut self, inputs: JsValue) -> Result<ProofBundle, js_sys::Error> {
        streaming::prove_auto(&mut self.0, inputs)
    }
}

/// Generate a Groth16 proof.
///
/// See the crate docs for the shape of each argument and the return object.
/// Every byte argument accepts a `Uint8Array` **or** an `ArrayBuffer` — so the
/// result of `await response.arrayBuffer()` can be passed directly.
///
/// Uses the streaming prover: the key is read from `pk_bytes` a chunk of points
/// at a time and the constraint rows are streamed, so memory stays far below the
/// key and circuit sizes (Ed25519 verification fits). The proof is checked
/// against the key's verifying key before it is returned.
///
/// Throws an `Error` on any error: a malformed `.xbc`, unknown input,
/// an unsatisfiable witness, or a proving key for a different circuit. Pass the
/// build's `sources.json` (text) as `sources` and inputs that fail a check name
/// it: `the inputs fail the check at src/lib.rs:77:20: \`…require_one_of(allowed);\``.
#[wasm_bindgen]
pub fn prove(
    circuit_xbc: &Bytes,
    pk_bytes: &Bytes,
    inputs: JsValue,
    sources: Option<String>,
) -> Result<ProofBundle, js_sys::Error> {
    let mut p = streaming::prepare_auto(circuit_xbc, pk_bytes, false, sources)?;
    streaming::prove_auto(&mut p, inputs)
}

/// Verify a Groth16 proof against its public inputs, in memory.
///
/// Each argument is the canonical compressed binary written by `xark setup` /
/// `xark prove` — `proof` and `public_inputs` are exactly what [`prove`]
/// returns, and `vk_bytes` is the contents of `vk.bin`.
///
/// Returns `true` if the proof is valid for `public_inputs` under `vk_bytes`,
/// `false` if it is well-formed but does not verify. Throws an `Error` on a
/// deserialization error (malformed key / proof / public inputs).
#[wasm_bindgen]
pub fn verify(
    vk_bytes: &Bytes,
    proof_bytes: &Bytes,
    public_inputs_bytes: &Bytes,
) -> Result<bool, js_sys::Error> {
    let vk_bytes = to_bytes(vk_bytes, "verifying key")?;
    let vk = deserialize_bytes::<VerifyingKey<Bn254>>(&vk_bytes, "verifying key")?;
    verify_with(&vk, proof_bytes, public_inputs_bytes)
}

fn verify_with(
    vk: &VerifyingKey<Bn254>,
    proof_bytes: &Bytes,
    public_inputs_bytes: &Bytes,
) -> Result<bool, js_sys::Error> {
    let proof = read_proof(proof_bytes)?;
    let public_inputs_bytes = to_bytes(public_inputs_bytes, "public inputs")?;
    let public: Vec<Fr> = deserialize_bytes(&public_inputs_bytes, "public inputs")?;
    xark_groth16::verify(vk, &public, &proof).map_err(|e| js_error(&format!("verifying: {e}")))
}

/// A proof in either form: the on-chain one (256 bytes, what an exported Solana
/// verifier reads) or the compressed one (128 bytes, as [`prove`] returns it).
fn read_proof(proof_bytes: &Bytes) -> Result<Proof<Bn254>, js_sys::Error> {
    let bytes = to_bytes(proof_bytes, "proof")?;
    if bytes.len() == xark_groth16::solana::PROOF_BYTES {
        return xark_groth16::solana::decode_proof_le(&bytes)
            .map_err(|e| js_error(&format!("reading proof: {e}")));
    }
    deserialize_bytes::<Proof<Bn254>>(&bytes, "proof")
}

/// A proof (either form) in the on-chain format an exported Solana verifier reads:
/// 256 bytes, `-A || B || C`, little-endian. The same bytes as `xark export`'s
/// `proof.solana.bin` for that proof.
#[wasm_bindgen(js_name = solanaProof)]
pub fn solana_proof(proof_bytes: &Bytes) -> Result<Vec<u8>, js_sys::Error> {
    Ok(xark_groth16::solana::assemble_proof_bytes_le(&read_proof(
        proof_bytes,
    )?))
}

/// Lowercase hex SHA-256 of `bytes`: a verifying key's, as `xark setup` prints it, to
/// pin a verifier to (without WebCrypto, which pages served over plain HTTP lack).
#[wasm_bindgen(js_name = sha256Hex)]
pub fn sha256_hex_js(bytes: &Bytes) -> Result<String, js_sys::Error> {
    Ok(sha256_hex(&to_bytes(bytes, "bytes")?))
}

/// The circuit digest of a `circuit.xbc` (what `xark build` prints, and a key's
/// `metadata.json` records): the same for every build of the circuit, whichever Rust
/// compiled it, and different for any other circuit.
#[wasm_bindgen(js_name = circuitDigest)]
pub fn circuit_digest(circuit_xbc: &Bytes) -> Result<String, js_sys::Error> {
    let b = to_bytes(circuit_xbc, "circuit.xbc")?;
    if xark_ir::function_decode::stream_field(&b).is_none() {
        return Err(js_error(
            "not a circuit.xbc written by this xark's `xark build`",
        ));
    }
    Ok(xark_ir::function_decode::stream_digest_hex(&b))
}

/// Decode binary public inputs (the `publicInputs` `Uint8Array` from [`prove`],
/// == `public_inputs.bin`) to decimal strings, in proof order.
#[wasm_bindgen]
pub fn decode_public_inputs(public_inputs_bytes: &Bytes) -> Result<Vec<String>, js_sys::Error> {
    let public_inputs_bytes = to_bytes(public_inputs_bytes, "public inputs")?;
    let public: Vec<Fr> = deserialize_bytes(&public_inputs_bytes, "public inputs")?;
    Ok(public.iter().map(|x| x.to_string()).collect())
}

// ---------------------------------------------------------------------------
// typed inputs (`schema.json`)
// ---------------------------------------------------------------------------

fn schema(text: &str) -> Result<xark_schema::Schema, js_sys::Error> {
    xark_schema::Schema::parse(text).map_err(|e| js_error(&e))
}

fn json(text: &str, what: &str) -> Result<serde_json::Value, js_sys::Error> {
    serde_json::from_str(text).map_err(|e| js_error(&format!("{what}: {e}")))
}

/// A circuit's `schema.json`, parsed once: what a generated client holds to encode
/// and decode values, instead of passing the text to every call.
#[wasm_bindgen(js_name = Schema)]
pub struct JsSchema(xark_schema::Schema);

#[wasm_bindgen(js_class = Schema)]
impl JsSchema {
    /// Parse `schema.json` (text). Throws if it isn't a schema this xark reads.
    #[wasm_bindgen(constructor)]
    pub fn new(schema_json: &str) -> Result<JsSchema, js_sys::Error> {
        Ok(JsSchema(schema(schema_json)?))
    }

    /// As [`encode_inputs`].
    #[wasm_bindgen(js_name = encodeInputs)]
    pub fn encode_inputs(&self, inputs_json: &str) -> Result<JsValue, js_sys::Error> {
        encode_inputs_with(&self.0, inputs_json)
    }

    /// As [`encode_public_inputs`].
    #[wasm_bindgen(js_name = encodePublicInputs)]
    pub fn encode_public_inputs(&self, public_json: &str) -> Result<Vec<u8>, js_sys::Error> {
        encode_public_inputs_with(&self.0, public_json)
    }

    /// As [`decode_public_values`].
    #[wasm_bindgen(js_name = decodePublicValues)]
    pub fn decode_public_values(
        &self,
        public_inputs_bytes: &Bytes,
    ) -> Result<String, js_sys::Error> {
        decode_public_values_with(&self.0, public_inputs_bytes)
    }

    /// As [`value_fields`].
    #[wasm_bindgen(js_name = valueFields)]
    pub fn value_fields(
        &self,
        type_name: &str,
        value_json: &str,
    ) -> Result<Vec<String>, js_sys::Error> {
        value_fields_with(&self.0, type_name, value_json)
    }
}

/// A verifying key (`vk.bin`), decoded once: a malformed key throws here, so that
/// [`VerifyingKey::verify`](JsVerifyingKey::verify) throws only on a malformed proof
/// or public inputs.
#[wasm_bindgen(js_name = VerifyingKey)]
pub struct JsVerifyingKey(VerifyingKey<Bn254>);

#[wasm_bindgen(js_class = VerifyingKey)]
impl JsVerifyingKey {
    #[wasm_bindgen(constructor)]
    pub fn new(vk_bytes: &Bytes) -> Result<JsVerifyingKey, js_sys::Error> {
        let bytes = to_bytes(vk_bytes, "verifying key")?;
        Ok(JsVerifyingKey(deserialize_bytes(&bytes, "verifying key")?))
    }

    /// As [`verify`], with this key.
    pub fn verify(
        &self,
        proof_bytes: &Bytes,
        public_inputs_bytes: &Bytes,
    ) -> Result<bool, js_sys::Error> {
        verify_with(&self.0, proof_bytes, public_inputs_bytes)
    }
}

/// The circuit's inputs (JSON text: an object of every input, each in its natural
/// form, `camelCase` or `snake_case` keys) as the `leaf → decimal` object [`prove`]
/// takes, encoded and checked against `schema` (the circuit's `schema.json` text).
/// A generated client holds a [`Schema`](JsSchema) instead.
#[wasm_bindgen(js_name = encodeInputs)]
pub fn encode_inputs(schema_json: &str, inputs_json: &str) -> Result<JsValue, js_sys::Error> {
    encode_inputs_with(&schema(schema_json)?, inputs_json)
}

fn encode_inputs_with(
    schema: &xark_schema::Schema,
    inputs_json: &str,
) -> Result<JsValue, js_sys::Error> {
    let leaves = schema
        .leaves(&json(inputs_json, "inputs")?)
        .map_err(|e| input_error(&e))?;
    let out = js_sys::Object::new();
    for (k, v) in leaves {
        js_sys::Reflect::set(&out, &k.into(), &v.to_string().into())?;
    }
    Ok(out.into())
}

/// The public inputs (JSON text, as for [`encode_inputs`]; only the public ones
/// needed) as the canonical bytes [`verify`] takes (`public_inputs.bin`).
#[wasm_bindgen(js_name = encodePublicInputs)]
pub fn encode_public_inputs(
    schema_json: &str,
    public_json: &str,
) -> Result<Vec<u8>, js_sys::Error> {
    encode_public_inputs_with(&schema(schema_json)?, public_json)
}

fn encode_public_inputs_with(
    schema: &xark_schema::Schema,
    public_json: &str,
) -> Result<Vec<u8>, js_sys::Error> {
    let values = schema
        .public_inputs(&json(public_json, "public inputs")?)
        .map_err(|e| input_error(&e))?;
    let mut out = Vec::new();
    values
        .serialize_compressed(&mut out)
        .map_err(|e| js_error(&format!("encoding public inputs: {e}")))?;
    Ok(out)
}

/// Canonical public-input bytes decoded to their natural forms: JSON text of an
/// object keyed `camelCase` (a `Date` as `"YYYY-MM-DD"`, flags as their names, bytes
/// as `0x`-hex, field elements as decimal strings).
#[wasm_bindgen(js_name = decodePublicValues)]
pub fn decode_public_values(
    schema_json: &str,
    public_inputs_bytes: &Bytes,
) -> Result<String, js_sys::Error> {
    decode_public_values_with(&schema(schema_json)?, public_inputs_bytes)
}

fn decode_public_values_with(
    schema: &xark_schema::Schema,
    public_inputs_bytes: &Bytes,
) -> Result<String, js_sys::Error> {
    let bytes = to_bytes(public_inputs_bytes, "public inputs")?;
    let values: Vec<Fr> = deserialize_bytes(&bytes, "public inputs")?;
    let v = schema
        .decode_public(&values, true)
        .map_err(|e| js_error(&e))?;
    Ok(v.to_string())
}

/// A value of the input type `typeName` (JSON text, in its natural form) as its
/// field elements, decimal, in input order: what `to_fields()` gives in Rust. Hash
/// them with [`poseidon2`] to compute a commitment the way the circuit does.
#[wasm_bindgen(js_name = valueFields)]
pub fn value_fields(
    schema_json: &str,
    type_name: &str,
    value_json: &str,
) -> Result<Vec<String>, js_sys::Error> {
    value_fields_with(&schema(schema_json)?, type_name, value_json)
}

fn value_fields_with(
    schema: &xark_schema::Schema,
    type_name: &str,
    value_json: &str,
) -> Result<Vec<String>, js_sys::Error> {
    let fields = schema
        .fields(type_name, &json(value_json, "value")?)
        .map_err(|e| input_error(&e))?;
    Ok(fields.iter().map(|f| f.to_string()).collect())
}

/// `xark_poseidon2::hash` of field elements (decimal or `0x`-hex strings, each
/// below the field order), as a decimal string: the value the gadget constrains.
#[wasm_bindgen]
pub fn poseidon2(inputs: Vec<String>) -> Result<String, js_sys::Error> {
    let fields = inputs
        .iter()
        .map(|s| {
            xark_prover::field_input_decimal(s)
                .ok()
                .and_then(|d| <Fr as std::str::FromStr>::from_str(&d).ok())
                .ok_or_else(|| js_error(&format!("{s:?} is not a field element")))
        })
        .collect::<Result<Vec<Fr>, _>>()?;
    Ok(xark_poseidon2::native::hash_slice(&fields).to_string())
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

/// Runs once when the wasm module is instantiated (after `await init()` on the
/// `web` target; on `require`/`import` for node/bundler). Installs the panic
/// hook here so every export gets readable panic messages without each one
/// re-arming it.
#[wasm_bindgen(start)]
pub fn start() {
    console_error_panic_hook::set_once();
}

/// Coerce a [`Bytes`] payload (`Uint8Array` or `ArrayBuffer`) into owned bytes,
/// so callers can pass `await response.arrayBuffer()` straight through without
/// wrapping it in `new Uint8Array(…)`. `what` labels the value in any error.
fn to_bytes(v: &Bytes, what: &'static str) -> Result<Vec<u8>, js_sys::Error> {
    let raw: &JsValue = v.as_ref();
    if let Some(arr) = raw.dyn_ref::<js_sys::Uint8Array>() {
        return Ok(arr.to_vec());
    }
    if let Some(buf) = raw.dyn_ref::<js_sys::ArrayBuffer>() {
        return Ok(js_sys::Uint8Array::new(buf.as_ref()).to_vec());
    }
    Err(js_error(&format!(
        "{what} must be a Uint8Array or ArrayBuffer (e.g. `await response.arrayBuffer()`)"
    )))
}

fn js_error(msg: &str) -> js_sys::Error {
    js_sys::Error::new(msg)
}

/// A refused input value, as an `Error` named `InputError` whose `path` is the input
/// at fault in a JS caller's names (`id.netWorth`; empty for the inputs as a whole).
fn input_error(e: &xark_schema::InputError) -> js_sys::Error {
    let e = e.camel_case();
    let err = js_error(&e.to_string());
    err.set_name("InputError");
    let _ = js_sys::Reflect::set(&err, &"path".into(), &e.path.as_str().into());
    err
}

/// Inputs that fail a check, as an `Error` named `CheckFailed` whose `site` is the
/// statement that emitted it: `{ file, line, col, text, chain }`.
pub(crate) fn check_failed(site: &xark_ir::Site) -> js_sys::Error {
    let err = js_error(&format!("the inputs fail the check at {}", site.describe()));
    err.set_name("CheckFailed");
    let s = js_sys::Object::new();
    let set = |k: &str, v: JsValue| {
        let _ = js_sys::Reflect::set(&s, &k.into(), &v);
    };
    set("file", site.file.as_str().into());
    set("line", site.line.into());
    set("col", site.col.into());
    set("text", site.text.as_str().into());
    let chain: js_sys::Array = site
        .chain
        .iter()
        .map(|f| JsValue::from(f.as_str()))
        .collect();
    set("chain", chain.into());
    let _ = js_sys::Reflect::set(&err, &"site".into(), &s.into());
    err
}

/// Deserialize canonical compressed bytes (the form `xark setup` / `xark prove`
/// write), validating as it parses. `what` labels the value in any error.
fn deserialize_bytes<T: CanonicalDeserialize>(
    bytes: &[u8],
    what: &str,
) -> Result<T, js_sys::Error> {
    T::deserialize_with_mode(bytes, Compress::Yes, Validate::Yes)
        .map_err(|e| js_error(&format!("deserializing {what}: {e}")))
}

/// The `XKPK` header at the start of `bytes` (`xark_groth16::pk::KeyFormat`:
/// point mode, and for v2 keys the QAP domain size). Legacy untagged keys are
/// compressed.
fn key_format(bytes: &[u8]) -> Result<xark_groth16::pk::KeyFormat, js_sys::Error> {
    xark_groth16::pk::KeyFormat::parse(bytes, true)
        .map_err(|e| js_error(&e.to_string()))
        .map(|f| f.expect("parse at EOF always decides"))
}

/// Deserialize a whole `pk.bin` from a reader (honoring its `XKPK` header),
/// unchecked: the key is the caller's own setup
/// output, and every proof is self-verified against its embedded `vk`.
pub(crate) fn deserialize_proving_key_from(
    mut r: impl std::io::Read,
) -> Result<ProvingKey<Bn254>, js_sys::Error> {
    let mut head = [0u8; xark_groth16::pk::MAX_HEADER_LEN];
    r.read_exact(&mut head)
        .map_err(|e| js_error(&format!("reading proving key: {e}")))?;
    let fmt = key_format(&head)?;
    ProvingKey::<Bn254>::deserialize_with_mode(
        std::io::Read::chain(&head[fmt.header_len..], r),
        fmt.compress(),
        Validate::No,
    )
    .map_err(|e| js_error(&format!("deserializing proving key: {e}")))
}

/// Lowercase hex SHA-256 (the `circuit.xbc` fingerprint `xark setup` records).
pub(crate) fn sha256_hex(b: &[u8]) -> String {
    use sha2::Digest;
    sha2::Sha256::digest(b)
        .iter()
        .map(|x| format!("{x:02x}"))
        .collect()
}
