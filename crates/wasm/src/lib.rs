//! WebAssembly bindings for generating xark Groth16 (BN254) proofs.
//!
//! ## What you need (produced offline by the host toolchain)
//!
//! | artifact       | produced by    | passed as                                          |
//! |----------------|----------------|----------------------------------------------------|
//! | `circuit.xbc`  | `xark build`   | `circuit_xbc: Uint8Array` (binary)                 |
//! | `pk.bin`       | `xark setup`   | `pk_bytes: Uint8Array`                             |
//! | witness inputs | (your circuit) | `inputs: { name: "value", … }` (a plain JS object) |
//!
//! The compile (`xark build`) and setup (`xark setup`) steps require the host
//! rustc driver / ceremony tooling and cannot run in wasm — produce those
//! artifacts on the server, ship them to the client, and prove client-side.
//!
//! `circuit.xbc` is the self-contained binary artifact `xark build` always
//! writes. From it we derive *both* views the prover needs, exactly as `xark
//! prove` does:
//!
//! * [`expand_function_blob_reduced`] → the **minimized R1CS** the proving key
//!   was generated from (the key from `xark setup` is keyed to this circuit).
//! * [`expand_function_blob`] → the full circuit **with its witness-generation
//!   program**, used to solve the witness. (The reduced variant leaves witness
//!   generation empty by design, so it cannot solve.)
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
//! // snarkjs-compatible objects are opt-in (most callers only need the bytes):
//! //   proof_to_snarkjs(out.proof)                 // == snarkjs-proof.json
//! //   public_inputs_to_snarkjs(out.publicInputs)  // == snarkjs-public.json
//! ```
//!
//! ## Security
//!
//! Prover randomness is drawn from the platform CSPRNG (`OsRng`, backed by
//! `crypto.getRandomValues`).

use std::cell::RefCell;
use std::collections::BTreeMap;

use ark_bn254::{Bn254, Fr};
use ark_groth16::{Groth16, Proof, ProvingKey, VerifyingKey};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use ark_snark::SNARK;
use wasm_bindgen::prelude::*;

use xark_ir::function_decode::{expand_function_blob, expand_function_blob_reduced};
use xark_ir::solver;
use xark_ir::{CircuitProgram, R1csProgram, VarId};
use xark_prover::{lower_witness, try_fr_from_decimal, XarkCircuit};
use xark_snarkjs::{proof_to_snarkjs as snarkjs_proof, public_inputs_to_snarkjs as snarkjs_public};

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

struct PreparedArtifacts {
    /// Full circuit (witness-gen intact) — solved on every [`prove_preloaded`] call.
    circuit: CircuitProgram,
    /// The **minimized** R1CS the proving key is keyed to — already run
    /// through the boundary minimize in [`preload`] (identically to how `xark
    /// setup` keyed the pk), so [`prove_preloaded`] can prove against it directly
    /// without re-minimizing on every call.
    r1cs: R1csProgram,
    by_name: BTreeMap<String, VarId>,
    pk: ProvingKey<Bn254>,
}

thread_local! {
    static ARTIFACTS: RefCell<Option<PreparedArtifacts>> = const { RefCell::new(None) };
}

/// Resolve a `name → value` JS object to `VarId → decimal` for the solver,
/// validating each value as a field element (mirrors `xark prove --inputs`).
/// `by_name` is the circuit's `name → VarId` map (built once in [`preload`]).
fn resolve_inputs(
    by_name: &BTreeMap<String, VarId>,
    inputs: JsValue,
) -> Result<BTreeMap<VarId, String>, String> {
    let inputs: BTreeMap<String, String> = serde_wasm_bindgen::from_value(inputs)
        .map_err(|e| format!("parsing inputs (expect object name→value): {e}"))?;

    let mut id_inputs: BTreeMap<VarId, String> = BTreeMap::new();

    for (k, v) in &inputs {
        let &id = by_name
            .get(k)
            .ok_or_else(|| format!("unknown input `{k}`"))?;
        try_fr_from_decimal(v).map_err(|e| format!("invalid value for input `{k}`: {e}"))?;
        id_inputs.insert(id, v.clone());
    }

    Ok(id_inputs)
}

/// Generates proof with already-expanded circuit views + the proving key.
/// `r1cs` must be the **pre-minimized** backend R1CS the pk is keyed to.
fn prove_with(
    circuit: &CircuitProgram,
    r1cs: &R1csProgram,
    pk: &ProvingKey<Bn254>,
    id_inputs: &BTreeMap<VarId, String>,
) -> Result<ProofBundle, js_sys::Error> {
    let assign_fp = solver::solve_and_check_cp(circuit, id_inputs)
        .map_err(|e| js_error(&format!("witness does not satisfy the circuit: {e:?}")))?;
    let assign = lower_witness(&assign_fp);

    let instance = XarkCircuit::for_proving_preminimized(r1cs.clone(), assign);
    instance
        .validate()
        .map_err(|e| js_error(&format!("malformed circuit: {e}")))?;
    let public = instance.public_inputs();

    let mut rng = rand::rngs::OsRng;
    let proof = Groth16::<Bn254>::prove(pk, instance, &mut rng)
        .map_err(|e| js_error(&format!("proving: {e}")))?;

    encode_result(&proof, &public)
}

/// The result of [`prove`] / [`prove_preloaded`]: the canonical compressed
/// proof + public-input bytes (identical to the host's `proof.bin` /
/// `public_inputs.bin`), plus the public-input count.
#[wasm_bindgen(getter_with_clone)]
pub struct ProofBundle {
    /// Canonical compressed proof bytes (`== proof.bin`).
    pub proof: Vec<u8>,
    /// Canonical compressed public-input bytes (`== public_inputs.bin`).
    #[wasm_bindgen(js_name = publicInputs)]
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

/// Load + prepare every artifact from the raw bytes: expand the two `.xbc`
/// views, build the `name → VarId` map, minimize the backend R1CS the pk is
/// keyed to, and deserialize the proving key.
fn load_artifacts(circuit_xbc: &[u8], pk_bytes: &[u8]) -> Result<PreparedArtifacts, js_sys::Error> {
    // Full circuit (with witness-gen) for the solver.
    let circuit = expand_function_blob(circuit_xbc)
        .map_err(|e| js_error(&format!("parsing circuit.xbc: {e}")))?;

    // The proving key is tied to a specific R1CS form. Reproducing it mirrors
    // `xark setup` in two steps — the reduced expand, then `for_setup`.
    let reduced = expand_function_blob_reduced(circuit_xbc)
        .map_err(|e| js_error(&format!("parsing circuit.xbc: {e}")))?
        .into_r1cs();

    let by_name: BTreeMap<String, VarId> = circuit
        .vars
        .iter()
        .map(|v| (v.name.clone(), v.id))
        .collect();
    let r1cs = XarkCircuit::for_setup(reduced).prog().clone();
    let pk = deserialize_bytes::<ProvingKey<Bn254>>(pk_bytes, "proving key")?;

    Ok(PreparedArtifacts {
        circuit,
        r1cs,
        by_name,
        pk,
    })
}

/// Parse and cache a circuit's `circuit.xbc` + `pk.bin` once for
/// [`prove_preloaded`]. Call once per circuit; subsequent calls silently
/// replace the cached state.
///
/// `circuit_xbc` is the self-contained binary artifact `xark build` always
/// writes; `pk_bytes` is the `pk.bin` from `xark setup`.
#[wasm_bindgen]
pub fn preload(circuit_xbc: &Bytes, pk_bytes: &Bytes) -> Result<(), js_sys::Error> {
    let circuit_xbc = to_bytes(circuit_xbc, "circuit.xbc")?;
    let pk_bytes = to_bytes(pk_bytes, "pk.bin")?;
    let artifacts = load_artifacts(&circuit_xbc, &pk_bytes)?;

    ARTIFACTS.with(|cell| *cell.borrow_mut() = Some(artifacts));

    Ok(())
}

/// Prove using the artifacts cached by a prior [`preload`] call — skipping the
/// `.xbc` expansion, `pk.bin` deserialization, and R1CS minimize on every call.
///
/// Does not self-verify; verify a returned proof with [`verify`] when needed.
/// Returns the same shape as [`prove`]. Throws if [`preload`] hasn't been called.
#[wasm_bindgen]
pub fn prove_preloaded(inputs: JsValue) -> Result<ProofBundle, js_sys::Error> {
    ARTIFACTS.with(|cell| -> Result<ProofBundle, js_sys::Error> {
        let state = cell.borrow();
        let s = state
            .as_ref()
            .ok_or_else(|| js_error("call preload() first"))?;
        let id_inputs = resolve_inputs(&s.by_name, inputs).map_err(|e| js_error(&e))?;
        prove_with(&s.circuit, &s.r1cs, &s.pk, &id_inputs)
    })
}

/// Generate a Groth16 proof entirely in memory.
///
/// See the crate docs for the shape of each argument and the return object.
/// Every byte argument accepts a `Uint8Array` **or** an `ArrayBuffer` — so the
/// result of `await response.arrayBuffer()` can be passed directly.
///
/// Throws an `Error` on any error: a malformed `.xbc`, unknown input,
/// an unsatisfiable witness, or a malformed proving key.
///
/// Does not self-verify (matching snarkjs / arkworks / gnark) — verify a
/// returned proof with [`verify`] when needed.
#[wasm_bindgen]
pub fn prove(
    circuit_xbc: &Bytes,
    pk_bytes: &Bytes,
    inputs: JsValue,
) -> Result<ProofBundle, js_sys::Error> {
    let circuit_xbc = to_bytes(circuit_xbc, "circuit.xbc")?;
    let pk_bytes = to_bytes(pk_bytes, "pk.bin")?;
    let s = load_artifacts(&circuit_xbc, &pk_bytes)?;
    let id_inputs = resolve_inputs(&s.by_name, inputs).map_err(|e| js_error(&e))?;
    prove_with(&s.circuit, &s.r1cs, &s.pk, &id_inputs)
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
    let proof_bytes = to_bytes(proof_bytes, "proof")?;
    let public_inputs_bytes = to_bytes(public_inputs_bytes, "public inputs")?;
    let vk = deserialize_bytes::<VerifyingKey<Bn254>>(&vk_bytes, "verifying key")?;
    let proof = deserialize_bytes::<Proof<Bn254>>(&proof_bytes, "proof")?;
    let public: Vec<Fr> = deserialize_bytes(&public_inputs_bytes, "public inputs")?;
    Groth16::<Bn254>::verify(&vk, &public, &proof).map_err(|e| js_error(&format!("verifying: {e}")))
}

/// Convert a binary proof (the `proof` `Uint8Array` from [`prove`], == `proof.bin`)
/// to the snarkjs proof object.
#[wasm_bindgen]
pub fn proof_to_snarkjs(proof_bytes: &Bytes) -> Result<JsValue, js_sys::Error> {
    let proof_bytes = to_bytes(proof_bytes, "proof")?;
    let proof = deserialize_bytes::<Proof<Bn254>>(&proof_bytes, "proof")?;
    serde_wasm_bindgen::to_value(&snarkjs_proof(&proof))
        .map_err(|e| js_error(&format!("encoding snarkjs proof: {e}")))
}

/// Convert binary public inputs (the `publicInputs` `Uint8Array` from [`prove`],
/// == `public_inputs.bin`) to the snarkjs `public.json` array of decimal strings.
#[wasm_bindgen]
pub fn public_inputs_to_snarkjs(public_inputs_bytes: &Bytes) -> Result<JsValue, js_sys::Error> {
    let public_inputs_bytes = to_bytes(public_inputs_bytes, "public inputs")?;
    let public: Vec<Fr> = deserialize_bytes(&public_inputs_bytes, "public inputs")?;
    serde_wasm_bindgen::to_value(&snarkjs_public(&public))
        .map_err(|e| js_error(&format!("encoding snarkjs public inputs: {e}")))
}

/// xark-wasm package version.
#[wasm_bindgen]
pub fn version() -> String {
    env!("CARGO_PKG_VERSION").to_string()
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

/// Deserialize canonical compressed bytes (the form `xark setup` / `xark prove`
/// write), validating as it parses. `what` labels the value in any error.
fn deserialize_bytes<T: CanonicalDeserialize>(
    bytes: &[u8],
    what: &str,
) -> Result<T, js_sys::Error> {
    T::deserialize_with_mode(bytes, Compress::Yes, Validate::Yes)
        .map_err(|e| js_error(&format!("deserializing {what}: {e}")))
}
