//! WebAssembly bindings for generating xark Groth16 (BN254) proofs.
//!
//! This is the browser/Node entry point for the *proving* half of the xark
//! toolchain. It mirrors what `xark prove` does on the host — but with no
//! filesystem: every artifact is passed in over the JS boundary.
//!
//! ## What you need (produced offline by the host toolchain)
//!
//! | artifact       | produced by    | passed as                          |
//! |----------------|----------------|-----------------------------------|
//! | `circuit.xbc`  | `xark build`   | `circuit_xbc: Uint8Array` (binary) |
//! | `pk.bin`       | `xark setup`   | `pk_bytes: Uint8Array`             |
//! | witness inputs | (your circuit) | `inputs_json: string` (`{"name":"value", …}`) |
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
//! So every heavy artifact — circuit, proving/verifying key, proof, public
//! inputs — is binary. Only the witness inputs (a tiny `name → value` map) stay
//! JSON, matching `xark prove --inputs`.
//!
//! ## JS usage (`--target web`)
//!
//! ```js,ignore
//! import init, { prove } from "./pkg/xark_wasm.js";
//! await init();    // instantiate the module
//!
//! const xbc        = new Uint8Array(await (await fetch("/circuit/circuit.xbc")).arrayBuffer());
//! const pkBytes    = new Uint8Array(await (await fetch("/circuit/pk.bin")).arrayBuffer());
//! const inputsJson = JSON.stringify({ secret: "3", result: "27" });
//!
//! const out = prove(xbc, pkBytes, inputsJson);
//! // => ProveResult {
//! //   proof:            Uint8Array,   // canonical compressed bytes (== proof.bin)
//! //   publicInputs:     Uint8Array,   // canonical compressed bytes (== public_inputs.bin)
//! //   numPublicInputs:  number,
//! // }
//! //
//! // snarkjs-compatible JSON is opt-in (most callers only need the bytes):
//! //   proof_to_snarkjs_json(out.proof)                 // == snarkjs-proof.json
//! //   public_inputs_to_snarkjs_json(out.publicInputs)  // == snarkjs-public.json
//! ```
//!
//! ## Security
//!
//! Prover randomness is drawn from the platform CSPRNG (`OsRng`, backed by
//! `crypto.getRandomValues`) — the same source the host `xark prove` production
//! path uses. There is **no** deterministic-RNG escape hatch here on purpose:
//! reproducible prover randomness breaks zero-knowledge.

use std::cell::RefCell;
use std::collections::BTreeMap;

use ark_bn254::{Bn254, Fr};
use ark_groth16::{Groth16, Proof, ProvingKey, VerifyingKey};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use ark_snark::SNARK;
use wasm_bindgen::prelude::*;

use xark_ir::function_decode::{
    expand_function_blob, expand_function_blob_reduced,
};
use xark_ir::primitive::{Var, VarRole};
use xark_ir::solver;
use xark_ir::{CircuitProgram, R1csProgram, VarId};
use xark_prover::{lower_witness, try_fr_from_decimal, XarkCircuit};
use xark_snarkjs::{proof_to_snarkjs, public_inputs_to_snarkjs};

// ---- preload: parse the heavy artifacts once, prove many times -------------

struct PreState {
    /// Full circuit (witness-gen intact) — solved on every [`prove_preloaded`] call.
    full: CircuitProgram,
    /// The **minimized** backend R1CS the proving key is keyed to — already run
    /// through the boundary minimize in [`preload`] (identically to how `xark
    /// setup` keyed the pk), so [`prove_preloaded`] can prove against it directly
    /// without re-minimizing on every call.
    prog: R1csProgram,
    by_name: BTreeMap<String, VarId>,
    pk: ProvingKey<Bn254>,
}

thread_local! {
    static PRESTATE: RefCell<Option<PreState>> = const { RefCell::new(None) };
}

/// Derive the two views the prover needs from one self-contained `circuit.xbc`,
/// mirroring `xark prove`:
///
/// * the full `CircuitProgram` (witness-gen present) for the solver, and
/// * the minimized `R1csProgram` the proving key was generated against.
///
/// `expand_function_blob_reduced` is the *only* correct source for the backend
/// R1CS — the proving key is keyed to exactly that circuit (`xark setup` builds
/// `for_setup(expand_function_blob_reduced(...).into_r1cs())`). Using the full
/// expand's R1CS instead would produce a different constraint set and the proof
/// would not verify.
fn expand_xbc(
    circuit_xbc: &[u8],
) -> Result<(CircuitProgram, R1csProgram), String> {
    let full = expand_function_blob(circuit_xbc)?;
    let prog = expand_function_blob_reduced(circuit_xbc)?.into_r1cs();
    Ok((full, prog))
}

/// Solve the witness on the full circuit and lower field-prime values → `Fr`.
///
/// The solver checks the assignment against the *full* constraint set (a
/// satisfying witness satisfies the minimized set too), so an unsatisfiable
/// input is rejected here rather than producing a proof that fails to verify.
fn solve_witness(
    full: &CircuitProgram,
    id_inputs: &BTreeMap<VarId, String>,
) -> Result<BTreeMap<VarId, Fr>, String> {
    let assign_fp = solver::solve_and_check_cp(full, id_inputs)
        .map_err(|e| format!("witness does not satisfy the circuit: {e:?}"))?;
    // Lower the solved witness (`VarId → Fp`) to Groth16 scalars via the shared
    // `xark-prover` helper — the same lowering `xark prove` uses on the host.
    Ok(lower_witness(&assign_fp))
}

/// Resolve a `name → value` JSON object to `VarId → decimal` for the solver,
/// validating each value as a field element (mirrors `xark prove --inputs`).
/// `by_name` is the circuit's `name → VarId` map (built once in [`preload`]).
fn resolve_inputs(
    by_name: &BTreeMap<String, VarId>,
    inputs_json: &str,
) -> Result<BTreeMap<VarId, String>, String> {
    let inputs: BTreeMap<String, String> = serde_json::from_str(inputs_json)
        .map_err(|e| format!("parsing inputs JSON (expect object name→value): {e}"))?;
    let mut id_inputs: BTreeMap<VarId, String> = BTreeMap::new();
    for (k, v) in &inputs {
        let &id = by_name
            .get(k)
            .ok_or_else(|| format!("unknown input `{k}`"))?;
        // Strict decimal validation (mirrors `xark prove`): a malformed value is
        // a clean error, not a silently-zeroed witness.
        try_fr_from_decimal(v)
            .map_err(|e| format!("invalid value for input `{k}`: {e}"))?;
        id_inputs.insert(id, v.clone());
    }
    Ok(id_inputs)
}

/// Prove given already-expanded circuit views + the proving key. `prog` must be
/// the **pre-minimized** backend R1CS the pk is keyed to (callers run the
/// boundary minimize once, up-front, and pass the result).
///
/// Does **not** self-verify — matching snarkjs / arkworks / gnark, where
/// proving and verifying are separate steps. A self-verify would only catch
/// your own witness/circuit bugs (it's a dev/QA aid, never an adversarial
/// safeguard), so it belongs in the consumer's [`verify`] call, not baked into
/// every production proof. Verify a returned proof with [`verify`] when needed.
fn prove_with(
    full: &CircuitProgram,
    prog: &R1csProgram,
    pk: &ProvingKey<Bn254>,
    id_inputs: &BTreeMap<VarId, String>,
) -> Result<ProveResult, JsValue> {
    let assign = solve_witness(full, id_inputs)
        .map_err(|e| js(&e))?;

    // The `prog` passed in is already the **minimized** backend R1CS the pk is
    // keyed to (both call sites run the boundary minimize once, up-front:
    // `preload` caches it, `prove` does it inline). So prove against it directly
    // — re-minimizing here would just reproduce the same fixpoint per proof.
    let circuit = XarkCircuit::for_proving_preminimized(prog.clone(), assign);
    circuit
        .validate()
        .map_err(|e| js(&format!("malformed circuit: {e}")))?;
    let public = circuit.public_inputs();

    let mut rng = rand::rngs::OsRng;
    let proof = Groth16::<Bn254>::prove(pk, circuit, &mut rng)
        .map_err(|e| js(&format!("proving: {e}")))?;

    encode_result(&proof, &public)
}

/// Serialize the proof + public inputs into a [`ProveResult`] of canonical
/// binary — exactly the `.bin` files `xark prove` writes, and the inputs
/// [`verify`] expects.
///
/// snarkjs-compatible JSON is **not** produced here: it's a lossless view of
/// these same bytes that most callers never need, so deriving it on every proof
/// would be wasted work. Callers who want it opt in via [`proof_to_snarkjs_json`]
/// / [`public_inputs_to_snarkjs_json`] on the returned `proof` / `publicInputs`.
///
/// The result of [`prove`] / [`prove_preloaded`]: the canonical compressed
/// proof + public-input bytes (identical to the host's `proof.bin` /
/// `public_inputs.bin`), plus the public-input count.
///
/// A typed struct (rather than an untyped JS object) so wasm-bindgen emits real
/// `.d.ts` types and the fields cross the boundary as `Uint8Array` / `number`
/// without manual `Reflect` plumbing. Field getters clone, so the JS caller owns
/// the returned arrays.
#[wasm_bindgen(getter_with_clone)]
pub struct ProveResult {
    /// Canonical compressed proof bytes (`== proof.bin`).
    pub proof: Vec<u8>,
    /// Canonical compressed public-input bytes (`== public_inputs.bin`).
    #[wasm_bindgen(js_name = publicInputs)]
    pub public_inputs: Vec<u8>,
    /// Number of public inputs.
    #[wasm_bindgen(js_name = numPublicInputs)]
    pub num_public_inputs: usize,
}

fn encode_result(proof: &Proof<Bn254>, public: &[Fr]) -> Result<ProveResult, JsValue> {
    let mut proof_buf = Vec::new();
    proof
        .serialize_with_mode(&mut proof_buf, Compress::Yes)
        .map_err(|e| js(&format!("serializing proof: {e}")))?;
    let mut public_buf = Vec::new();
    public
        .serialize_with_mode(&mut public_buf, Compress::Yes)
        .map_err(|e| js(&format!("serializing public inputs: {e}")))?;

    Ok(ProveResult {
        proof: proof_buf,
        public_inputs: public_buf,
        num_public_inputs: public.len(),
    })
}

/// Load + prepare every artifact from the raw bytes: expand the two `.xbc`
/// views, build the `name → VarId` map, minimize the backend R1CS the pk is
/// keyed to, and deserialize the proving key. Shared by [`prove`] and
/// [`preload`] so the one-shot and preloaded paths prepare artifacts identically.
fn load_artifacts(circuit_xbc: &[u8], pk_bytes: &[u8]) -> Result<PreState, JsValue> {
    let (full, reduced) =
        expand_xbc(circuit_xbc).map_err(|e| js(&format!("parsing circuit.xbc: {e}")))?;
    let by_name: BTreeMap<String, VarId> =
        full.vars.iter().map(|v| (v.name.clone(), v.id)).collect();
    // Minimize the backend R1CS **once**, exactly as `xark setup` did when it
    // keyed the proving key (`for_setup` runs the same boundary minimize).
    // Caching the minimized form lets [`prove_preloaded`] use
    // `for_proving_preminimized` and skip re-minimizing on every proof — the
    // dominant per-proof cost on large circuits.
    let prog = XarkCircuit::for_setup(reduced).prog().clone();
    let pk = ProvingKey::<Bn254>::deserialize_with_mode(pk_bytes, Compress::Yes, Validate::Yes)
        .map_err(|e| js(&format!("deserializing proving key: {e}")))?;
    Ok(PreState {
        full,
        prog,
        by_name,
        pk,
    })
}

/// Parse a circuit's `circuit.xbc` + `pk.bin` once so subsequent calls to
/// [`prove_preloaded`] skip all heavy deserialization. Call once per circuit;
/// subsequent calls silently replace the cached state.
///
/// `circuit_xbc` is the self-contained binary artifact `xark build` always
/// writes; `pk_bytes` is the `pk.bin` from `xark setup`.
#[wasm_bindgen]
pub fn preload(circuit_xbc: &[u8], pk_bytes: &[u8]) -> Result<(), JsValue> {
    let state = load_artifacts(circuit_xbc, pk_bytes)?;
    PRESTATE.with(|cell| *cell.borrow_mut() = Some(state));
    Ok(())
}

/// Prove using the artifacts cached by a prior [`preload`] call — skipping the
/// `.xbc` expansion, `pk.bin` deserialization, and R1CS minimize on every call.
///
/// Does not self-verify; verify a returned proof with [`verify`] when needed.
/// Returns the same shape as [`prove`]. Throws if [`preload`] hasn't been called.
#[wasm_bindgen]
pub fn prove_preloaded(inputs_json: &str) -> Result<ProveResult, JsValue> {
    PRESTATE.with(|cell| -> Result<ProveResult, JsValue> {
        let state = cell.borrow();
        let s = state
            .as_ref()
            .ok_or_else(|| js("call preload() first"))?;
        let id_inputs = resolve_inputs(&s.by_name, inputs_json)
            .map_err(|e| js(&e))?;
        prove_with(&s.full, &s.prog, &s.pk, &id_inputs)
    })
}

/// Generate a Groth16 proof entirely in memory.
///
/// See the crate docs for the shape of each argument and the return object.
/// Throws a `JsValue` (string) on any error: a malformed `.xbc`, unknown input,
/// an unsatisfiable witness, or a malformed proving key.
///
/// Does not self-verify (matching snarkjs / arkworks / gnark) — verify a
/// returned proof with [`verify`] when needed.
#[wasm_bindgen]
pub fn prove(circuit_xbc: &[u8], pk_bytes: &[u8], inputs_json: &str) -> Result<ProveResult, JsValue> {
    let s = load_artifacts(circuit_xbc, pk_bytes)?;
    let id_inputs = resolve_inputs(&s.by_name, inputs_json)
        .map_err(|e| js(&e))?;
    prove_with(&s.full, &s.prog, &s.pk, &id_inputs)
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
    let vk = VerifyingKey::<Bn254>::deserialize_with_mode(vk_bytes, Compress::Yes, Validate::Yes)
        .map_err(|e| js(&format!("deserializing verifying key: {e}")))?;
    let proof = Proof::<Bn254>::deserialize_with_mode(proof_bytes, Compress::Yes, Validate::Yes)
        .map_err(|e| js(&format!("deserializing proof: {e}")))?;
    let public: Vec<Fr> =
        Vec::<Fr>::deserialize_with_mode(public_inputs_bytes, Compress::Yes, Validate::Yes)
            .map_err(|e| js(&format!("deserializing public inputs: {e}")))?;
    Groth16::<Bn254>::verify(&vk, &public, &proof).map_err(|e| js(&format!("verifying: {e}")))
}

/// Convert a binary proof (the `proof` `Uint8Array` from [`prove`], == `proof.bin`)
/// to snarkjs-compatible JSON — the same shape the host writes to
/// `snarkjs-proof.json`. Opt-in: [`prove`] returns only the canonical bytes, so
/// callers who need snarkjs interop derive the JSON here.
#[wasm_bindgen]
pub fn proof_to_snarkjs_json(proof_bytes: &[u8]) -> Result<String, JsValue> {
    let proof = Proof::<Bn254>::deserialize_with_mode(proof_bytes, Compress::Yes, Validate::Yes)
        .map_err(|e| js(&format!("deserializing proof: {e}")))?;
    serde_json::to_string(&proof_to_snarkjs(&proof))
        .map_err(|e| js(&format!("encoding snarkjs proof: {e}")))
}

/// Convert binary public inputs (the `publicInputs` `Uint8Array` from [`prove`],
/// == `public_inputs.bin`) to the snarkjs `public.json` array of decimal strings.
/// Opt-in, mirroring [`proof_to_snarkjs_json`].
#[wasm_bindgen]
pub fn public_inputs_to_snarkjs_json(public_inputs_bytes: &[u8]) -> Result<String, JsValue> {
    let public: Vec<Fr> =
        Vec::<Fr>::deserialize_with_mode(public_inputs_bytes, Compress::Yes, Validate::Yes)
            .map_err(|e| js(&format!("deserializing public inputs: {e}")))?;
    serde_json::to_string(&public_inputs_to_snarkjs(&public))
        .map_err(|e| js(&format!("encoding snarkjs public inputs: {e}")))
}

/// List a circuit's declared inputs (the values [`prove`]'s `inputs_json` must
/// supply) as a JSON string: `[{"name":"…","role":"public"|"private"}, …]` in
/// declaration (variable-id) order. Convenience for the JS caller.
///
/// `circuit_xbc` is the binary `circuit.xbc`.
#[wasm_bindgen]
pub fn circuit_inputs(circuit_xbc: &[u8]) -> Result<String, JsValue> {
    // TODO: switch to a header-only parse (variable metadata only) when
    // `xark-ir` exposes one — expanding the full circuit just to list declared
    // inputs is heavier than necessary.
    let full = expand_function_blob(circuit_xbc)
        .map_err(|e| js(&format!("parsing circuit.xbc: {e}")))?;
    let mut vars: Vec<&Var> = full
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
                    VarRole::Derived => "other",
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

/// Runs once when the wasm module is instantiated (after `await init()` on the
/// `web` target; on `require`/`import` for node/bundler). Installs the panic
/// hook here so every export gets readable panic messages without each one
/// re-arming it.
#[wasm_bindgen(start)]
pub fn start() {
    console_error_panic_hook::set_once();
}

fn js(msg: &str) -> JsValue {
    JsValue::from_str(msg)
}
