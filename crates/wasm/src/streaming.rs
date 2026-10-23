//! Streaming prover bindings ([`prove_streaming`]) and the Web-Worker kernels the
//! optional parallel pool (`js/pool.cjs`) runs.
//!
//! [`prove_streaming`] never materializes the constraint system or the proving
//! key in wasm memory: rows are expanded window-by-window from `circuit.xbc`, the
//! witness is solved by streaming the hint program, and the proving key stays in
//! its JS `Uint8Array` — only one chunk of points at a time is copied in. The
//! linear-memory peak is the witness plus two FFT vectors.
//!
//! With a worker pool (`options.pool`), the FFT sweeps and MSM chunks are handed
//! to workers through a `SharedArrayBuffer`; without one (no cross-origin
//! isolation), the same prover runs single-threaded with the same memory profile.

use std::cell::RefCell;
use std::io::{Read, Seek, SeekFrom};

use ark_bn254::Bn254;
use ark_bn254::Fr;
use ark_ff::{UniformRand, Zero};
use rand::SeedableRng;
use wasm_bindgen::prelude::*;
use xark_groth16::accel::{self, Accelerator};
use xark_groth16::fft::ColOp;
use xark_groth16::msm::Scalar;
use xark_groth16::ProvingKey;
use xark_groth16::{
    BytecodeSource, ConstraintSource, Domain, FftConfig, InMemoryPk, ProverConfig, RowFileSource,
    SerializedPk,
};

use crate::{encode_result, js_error, resolve_inputs, to_bytes, Bytes, ProofBundle};

/// A `Read + Seek` view of a JS `Uint8Array` that copies only what is read.
struct JsReader {
    arr: js_sys::Uint8Array,
    pos: u64,
    len: u64,
}

impl Read for JsReader {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let n = (buf.len() as u64).min(self.len.saturating_sub(self.pos)) as usize;
        if n > 0 {
            self.arr
                .subarray(self.pos as u32, (self.pos + n as u64) as u32)
                .copy_to(&mut buf[..n]);
            self.pos += n as u64;
        }
        Ok(n)
    }
}

impl Seek for JsReader {
    fn seek(&mut self, to: SeekFrom) -> std::io::Result<u64> {
        let p = match to {
            SeekFrom::Start(p) => p as i64,
            SeekFrom::End(d) => self.len as i64 + d,
            SeekFrom::Current(d) => self.pos as i64 + d,
        };
        if p < 0 {
            return Err(std::io::Error::other("seek before start"));
        }
        self.pos = p as u64;
        Ok(self.pos)
    }
}

/// A `Uint8Array` view of a byte argument (`Uint8Array`, `ArrayBuffer`, or
/// `SharedArrayBuffer`) — no copy into wasm memory.
fn js_view(v: &Bytes, what: &str) -> Result<js_sys::Uint8Array, js_sys::Error> {
    let raw: &JsValue = v.as_ref();
    if let Some(a) = raw.dyn_ref::<js_sys::Uint8Array>() {
        return Ok(a.clone());
    }
    if raw.is_instance_of::<js_sys::ArrayBuffer>()
        || raw.is_instance_of::<js_sys::SharedArrayBuffer>()
    {
        return Ok(js_sys::Uint8Array::new(raw));
    }
    Err(js_error(&format!(
        "{what} must be a Uint8Array or (Shared)ArrayBuffer"
    )))
}

#[wasm_bindgen]
extern "C" {
    /// The worker pool from `js/pool.cjs` (any object with these methods works).
    /// Each call blocks until the workers finish (`Atomics.wait`).
    pub type WorkerPool;
    #[wasm_bindgen(method, js_name = toCoset)]
    fn to_coset(this: &WorkerPool, n1: u32, n2: u32, buf: &mut [u8]) -> bool;
    #[wasm_bindgen(method, js_name = fromCosetToT)]
    fn from_coset_to_t(this: &WorkerPool, n1: u32, n2: u32, buf: &mut [u8]) -> bool;
    #[wasm_bindgen(method, js_name = decompress)]
    fn decompress(this: &WorkerPool, g2: bool, points: &[u8]) -> Option<Vec<u8>>;
    #[wasm_bindgen(method, js_name = msm)]
    fn msm(
        this: &WorkerPool,
        g2: bool,
        points: &[u8],
        compressed: bool,
        scalars: &[u8],
    ) -> Option<Vec<u8>>;
}

struct PoolAccel(WorkerPool);

/// Parks a quotient vector in a JS `Uint8Array` — outside wasm linear memory, so
/// the 4 GB wasm32 ceiling holds one domain vector fewer.
struct JsSpill(js_sys::Uint8Array);

impl xark_groth16::spill::Spill for JsSpill {
    fn store(&mut self, data: &[Fr]) -> std::io::Result<()> {
        let bytes = unsafe {
            std::slice::from_raw_parts(data.as_ptr() as *const u8, std::mem::size_of_val(data))
        };
        if self.0.length() as usize != bytes.len() {
            self.0 = js_sys::Uint8Array::new_with_length(bytes.len() as u32);
        }
        self.0.copy_from(bytes);
        Ok(())
    }
    fn load(&mut self, off: usize, out: &mut [Fr]) -> std::io::Result<()> {
        let n = std::mem::size_of_val(out);
        self.0
            .subarray((off * 32) as u32, (off * 32 + n) as u32)
            .copy_to(accel::fr_bytes_mut(out));
        Ok(())
    }
}

/// The host's offloads for one proof: an optional worker pool, and (`spill`)
/// parking quotient vectors in JS memory.
struct Host {
    pool: Option<PoolAccel>,
    spill: bool,
}

impl Host {
    fn from_options(options: &JsValue) -> Self {
        Host {
            pool: opt_get(options, "pool").map(|p| PoolAccel(p.unchecked_into())),
            spill: opt_get(options, "spill").is_some_and(|v| v.is_truthy()),
        }
    }
}

impl Accelerator for Host {
    fn to_coset(&mut self, dom: &Domain, buf: &mut [Fr]) -> bool {
        self.pool.as_mut().is_some_and(|p| p.to_coset(dom, buf))
    }
    fn from_coset_to_t(&mut self, dom: &Domain, buf: &mut [Fr]) -> bool {
        self.pool
            .as_mut()
            .is_some_and(|p| p.from_coset_to_t(dom, buf))
    }
    fn wants_msm(&self) -> bool {
        self.pool.as_ref().is_some_and(|p| p.wants_msm())
    }
    fn msm(
        &mut self,
        g2: bool,
        points: &[u8],
        compressed: bool,
        scalars: &[Scalar],
    ) -> Option<Vec<u8>> {
        self.pool.as_mut()?.msm(g2, points, compressed, scalars)
    }
    fn decompress(&mut self, g2: bool, points: &[u8]) -> Option<Vec<u8>> {
        self.pool.as_mut()?.0.decompress(g2, points)
    }
    fn spill(&mut self) -> Option<Box<dyn xark_groth16::spill::Spill>> {
        self.spill
            .then(|| Box::new(JsSpill(js_sys::Uint8Array::new_with_length(0))) as Box<_>)
    }
}

impl Accelerator for PoolAccel {
    fn to_coset(&mut self, dom: &Domain, buf: &mut [Fr]) -> bool {
        dom.is_blocked()
            && self
                .0
                .to_coset(dom.n1 as u32, dom.n2 as u32, accel::fr_bytes_mut(buf))
    }
    fn from_coset_to_t(&mut self, dom: &Domain, buf: &mut [Fr]) -> bool {
        dom.is_blocked()
            && self
                .0
                .from_coset_to_t(dom.n1 as u32, dom.n2 as u32, accel::fr_bytes_mut(buf))
    }
    fn wants_msm(&self) -> bool {
        true
    }
    fn msm(
        &mut self,
        g2: bool,
        points: &[u8],
        compressed: bool,
        scalars: &[Scalar],
    ) -> Option<Vec<u8>> {
        self.0
            .msm(g2, points, compressed, &accel::scalars_to_bytes(scalars))
    }
}

fn opt_get(options: &JsValue, key: &str) -> Option<JsValue> {
    if options.is_undefined() || options.is_null() {
        return None;
    }
    js_sys::Reflect::get(options, &JsValue::from_str(key))
        .ok()
        .filter(|v| !v.is_undefined() && !v.is_null())
}

/// Everything a proof needs besides the inputs: parsed once by
/// [`preload_streaming`], or built per call by [`prove_streaming`].
pub(crate) struct Prepared {
    xbc: Vec<u8>,
    vars: Vec<xark_ir::primitive::Var>,
    src: Box<dyn ConstraintSource>,
    key: Key,
    /// `sources.json`, to name the statement a failing witness breaks.
    sources: Option<xark_ir::SourceMap>,
}

/// `sources.json` text, parsed (a malformed one is an error: it was passed on
/// purpose).
pub(crate) fn parse_sources(
    text: Option<String>,
) -> Result<Option<xark_ir::SourceMap>, js_sys::Error> {
    text.map(|t| {
        xark_ir::SourceMap::from_json(&t)
            .map_err(|e| js_error(&format!("parsing sources.json: {e}")))
    })
    .transpose()
}

/// The error for inputs that don't satisfy the circuit: the statement that fails,
/// from `sources`, else the constraint. The prover's own row order can differ (a
/// minimized key), so the failing row is found again in build order, solving the
/// witness a second time; this only runs on the way to an error.
fn unsatisfied(
    xbc: &[u8],
    ids: &std::collections::BTreeMap<u32, String>,
    sources: Option<&xark_ir::SourceMap>,
) -> js_sys::Error {
    let row = xark_ir::function_decode::stream_solve_dense(xbc, ids)
        .ok()
        .and_then(|slots| xark_ir::function_decode::first_failing_row(xbc, &slots));
    let Some(row) = row else {
        return js_error("the inputs don't satisfy the circuit (a constraint fails)");
    };
    match sources.and_then(|s| s.at(row)) {
        Some(site) => crate::check_failed(site),
        None => js_error(&format!(
            "the inputs don't satisfy the circuit: constraint #{row} fails (pass the build's \
             sources.json to name its source line)"
        )),
    }
}

#[allow(clippy::large_enum_variant)] // one per preloaded circuit
enum Key {
    /// Kept in its JS buffer; one chunk of points is decoded at a time.
    Streamed(SerializedPk<JsReader>),
    /// Decoded once into wasm memory (`residentKey`): no per-proof point
    /// decompression, at the cost of holding the whole decoded key.
    Resident(Box<ProvingKey<Bn254>>),
}

/// The constraint rows: from `options.r1cs` (an `r1cs.stream`, for a `minimized`
/// key) or straight from the bytecode (a `reduced` key).
fn row_source(xbc: &[u8], options: &JsValue) -> Result<Box<dyn ConstraintSource>, js_sys::Error> {
    Ok(match opt_get(options, "r1cs") {
        Some(r1cs) => {
            let bytes = to_bytes(r1cs.unchecked_ref(), "r1cs.stream")?;
            let src = RowFileSource::new(bytes)
                .map_err(|e| js_error(&format!("parsing r1cs.stream: {e}")))?;
            if !xark_ir::function_decode::row_file_fits(
                src.file().fingerprint(),
                &crate::sha256_hex(xbc),
                xbc,
            ) {
                return Err(js_error(
                    "r1cs.stream was written for a different circuit.xbc — re-run `xark setup`",
                ));
            }
            Box::new(src)
        }
        None => {
            let mut src = BytecodeSource::new(xbc)
                .map_err(|e| js_error(&format!("parsing circuit.xbc: {e}")))?;
            // Benchmarking only: rebuild rows symbolically instead of evaluating
            // the compiled templates (same results, much slower).
            if opt_get(options, "expandRows").is_some_and(|v| v.is_truthy()) {
                src.set_compiled(false);
            }
            Box::new(src)
        }
    })
}

/// Solve the witness by streaming the hint program and lay it out for the prover
/// (`z[0] = 1`), straight from the solver's dense slots.
fn witness(
    xbc: &[u8],
    ids: &std::collections::BTreeMap<u32, String>,
    layout: &xark_groth16::VarLayout,
) -> Result<Vec<Fr>, js_sys::Error> {
    let slots = xark_ir::function_decode::stream_solve_dense(xbc, ids)
        .map_err(|e| js_error(&format!("solving witness: {e}")))?;
    Ok(layout.assignment(|id| {
        slots.get(id as usize).and_then(|o| o.as_ref()).map(|v| {
            v.as_bn254_fr()
                .unwrap_or_else(|| xark_prover::fr_from_decimal(&v.to_decimal()))
        })
    }))
}

/// Prover settings + randomness from `options` (`msmChunk`, `tile`, `seed`,
/// `domainSize`).
fn config(options: &JsValue) -> (ProverConfig, Fr, Fr) {
    let mut cfg = ProverConfig {
        msm_chunk: 1 << 18,
        ..ProverConfig::default()
    };
    // Optional for streamed proofs: the key's header states the domain. With it,
    // `h` is computed before any key bytes; a wrong value costs a recomputation,
    // never a wrong proof.
    if let Some(n) = opt_get(options, "domainSize").and_then(|v| v.as_f64()) {
        cfg.domain = Some(n as usize);
    }
    if let Some(c) = opt_get(options, "msmChunk").and_then(|v| v.as_f64()) {
        cfg.msm_chunk = c as usize;
    }
    if let Some(t) = opt_get(options, "tile").and_then(|v| v.as_f64()) {
        cfg.fft = FftConfig {
            tile: t as usize,
            ..cfg.fft
        };
    }
    let (r, s) = match opt_get(options, "seed").and_then(|v| v.as_f64()) {
        Some(seed) => {
            let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(seed as u64);
            (Fr::rand(&mut rng), Fr::rand(&mut rng))
        }
        None => {
            let mut rng = rand::rngs::OsRng;
            (Fr::rand(&mut rng), Fr::rand(&mut rng))
        }
    };
    (cfg, r, s)
}

fn mismatch_error(e: xark_groth16::ProveError) -> js_sys::Error {
    match e {
        xark_groth16::ProveError::Unsatisfied { .. } => js_error(
            "the inputs don't satisfy the circuit (a constraint fails); `xark prove` with \
             the same inputs names the constraint and its source line",
        ),
        xark_groth16::ProveError::SelfCheckFailed => js_error(
            "the proving key doesn't match this circuit.xbc: it was made for a different \
             circuit or an earlier build of it (rerun `xark setup` and use its pk.bin)",
        ),
        xark_groth16::ProveError::KeyMismatch(m) => js_error(&format!(
            "{m} — a `reduced` key proves from circuit.xbc alone; a `minimized` key also \
             needs its r1cs.stream (options.r1cs)"
        )),
        e => js_error(&format!("proving: {e}")),
    }
}

fn prepare(
    circuit_xbc: &Bytes,
    pk_bytes: &Bytes,
    options: &JsValue,
) -> Result<Prepared, js_sys::Error> {
    let xbc = to_bytes(circuit_xbc, "circuit.xbc")?;
    let vars = xark_ir::function_decode::decode_input_vars(&xbc);
    let src = row_source(&xbc, options)?;
    let arr = js_view(pk_bytes, "pk.bin")?;
    let len = arr.length() as u64;
    let reader = JsReader { arr, pos: 0, len };
    let resident = opt_get(options, "residentKey").is_some_and(|v| v.is_truthy());
    let key = if resident {
        Key::Resident(Box::new(crate::deserialize_proving_key_from(reader)?))
    } else {
        Key::Streamed(SerializedPk::new(reader).map_err(|e| js_error(&e.to_string()))?)
    };
    let sources = parse_sources(opt_get(options, "sources").and_then(|v| v.as_string()))?;
    Ok(Prepared {
        xbc,
        vars,
        src,
        key,
        sources,
    })
}

/// The rows a key was made for, without an `r1cs.stream`: straight from the
/// bytecode for a `reduced` key (its variable count matches), else the minimized
/// program — rebuilt here exactly as `xark setup` keyed it — held as a compact
/// in-memory row file.
fn auto_row_source(xbc: &[u8], a_len: usize) -> Result<Box<dyn ConstraintSource>, js_sys::Error> {
    xark_prover::rows_for_key(xbc, a_len, None).map_err(|e| js_error(&e))
}

/// [`Prepared`] for the one-call API (`prove` / `preload`): the row source is
/// picked from the key, which stays in its JS buffer unless `resident`.
pub(crate) fn prepare_auto(
    circuit_xbc: &Bytes,
    pk_bytes: &Bytes,
    resident: bool,
    sources: Option<String>,
) -> Result<Prepared, js_sys::Error> {
    let sources = parse_sources(sources)?;
    let xbc = to_bytes(circuit_xbc, "circuit.xbc")?;
    let vars = xark_ir::function_decode::decode_input_vars(&xbc);
    let reader = || -> Result<JsReader, js_sys::Error> {
        let arr = js_view(pk_bytes, "pk.bin")?;
        let len = arr.length() as u64;
        Ok(JsReader { arr, pos: 0, len })
    };
    let streamed = SerializedPk::new(reader()?).map_err(|e| js_error(&e.to_string()))?;
    let src = auto_row_source(&xbc, xark_groth16::PkSource::header(&streamed).a_len)?;
    let key = if resident {
        drop(streamed);
        Key::Resident(Box::new(crate::deserialize_proving_key_from(reader()?)?))
    } else {
        Key::Streamed(streamed)
    };
    Ok(Prepared {
        xbc,
        vars,
        src,
        key,
        sources,
    })
}

/// Prove with a [`prepare_auto`]d circuit and default options.
pub(crate) fn prove_auto(p: &mut Prepared, inputs: JsValue) -> Result<ProofBundle, js_sys::Error> {
    prove_prepared(p, inputs, &JsValue::UNDEFINED)
}

fn prove_prepared(
    p: &mut Prepared,
    inputs: JsValue,
    options: &JsValue,
) -> Result<ProofBundle, js_sys::Error> {
    let ids = resolve_inputs(&p.vars, inputs).map_err(|e| js_error(&e))?;
    let z = witness(&p.xbc, &ids, p.src.layout())?;
    let ninst = p.src.layout().num_instance();

    let (cfg, r, s) = config(options);
    let accel = &mut Host::from_options(options);
    let res = match &mut p.key {
        Key::Streamed(pk) => {
            xark_groth16::prove_accelerated(&*p.src, &z, pk, r, s, &cfg, &mut (), accel)
        }
        Key::Resident(pk) => xark_groth16::prove_accelerated(
            &*p.src,
            &z,
            &mut InMemoryPk::new(pk),
            r,
            s,
            &cfg,
            &mut (),
            accel,
        ),
    };
    let proof = res.map_err(|e| match e {
        xark_groth16::ProveError::Unsatisfied { .. } => {
            unsatisfied(&p.xbc, &ids, p.sources.as_ref())
        }
        e => mismatch_error(e),
    })?;
    encode_result(&proof, &z[1..ninst])
}

/// Generate a Groth16 proof with the **streaming** prover.
///
/// Same arguments and result as [`prove`](crate::prove), plus `options`:
///
/// * `r1cs` — the `r1cs.stream` written by `xark setup` for a `minimized` key
///   (`metadata.json` `r1cs_form`). Omit for a `reduced` key, which streams from
///   `circuit.xbc` alone.
/// * `pool` — a worker pool from `js/pool.mjs` (`createPool`) to parallelize the
///   FFT and MSMs across Web Workers / worker threads (requires
///   `SharedArrayBuffer`, i.e. a cross-origin-isolated page). Omit for
///   single-threaded proving.
/// * `msmChunk` — proving-key points per streamed chunk (default 2¹⁸).
/// * `spill` — keep only one quotient vector in wasm memory, parking the other in
///   a JS buffer (for circuits near the 4 GB wasm32 limit).
/// * `sources` — the build's `sources.json` (text), so inputs that fail a check
///   name its source line.
/// * `seed` — **testing only**: deterministic prover randomness (breaks
///   zero-knowledge across proofs). Default: the platform CSPRNG.
///
/// A key for a different R1CS form is rejected with a clear error, never a bad
/// proof. The proof is self-verified before it is returned. To prove repeatedly,
/// use [`preload_streaming`] + [`prove_streaming_preloaded`].
#[wasm_bindgen(js_name = proveStreaming)]
pub fn prove_streaming(
    circuit_xbc: &Bytes,
    pk_bytes: &Bytes,
    inputs: JsValue,
    options: JsValue,
) -> Result<ProofBundle, js_sys::Error> {
    let mut p = prepare(circuit_xbc, pk_bytes, &options)?;
    prove_prepared(&mut p, inputs, &options)
}

thread_local! {
    static PRELOADED: RefCell<Option<Prepared>> = const { RefCell::new(None) };
}

/// Parse a circuit + key once for [`prove_streaming_preloaded`]: the variable
/// table, the row source (bytecode templates or `r1cs.stream`) and the key header
/// are kept; the key bytes stay in their JS buffer. `options`:
///
/// * `r1cs` — as for [`prove_streaming`].
/// * `residentKey` — decode the whole key into wasm memory now, so later proofs
///   skip point decompression (faster repeat proofs, single-threaded; the decoded
///   key is ~2.2× the compressed file). Leave off with a worker pool: workers
///   decompress their own chunks in parallel.
///
/// Replaces any previously preloaded circuit.
#[wasm_bindgen(js_name = preloadStreaming)]
pub fn preload_streaming(
    circuit_xbc: &Bytes,
    pk_bytes: &Bytes,
    options: JsValue,
) -> Result<(), js_sys::Error> {
    let p = prepare(circuit_xbc, pk_bytes, &options)?;
    PRELOADED.with(|c| *c.borrow_mut() = Some(p));
    Ok(())
}

/// Prove against the artifacts cached by [`preload_streaming`]. `options` as for
/// [`prove_streaming`] (`pool`, `msmChunk`, `seed`).
#[wasm_bindgen(js_name = proveStreamingPreloaded)]
pub fn prove_streaming_preloaded(
    inputs: JsValue,
    options: JsValue,
) -> Result<ProofBundle, js_sys::Error> {
    PRELOADED.with(|c| {
        let mut c = c.borrow_mut();
        let p = c
            .as_mut()
            .ok_or_else(|| js_error("call preloadStreaming() first"))?;
        prove_prepared(p, inputs, &options)
    })
}

/// Current wasm linear-memory size in bytes. Linear memory only grows, so after a
/// prove this is the run's peak.
#[wasm_bindgen(js_name = wasmMemoryBytes)]
pub fn wasm_memory_bytes() -> f64 {
    wasm_bindgen::memory()
        .unchecked_into::<js_sys::WebAssembly::Memory>()
        .buffer()
        .unchecked_into::<js_sys::ArrayBuffer>()
        .byte_length() as f64
}

// ---- worker kernels ----------------------------------------------------------------

thread_local! {
    static DOMAIN: RefCell<Option<Domain>> = const { RefCell::new(None) };
}

/// The coordinator's `n1 × n2` domain (cached per worker).
fn with_domain<T>(n1: u32, n2: u32, f: impl FnOnce(&Domain) -> T) -> T {
    let (n1, n2) = (n1 as usize, n2 as usize);
    DOMAIN.with(|d| {
        let mut d = d.borrow_mut();
        if d.as_ref().map(|x| (x.n1, x.n2)) != Some((n1, n2)) {
            *d = Domain::with_split(n1, n2, FftConfig::default().tile);
        }
        f(d.as_ref().expect("unsupported domain split"))
    })
}

/// Run `f` on `bytes` as field elements (copied through an aligned buffer: the
/// incoming bytes carry no alignment guarantee).
fn on_fr(bytes: &mut [u8], f: impl FnOnce(&mut [Fr])) {
    let mut v = vec![Fr::zero(); bytes.len() / 32];
    accel::fr_bytes_mut(&mut v).copy_from_slice(bytes);
    f(&mut v);
    bytes.copy_from_slice(accel::fr_bytes_mut(&mut v));
}

/// Worker kernel: whole rows `[first_row, …)` of a coset transform chain.
#[wasm_bindgen]
pub fn kernel_rows(rows: &mut [u8], n1: u32, n2: u32, first_row: u32, to_coset: bool) {
    with_domain(n1, n2, |d| {
        on_fr(rows, |v| {
            accel::kernel_rows(d, v, first_row as usize, to_coset)
        })
    })
}

/// Worker kernel: a row-major `N1 × b` column tile at column `c0`.
/// `op`: 0 = inverse + twiddle·(1/N), 1 = twiddle + forward.
#[wasm_bindgen]
pub fn kernel_cols(block: &mut [u8], n1: u32, n2: u32, c0: u32, op: u8) {
    let op = if op == 0 {
        ColOp::InversePost
    } else {
        ColOp::ForwardPre
    };
    with_domain(n1, n2, |d| {
        on_fr(block, |v| accel::kernel_cols(d, v, c0 as usize, op))
    })
}

/// Worker kernel: MSM over serialized points and 32-byte LE scalars; returns the
/// uncompressed affine sum.
#[wasm_bindgen]
pub fn kernel_msm(g2: bool, points: &[u8], compressed: bool, scalars: &[u8]) -> Vec<u8> {
    accel::kernel_msm(g2, points, compressed, scalars)
}

// ---- push-driven proving (key from a ReadableStream) -------------------------------

/// A proof waiting for proving-key bytes: created by [`begin_streaming_proof`],
/// fed with [`push`](Self::push) (e.g. each chunk of a `fetch` body), completed
/// with [`finish`](Self::finish). The key is never held — each chunk of points is
/// folded into its MSM and dropped — and the witness and quotient are computed
/// before the first byte is needed, so proving overlaps the download.
#[wasm_bindgen]
pub struct StreamingProof {
    inner: Option<xark_groth16::PushProver<Box<dyn ConstraintSource>>>,
    host: Host,
}

/// Start a push-driven proof. `options` as for [`prove_streaming`] (`r1cs`,
/// `pool`, `msmChunk`, `seed`).
#[wasm_bindgen(js_name = beginStreamingProof)]
pub fn begin_streaming_proof(
    circuit_xbc: &Bytes,
    inputs: JsValue,
    options: JsValue,
) -> Result<StreamingProof, js_sys::Error> {
    let xbc = to_bytes(circuit_xbc, "circuit.xbc")?;
    let vars = xark_ir::function_decode::decode_input_vars(&xbc);
    let ids = resolve_inputs(&vars, inputs).map_err(|e| js_error(&e))?;
    drop(vars);
    let src = row_source(&xbc, &options)?;
    let z = witness(&xbc, &ids, src.layout())?;
    let (cfg, r, s) = config(&options);
    let mut host = Host::from_options(&options);
    let inner =
        xark_groth16::PushProver::new(src, z, r, s, cfg, &mut host).map_err(mismatch_error)?;
    Ok(StreamingProof {
        inner: Some(inner),
        host,
    })
}

#[wasm_bindgen]
impl StreamingProof {
    /// Feed the next bytes of `pk.bin` (any chunk size, in order).
    pub fn push(&mut self, chunk: &[u8]) -> Result<(), js_sys::Error> {
        let inner = self
            .inner
            .as_mut()
            .ok_or_else(|| js_error("proof already finished"))?;
        inner.push(chunk, &mut self.host).map_err(mismatch_error)
    }

    /// Proving-key bytes consumed so far.
    #[wasm_bindgen(getter)]
    pub fn received(&self) -> f64 {
        self.inner.as_ref().map_or(0.0, |p| p.received() as f64)
    }

    /// Whether the whole key has arrived.
    #[wasm_bindgen(getter)]
    pub fn complete(&self) -> bool {
        self.inner.as_ref().is_some_and(|p| p.is_complete())
    }

    /// Assemble and self-verify the proof (after the whole key has been pushed).
    pub fn finish(&mut self) -> Result<ProofBundle, js_sys::Error> {
        let inner = self
            .inner
            .take()
            .ok_or_else(|| js_error("proof already finished"))?;
        let public = inner.public_inputs().to_vec();
        let proof = inner.finish().map_err(mismatch_error)?;
        encode_result(&proof, &public)
    }
}

// ---- key transcoding (compressed → uncompressed, for a decoded-key cache) ----------

/// Re-encodes a proving key with uncompressed points as it streams through:
/// `push(chunk)` returns the output produced so far. Store the result (OPFS,
/// IndexedDB, Cache API) and prove from it next time — every point read then
/// skips its square root, the dominant cost of a WASM proof. See
/// `js/stream.mjs` `transcodeKey`.
#[wasm_bindgen]
pub struct KeyTranscoder {
    inner: xark_groth16::transcode::KeyTranscoder,
    host: Host,
}

/// Start transcoding. `options.pool` decompresses on the worker pool.
#[wasm_bindgen(js_name = beginKeyTranscode)]
pub fn begin_key_transcode(options: JsValue) -> KeyTranscoder {
    KeyTranscoder {
        inner: xark_groth16::transcode::KeyTranscoder::new(1 << 16),
        host: Host::from_options(&options),
    }
}

#[wasm_bindgen]
impl KeyTranscoder {
    /// Feed the next bytes of `pk.bin`; returns the uncompressed bytes produced.
    pub fn push(&mut self, chunk: &[u8]) -> Result<Vec<u8>, js_sys::Error> {
        self.inner
            .push(chunk, &mut self.host)
            .map_err(|e| js_error(&format!("transcoding proving key: {e}")))?;
        Ok(self.inner.take_output())
    }

    /// Whether the whole key has been read.
    #[wasm_bindgen(getter)]
    pub fn complete(&self) -> bool {
        self.inner.is_complete()
    }
}

/// Worker kernel: re-encode compressed points uncompressed.
#[wasm_bindgen]
pub fn kernel_decompress(g2: bool, points: &[u8]) -> Result<Vec<u8>, js_sys::Error> {
    xark_groth16::transcode::decompress_points(g2, points).map_err(|e| js_error(&e))
}
