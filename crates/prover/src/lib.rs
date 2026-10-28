//! End-to-end Groth16 prover for the xark-lang IR.
//!
//! Consumes an [`R1csProgram`] plus a [`PrimitiveProgram`] (witness-gen hints),
//! runs the [`solver`] to produce the witness, and proves with `xark-groth16`
//! (Groth16 over BN254).

use std::collections::{BTreeMap, BTreeSet};

use ark_bn254::Bn254;
/// The prover's scalar field (BN254 `Fr`): what an input leaf's value is.
pub use ark_bn254::Fr;
use ark_ff::{PrimeField, Zero};
use num_bigint::{BigInt, Sign};
use xark_groth16::{Proof, VerifyingKey};

use xark_ir::SourceMap;
use xark_ir::primitive::{PrimitiveProgram, Var, VarRole};
use xark_ir::solver::{self, Fp};
use xark_ir::{FieldConst, LinearCombination as IrLc, R1csProgram, VarId, Visibility};

pub mod inputs;
pub use inputs::{InputValue, flatten_inputs, resolve_input_ids};

/// Developer-diagnostics env-flag probe. Only reads the environment under the
/// `debug` feature; a normal release build compiles this to `false` so the
/// diagnostic branches (and their `XARK_*` knobs) vanish entirely.
#[inline]
fn dbg_flag(name: &str) -> bool {
    #[cfg(feature = "debug")]
    {
        std::env::var(name).is_ok()
    }
    #[cfg(not(feature = "debug"))]
    {
        let _ = name;
        false
    }
}

/// BN254 scalar field modulus (decimal).
const BN254_MODULUS: &[u8] =
    b"21888242871839275222246405745257275088548364400416034343698204186575808495617";

/// Parse a (possibly negative) decimal `FieldConst` into an `Fr`, reduced mod p.
///
/// Returns `Err` with a descriptive message if `s` is not a valid decimal
/// integer. Use this on any constant that originates from untrusted input
/// (e.g. a deserialized R1CS); it never panics.
pub fn try_fr_from_decimal(s: &str) -> Result<Fr, String> {
    // Fast path: small integer constants (the vast majority — `0`, `±1`, `±2`,
    // small gadget constants) go straight to `Fr` with no `BigInt` allocation and
    // no modulus reduction (`Fr::from` handles sign + reduction natively). This is
    // the hot path when parsing every coefficient of an R1CS.
    let t = s.trim();
    if let Ok(n) = t.parse::<i64>() {
        let mag = Fr::from(n.unsigned_abs());
        return Ok(if n < 0 { -mag } else { mag });
    }
    let bi = BigInt::parse_bytes(t.as_bytes(), 10)
        .ok_or_else(|| format!("invalid decimal field constant: {s:?}"))?;
    // The modulus is a compile-time constant known to be a valid decimal.
    let modulus = BigInt::parse_bytes(BN254_MODULUS, 10).expect("BN254_MODULUS is a valid decimal");
    let mut r = bi % &modulus;
    if r.sign() == Sign::Minus {
        r += &modulus;
    }
    let (_, bytes) = r.to_bytes_le();
    Ok(Fr::from_le_bytes_mod_order(&bytes))
}

/// Infallible convenience wrapper over [`try_fr_from_decimal`] for *trusted*
/// decimals (constants this crate produced itself, e.g. solver witness output).
///
/// Panics if `s` is not a valid decimal — do not call it on untrusted input;
/// use [`try_fr_from_decimal`] there instead.
pub fn fr_from_decimal(s: &str) -> Fr {
    try_fr_from_decimal(s).expect("valid decimal")
}

/// Convert a [`FieldConst`] straight to `Fr`, skipping the `decimal()` round-trip:
/// the small-integer fast path goes direct, the big path reduces the stored
/// `BigInt`'s little-endian bytes (`from_le_bytes_mod_order`), avoiding a
/// `BigInt→String→BigInt` round-trip per coefficient. Infallible.
pub fn fr_from_fieldconst(fc: &FieldConst) -> Fr {
    if let Some(n) = fc.as_i64() {
        let mag = Fr::from(n.unsigned_abs());
        return if n < 0 { -mag } else { mag };
    }
    let (sign, bytes) = fc.big().to_bytes_le();
    let mag = Fr::from_le_bytes_mod_order(&bytes);
    if sign == Sign::Minus { -mag } else { mag }
}

/// A field-element input value — decimal or `0x`-hex (big-endian) — as its
/// decimal. It must already be a field element, `0 <= x < p`: a negative or
/// larger value is an error rather than silently reduced, since a value that
/// wraps (a 256-bit hash passed as a `Field`, say) would prove a different number
/// than the one written. Errors, never panics.
pub fn field_input_decimal(s: &str) -> Result<String, String> {
    let t = s.trim();
    let bi = match t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        Some("") => return Err(format!("empty hex value {s:?}")),
        Some(h) => BigInt::parse_bytes(h.as_bytes(), 16)
            .filter(|_| h.bytes().all(|b| b.is_ascii_hexdigit()))
            .ok_or_else(|| format!("invalid hex value {s:?}"))?,
        // Digits only (no `+` or `_`), as the input codec and the client read it; a
        // `-` goes on to be refused as below zero.
        None => Some(t)
            .filter(|t| {
                let d = t.strip_prefix('-').unwrap_or(t);
                !d.is_empty() && d.bytes().all(|b| b.is_ascii_digit())
            })
            .and_then(|t| BigInt::parse_bytes(t.as_bytes(), 10))
            .ok_or_else(|| format!("{s:?} is not a decimal or 0x-hex number"))?,
    };
    let modulus = BigInt::parse_bytes(BN254_MODULUS, 10).expect("BN254_MODULUS is a valid decimal");
    if bi.sign() == Sign::Minus || bi >= modulus {
        return Err(format!(
            "{s} is not a field element (0 <= x < p, p = {})",
            std::str::from_utf8(BN254_MODULUS).expect("ascii")
        ));
    }
    Ok(bi.to_str_radix(10))
}

/// Lower a solved witness (`VarId → Fp`) to Groth16 scalars (`VarId → Fr`).
pub fn lower_witness(assign_fp: &BTreeMap<VarId, Fp>) -> BTreeMap<VarId, Fr> {
    assign_fp
        .iter()
        .map(|(k, v)| {
            let fr = v
                .as_bn254_fr()
                .unwrap_or_else(|| fr_from_decimal(&v.to_decimal()));
            (*k, fr)
        })
        .collect()
}

/// A circuit over the xark-lang IR: our R1CS constraints plus a variable
/// assignment — the setup-minimized circuit Groth16 keys are made for, and the
/// witness to prove it with (`xark-groth16`'s `ProgramSource` over
/// [`Self::prog`], plus [`Self::assignment`]). Setup mode carries the
/// constraint shape only; proving mode adds the witness assignment.
#[derive(Clone)]
pub struct XarkCircuit {
    prog: R1csProgram,
    assign: BTreeMap<VarId, Fr>,
}

/// Minimize the R1CS (linear-variable elimination to a fixpoint). **Default ON**;
/// `XARK_NO_MINIMIZE` disables it. Both setup and
/// proving route through here so they see the *identical* deterministic circuit.
/// Elimination is Gaussian, so satisfiability is preserved exactly: the witness
/// `assign` (keyed by original ids, retained by surviving vars) stays valid, and
/// public-input ids/order are untouched.
fn maybe_minimize(prog: R1csProgram) -> R1csProgram {
    // The fill cap (`MAX_FILL_DEFAULT`, overridable via `XARK_MAX_FILL`) is
    // deliberately low: it does the cheap, strictly-shrinking eliminations and
    // stops before the dense substitutions that inflate the nonzero count (which is
    // what Groth16 setup/prove actually cost). An unguarded pass reduces a few more
    // constraints but explodes nonzeros on non-native circuits (secp256k1:
    // 6.6M→47M) and can OOM, so it is opt-in.
    if dbg_flag("XARK_NO_MINIMIZE") {
        return prog;
    }
    let timed = dbg_flag("XARK_BUILD_TIME") || dbg_flag("PROVE_TIME");
    let t = timed.then(std::time::Instant::now);
    let out = xark_ir::minimize::minimize(&prog);
    if let Some(t) = t {
        eprintln!(
            "MINIMIZE: {} -> {} constraints, {} -> {} vars ({:.2}s)",
            prog.constraints.len(),
            out.constraints.len(),
            prog.variables.len(),
            out.variables.len(),
            t.elapsed().as_secs_f64(),
        );
    }
    out
}

impl XarkCircuit {
    /// For Groth16 setup: only the constraint *shape* is needed (Arkworks calls
    /// the value closures only in proving mode), so the assignment is empty.
    pub fn for_setup(prog: R1csProgram) -> Self {
        Self {
            prog: maybe_minimize(prog),
            assign: BTreeMap::new(),
        }
    }

    /// For proving: the constraints plus the full solved witness (`VarId → Fr`).
    pub fn for_proving(prog: R1csProgram, assign: BTreeMap<VarId, Fr>) -> Self {
        Self {
            prog: maybe_minimize(prog),
            assign,
        }
    }

    /// For Groth16 setup from an **already-minimized** `prog` — skips
    /// `maybe_minimize`. Pair with [`Self::for_proving_preminimized`] so setup and
    /// prove use the *identical* circuit: re-running `maybe_minimize` here on a
    /// circuit the caller already minimized (possibly under a different `XARK_MAX_FILL`)
    /// could reduce it further and desync the proving key from the proof. The caller
    /// owns the minimization policy; both sides consume its exact result.
    pub fn for_setup_preminimized(prog: R1csProgram) -> Self {
        Self {
            prog,
            assign: BTreeMap::new(),
        }
    }

    /// For proving from an **already-minimized** `prog` — skips `maybe_minimize`, since re-running it would
    /// just reproduce the same fixpoint. The `prog` must be the exact minimized
    /// circuit the proving key was generated from.
    pub fn for_proving_preminimized(prog: R1csProgram, assign: BTreeMap<VarId, Fr>) -> Self {
        Self { prog, assign }
    }

    /// The witness values, by variable id (empty for a setup-only circuit).
    pub fn assignment(&self) -> &BTreeMap<VarId, Fr> {
        &self.assign
    }

    /// The (minimized) R1CS this circuit proves — exactly what its proving key
    /// is generated from.
    pub fn prog(&self) -> &R1csProgram {
        &self.prog
    }

    /// Public inputs in variable-id (allocation) order — the order Groth16
    /// verification expects.
    pub fn public_inputs(&self) -> Vec<Fr> {
        public_inputs(&self.prog, &self.assign)
    }

    /// Pre-flight validation of the program's field constants. Every constant
    /// and coefficient decimal in the R1CS is parsed; on the first malformed
    /// one this returns a descriptive `Err` instead of letting proving panic.
    ///
    /// Call this before handing a circuit built from *untrusted* input (e.g. a
    /// deserialized R1CS) to the Groth16 backend.
    pub fn validate(&self) -> Result<(), String> {
        validate_program_constants(&self.prog)
    }
}

/// Reject an R1CS program that would crash the prover, returning a descriptive
/// error. Used to fail gracefully on an untrusted program before proving.
fn validate_program_constants(prog: &R1csProgram) -> Result<(), String> {
    // Every term must reference a declared variable: the prover looks each one
    // up and would panic on a dangling id. Reject it here so a malformed
    // program is a clean error, not a crash. Coefficients need no
    // check: a `FieldConst` is already a validated field value (an invalid decimal
    // fails at deserialization), and `fr_from_fieldconst` reduces any value mod p.
    let valid_ids: BTreeSet<VarId> = prog.variables.iter().map(|v| v.id).collect();
    let check_lc = |lc: &IrLc| -> Result<(), String> {
        for t in &lc.terms {
            if !valid_ids.contains(&t.var) {
                return Err(format!(
                    "constraint references undefined variable id {}",
                    t.var
                ));
            }
        }
        Ok(())
    };
    for con in &prog.constraints {
        check_lc(&con.a)?;
        check_lc(&con.b)?;
        check_lc(&con.c)?;
    }
    Ok(())
}

/// Public inputs in variable-id order (the order they are allocated), which is
/// exactly the order Groth16 verification expects.
fn public_inputs(prog: &R1csProgram, assign: &BTreeMap<VarId, Fr>) -> Vec<Fr> {
    let mut order: Vec<_> = prog.variables.iter().collect();
    order.sort_by_key(|v| v.id);
    order
        .iter()
        .filter(|v| v.visibility == Visibility::Public)
        .map(|v| assign.get(&v.id).copied().unwrap_or_else(Fr::zero))
        .collect()
}

/// Solve the witness, run Groth16 setup + prove, and return the verifying key,
/// proof, and public inputs (so the caller can verify — possibly against
/// tampered public inputs).
///
/// **TEST / DEV ONLY.** Setup here uses a *fixed* RNG seed (`0`), so the Groth16
/// trapdoor is publicly known and any proof this produces is forgeable. It
/// exists for this crate's round-trip tests. Never use it — or any key it
/// generates — in production; the CLI `xark setup` (ptau / ceremony) and
/// `xark prove` (`OsRng`) path is the real one.
// The tuple return (verifying key, proof, public inputs) is the natural result
// shape for a test/dev prove helper; a named struct would not add clarity.
#[cfg(test)]
#[allow(clippy::type_complexity)]
fn prove_only(
    r1cs: &R1csProgram,
    circuit: &PrimitiveProgram,
    inputs: &BTreeMap<VarId, String>,
) -> Result<(VerifyingKey<Bn254>, Proof<Bn254>, Vec<Fr>), String> {
    // Reject a malformed R1CS program (bad decimal constant) up front with a
    // descriptive error, rather than panicking inside the prover.
    validate_program_constants(r1cs)?;
    let assign_fp = solver::solve_and_check(circuit, inputs)
        .map_err(|e| format!("witness does not satisfy the circuit: {e:?}"))?;
    let assign = lower_witness(&assign_fp);

    let public = public_inputs(r1cs, &assign);
    let (vk, proof) = dev_prove(&maybe_minimize(r1cs.clone()), &assign, 0)?;
    Ok((vk, proof, public))
}

/// Dev-mode Groth16 on `prog`: keys from a fixed `seed` (a known trapdoor), then a
/// proof for `assign`. The test round trip `prove_only` and
/// [`Circuit::prove_dev`] share.
fn dev_prove(
    prog: &R1csProgram,
    assign: &BTreeMap<VarId, Fr>,
    seed: u64,
) -> Result<(VerifyingKey<Bn254>, Proof<Bn254>), String> {
    use rand::SeedableRng;
    use xark_groth16::ConstraintSource;
    let src = xark_groth16::ProgramSource::new(prog);
    let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
    let mut pk = Vec::new();
    let vk = xark_groth16::setup::dev_setup(
        &src,
        &mut rng,
        &mut pk,
        ark_serialize::Compress::No,
        xark_groth16::DomainKind::Radix2,
    )
    .map_err(|e| format!("setup: {e}"))?;
    let mut pk = xark_groth16::SerializedPk::from_bytes(&pk).map_err(|e| format!("setup: {e}"))?;
    let z = src.layout().assignment(|id| assign.get(&id).copied());
    let proof = xark_groth16::prove(
        &src,
        &z,
        &mut pk,
        &mut rng,
        &xark_groth16::ProverConfig::default(),
    )
    .map_err(|e| format!("prove: {e}"))?;
    Ok((vk, proof))
}

/// Run the full pipeline: solve the witness from `inputs`, lower to Groth16, and
/// return whether the resulting proof verifies against the public inputs.
#[cfg(test)]
fn prove_and_verify(
    r1cs: &R1csProgram,
    circuit: &PrimitiveProgram,
    inputs: &BTreeMap<VarId, String>,
) -> Result<bool, String> {
    let (vk, proof, public) = prove_only(r1cs, circuit, inputs)?;
    xark_groth16::verify(&vk, &public, &proof).map_err(|e| format!("verify: {e}"))
}

// In-crate testing API: lets a circuit author unit-test with plain `cargo test`
// (via the `xark init` scaffold) — load the built artifacts, feed typed
// inputs, and get back whether a dev-mode Groth16 proof verifies.

/// A built circuit loaded from `target/xark/<name>/`, ready to prove against.
///
/// Obtain one with [`circuit`]; drive it with [`Circuit::prove`].
pub struct Circuit {
    /// The circuit name (for diagnostics), e.g. `<name>` in `target/xark/<name>/`.
    name: String,
    /// The artifact directory (`circuit.xbc`, and `pk.bin` once `xark setup` ran).
    dir: std::path::PathBuf,
    r1cs: R1csProgram,
    prim: PrimitiveProgram,
    /// Each constraint's source statement (`sources.json`, from every build), to
    /// explain *which* line a failing constraint came from.
    sources: Option<SourceMap>,
}

/// The error from [`Circuit::check`]: a human-readable, multi-line explanation
/// of why the witness does not satisfy the circuit (which constraint, and — when
/// built — its source line).
///
/// Its `Debug` delegates to `Display`, so `c.check(..).unwrap()` prints the
/// message verbatim (with real newlines) instead of an escaped one-liner — the
/// panic message points straight at the offending line.
pub struct ProveError(pub String);

impl std::fmt::Display for ProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::fmt::Debug for ProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Leading newline so `unwrap()`'s `… on an Err value:` prefix doesn't run
        // into the first line of the explanation.
        write!(f, "\n{}", self.0)
    }
}

impl std::error::Error for ProveError {}

/// Typed inputs for [`Circuit::check`]/[`Circuit::prove`], generated by
/// `#[circuit]` from the entry signature.
///
/// Each declared parameter becomes one `(leaf-name, value)` pair per input leaf it
/// occupies, written by the parameter type's `xark::Input` impl: a scalar
/// `Private<Field>` is a single leaf (`k`); a `Private<[u8; 56]>` is 56 byte leaves
/// (`input[0]`, …); a `Public<Hash>` its two halves (`digest.hi`, `digest.lo`).
/// `Circuit::resolve_inputs` matches each name to its variable.
pub trait ProveInputs {
    fn into_inputs(self) -> Vec<(String, Fr)>;
}

/// The "circuit not built" failure: an actionable message with the fix command
/// on its own line. Colorized (brand green for the command, red for the header)
/// when stderr is a terminal, matching the `xark` CLI palette; plain text when
/// piped or `NO_COLOR` is set, so CI logs stay readable.
fn not_built_message(name: &str, xbc_path: &std::path::Path) -> String {
    let color = {
        use std::io::IsTerminal;
        std::env::var_os("NO_COLOR").is_none()
            && (std::env::var_os("CLICOLOR_FORCE").is_some() || std::io::stderr().is_terminal())
    };
    let (err, brand, dim, reset) = if color {
        (
            "\x1b[1;38;2;255;85;85m", // red — the problem
            "\x1b[1;38;2;153;255;0m", // brand green — the command
            "\x1b[2m",                // faint — the aside
            "\x1b[0m",
        )
    } else {
        ("", "", "", "")
    };
    format!(
        "\n\
         {err}circuit `{name}` has not been built.{reset}\n\n\
         \x20 build it first:\n\n\
         \x20     {brand}xark build{reset}\n\n\
         \x20 {dim}then re-run the test — or use `xark test`, which builds then tests.{reset}\n\
         \x20 {dim}expected: {}{reset}\n",
        xbc_path.display()
    )
}

/// Best-effort auto-build: when a `#[circuit]` test finds its circuit missing,
/// run the `xark` CLI (`$XARK`, else `xark` on `PATH`) to build it in place.
/// Silently no-ops if `xark` isn't reachable or the build fails. Fires when the
/// artifact is absent, older than the crate's sources ([`newer_source`]), or built over
/// another field ([`other_field`]).
fn try_autobuild(dir: &std::path::Path) {
    // Serialize across the test binary's threads: parallel `#[circuit]` tests
    // would otherwise each launch a build and race on the output files. After
    // taking the lock, re-check — another thread may have just built it.
    static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let _guard = LOCK.lock().unwrap_or_else(|e| e.into_inner());
    if dir.join("circuit.xbc").exists() && newer_source(dir).is_none() && other_field(dir).is_none()
    {
        return;
    }
    let crate_dir = dir
        .ancestors()
        .nth(3)
        .filter(|p| !p.as_os_str().is_empty())
        .map(std::path::Path::to_path_buf)
        .unwrap_or_else(|| std::path::PathBuf::from("."));
    let xark = std::env::var("XARK").unwrap_or_else(|_| "xark".to_string());
    // A CLI from another release would build a circuit this prover can't read (or
    // fail on the source outright): say so instead of running it.
    if let Some(found) = cli_version(&xark)
        && !xark_ir::same_release(&found, env!("CARGO_PKG_VERSION"))
    {
        eprintln!(
            "warning: not rebuilding {}: `{xark}` is xark {found}, but this is xark-prover {}. \
             Install the matching CLI (`cargo install xark-cli --version {}`), or point \
             $XARK at one.",
            crate_dir.display(),
            env!("CARGO_PKG_VERSION"),
            env!("CARGO_PKG_VERSION"),
        );
        return;
    }
    let _ = std::process::Command::new(xark)
        .arg("build")
        .arg(&crate_dir)
        .status();
}

/// `xark --version`'s version (`xark 0.3.0 (…)` → `0.3.0`); `None` if it can't run.
fn cli_version(xark: &str) -> Option<String> {
    let out = std::process::Command::new(xark)
        .arg("--version")
        .output()
        .ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    text.split_whitespace().nth(1).map(str::to_string)
}

/// The field `circuit.xbc` in `dir` was built over, when it isn't BN254 (`xark build
/// --field 7`): Rust tests check the BN254 circuit, so that build is rebuilt.
fn other_field(dir: &std::path::Path) -> Option<String> {
    let bytes = std::fs::read(dir.join("circuit.xbc")).ok()?;
    xark_ir::function_decode::stream_field(&bytes)
        .filter(|f| f.name != "bn254")
        .map(|f| f.modulus_decimal)
}

/// A source the circuit came from changed since `circuit.xbc` in
/// `<crate>/target/xark/<name>/` was built — `cargo test` after an edit, without
/// `xark test` or `xark build`.
fn newer_source(dir: &std::path::Path) -> Option<std::path::PathBuf> {
    newer_source_than(dir, "circuit.xbc")
}

/// A source the circuit came from that changed since `artifact` (`circuit.xbc`,
/// `profile.json`) in the build directory `dir` was written: a file `xark build`
/// listed in `deps` (the crate's own and its path dependencies', gadgets included),
/// the crate's `Cargo.toml`, or anything under its `src/`. `None` also when
/// `artifact` is missing: check it exists first.
pub fn newer_source_than(dir: &std::path::Path, artifact: &str) -> Option<std::path::PathBuf> {
    let built = std::fs::metadata(dir.join(artifact))
        .and_then(|m| m.modified())
        .ok()?;
    let changed = |p: &std::path::Path| {
        // A listed file that is gone changed too (moved, or a module removed).
        std::fs::metadata(p)
            .and_then(|m| m.modified())
            .map_or(true, |t| t > built)
    };
    if let Ok(deps) = std::fs::read_to_string(dir.join("deps"))
        && let Some(p) = deps
            .lines()
            .filter(|l| !l.is_empty())
            .map(std::path::Path::new)
            .find(|p| changed(p))
    {
        return Some(p.to_path_buf());
    }
    let xark = dir.parent()?;
    let target = xark.parent()?;
    if xark.file_name()? != "xark" || target.file_name()? != "target" {
        return None;
    }
    let krate = target.parent()?;
    let newer = |p: &std::path::Path| {
        std::fs::metadata(p)
            .and_then(|m| m.modified())
            .is_ok_and(|t| t > built)
    };
    let manifest = krate.join("Cargo.toml");
    if newer(&manifest) {
        return Some(manifest);
    }
    let mut stack = vec![krate.join("src")];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).into_iter().flatten().flatten() {
            let (p, ty) = (e.path(), e.file_type());
            if ty.as_ref().is_ok_and(|t| t.is_dir()) {
                stack.push(p);
            } else if newer(&p) {
                return Some(p);
            }
        }
    }
    None
}

/// Load a circuit built by `xark build` from `target/xark/<name>/`, relative to
/// the current directory (where `cargo test` runs, i.e. the crate root).
///
/// Missing or out-of-date artifacts trigger a best-effort `try_autobuild`; if
/// that can't run, a missing circuit panics with a clear message (run `xark
/// build` first) and an out-of-date one is used with a warning.
pub fn circuit(name: &str) -> Circuit {
    circuit_at(std::path::Path::new("target/xark").join(name))
}

/// Load a circuit from an explicit artifact directory (`<dir>/circuit.xbc`).
/// [`circuit`] is the sugar for the conventional `target/xark/<name>/` location.
/// The circuit name (for diagnostics) is the directory's final component.
pub fn circuit_at(dir: impl AsRef<std::path::Path>) -> Circuit {
    let dir = dir.as_ref();
    let name = dir
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("circuit")
        .to_string();
    let xbc_path = dir.join("circuit.xbc");

    // The common failures are "forgot to build" and "edited since the build".
    // Try a best-effort auto-build so `cargo test` on a `#[circuit]` example
    // tests what's in `src/`; if that can't run (no
    // `xark` on `PATH`/`$XARK`), fall through to the clear "run `xark build`"
    // guidance rather than a raw file/parse error from deeper in the load.
    if !xbc_path.exists() || newer_source(dir).is_some() || other_field(dir).is_some() {
        try_autobuild(dir);
    }
    if !xbc_path.exists() {
        panic!("{}", not_built_message(&name, &xbc_path));
    }
    if let Some(p) = other_field(dir) {
        panic!(
            "{} was built over another field ({p}), and couldn't be rebuilt: Rust tests \
             check the BN254 circuit. Run `xark build` (no `--field`), or `xark test`.",
            xbc_path.display()
        );
    }
    if let Some(src) = newer_source(dir) {
        eprintln!(
            "warning: {} changed since {} was built, and it couldn't be rebuilt; testing \
             the previous build. Run `xark test` instead.",
            src.display(),
            xbc_path.display()
        );
    }

    // `circuit.xbc` is self-contained: expanding it once yields both the
    // solver's primitive view and the backend's R1CS.
    let bytes =
        std::fs::read(&xbc_path).unwrap_or_else(|e| panic!("reading {}: {e}", xbc_path.display()));
    let cp = xark_ir::function_decode::expand_function_blob(&bytes)
        .unwrap_or_else(|e| panic!("expanding {}: {e}", xbc_path.display()));
    let (prim, r1cs) = (cp.to_primitive(), cp.to_r1cs());
    // Best-effort: each constraint's source line. Absent (an older build) or
    // malformed → `None`; the failure diagnostic then names only the constraint.
    let sources = SourceMap::load(dir);
    Circuit {
        name,
        dir: dir.to_path_buf(),
        r1cs,
        prim,
        sources,
    }
}

/// A Groth16 proof and its public inputs, as the canonical compressed bytes
/// `xark prove` writes (`proof.bin`, `public_inputs.bin`): what `xark verify`,
/// xark-wasm's `verify` and `xark export`'s verifier tests consume.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitProof {
    pub proof: Vec<u8>,
    pub public_inputs: Vec<u8>,
}

/// The constraint rows a proving key was made for, picked from the key's
/// `a_len`: the circuit as built (a `reduced` key, streamed from `xbc`) or its
/// minimized form (`minimized`). `cached` is the `r1cs.stream` `xark setup` writes
/// beside a minimized key; it is used when it belongs to this `xbc`, and the
/// minimize is redone otherwise.
pub fn rows_for_key(
    xbc: &[u8],
    a_len: usize,
    cached: Option<Vec<u8>>,
) -> Result<Box<dyn xark_groth16::ConstraintSource>, String> {
    use sha2::Digest;
    use xark_groth16::ConstraintSource;
    let src =
        xark_groth16::BytecodeSource::new(xbc).map_err(|e| format!("parsing circuit.xbc: {e}"))?;
    if src.layout().num_vars() == a_len {
        return Ok(Box::new(src));
    }
    drop(src);
    let fingerprint: String = sha2::Sha256::digest(xbc)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    if let Some(rows) = cached
        && let Ok(src) = xark_groth16::RowFileSource::new(rows)
        && xark_ir::function_decode::row_file_fits(src.file().fingerprint(), &fingerprint, xbc)
    {
        return Ok(Box::new(src));
    }
    let reduced = xark_ir::function_decode::expand_function_blob_reduced(xbc)
        .map_err(|e| format!("parsing circuit.xbc: {e}"))?
        .into_r1cs();
    let circuit = XarkCircuit::for_setup(reduced);
    let digest = xark_ir::function_decode::stream_digest_hex(xbc);
    let rows = xark_ir::r1cs_stream::encode(&digest, circuit.prog());
    drop(circuit);
    Ok(Box::new(
        xark_groth16::RowFileSource::new(rows).map_err(|e| format!("r1cs: {e}"))?,
    ))
}

impl Circuit {
    /// [`solver::solve_and_check_recorded`] under this circuit's name.
    fn solve_and_check(
        &self,
        id_inputs: &BTreeMap<VarId, String>,
    ) -> Result<BTreeMap<VarId, Fp>, solver::SolveError> {
        solver::solve_and_check_recorded(&self.name, &self.prim, id_inputs)
    }

    /// Resolve the typed `inputs` into `VarId → decimal` for the solver.
    ///
    /// Panics on a name that isn't a declared input, or a count mismatch — those
    /// are test-authoring bugs (the generated `<Fn>Inputs` struct can't produce
    /// them), so failing loudly is correct. A value that isn't a field element
    /// (`0 <= x < p`) is an `Err`: it would otherwise wrap to a different number.
    fn resolve_inputs<I: ProveInputs>(
        &self,
        inputs: I,
    ) -> Result<BTreeMap<VarId, String>, ProveError> {
        let input_vars: Vec<&Var> = self
            .prim
            .vars
            .iter()
            .filter(|v| matches!(v.role, VarRole::PublicInput | VarRole::PrivateInput))
            .collect();
        let by_name: BTreeMap<&str, VarId> =
            input_vars.iter().map(|v| (v.name.as_str(), v.id)).collect();
        let names = || {
            input_vars
                .iter()
                .map(|v| v.name.as_str())
                .collect::<Vec<_>>()
        };

        let pairs = inputs.into_inputs();
        if pairs.len() != input_vars.len() {
            panic!(
                "circuit expects {} input leaf(s) {:?}, got {}",
                input_vars.len(),
                names(),
                pairs.len()
            );
        }
        let mut id_inputs: BTreeMap<VarId, String> = BTreeMap::new();
        for (name, val) in pairs {
            let Some(&id) = by_name.get(name.as_str()) else {
                panic!("unknown circuit input `{name}`; expected {:?}", names());
            };
            id_inputs.insert(id, ark_ff::PrimeField::into_bigint(val).to_string());
        }
        Ok(id_inputs)
    }

    /// Check that `inputs` **satisfy the circuit**: solve the witness and verify it
    /// meets every constraint. Returns `Ok(())`, or an actionable `Err` naming the
    /// first failing constraint (and its source line).
    ///
    /// The fast, everyday circuit test — a satisfying witness *is* the proof the
    /// relation holds, so the positive test is `c.check(good).unwrap()` and the
    /// negative test is `assert!(c.check(bad).is_err())`. It deliberately does
    /// **not** run Groth16 (that exercises the backend, not the circuit); use
    /// [`Self::prove`] for the full pipeline. Panics only on malformed `inputs`.
    pub fn check<I: ProveInputs>(&self, inputs: I) -> Result<(), ProveError> {
        let id_inputs = self.resolve_inputs(inputs)?;
        // An unsatisfiable witness means the stated relation is false; explain
        // *which* constraint (and its source line)
        // failed, via the shared diagnostic.
        self.solve_and_check(&id_inputs).map_err(|e| {
            ProveError(xark_ir::diagnose::describe_unsatisfied(
                &e,
                &self.r1cs,
                self.sources.as_ref(),
            ))
        })?;
        Ok(())
    }

    /// [`Self::check`], and also that the inputs leave no witness variable free:
    /// [`solver::analyze_underconstrained`] finds no variable that could take a
    /// second value with everything else fixed. A necessary soundness check (it
    /// catches the common "forgot to constrain a hint" bug, not every
    /// under-constraint); use it on a few representative inputs.
    pub fn check_constrained<I: ProveInputs>(&self, inputs: I) -> Result<(), ProveError> {
        let id_inputs = self.resolve_inputs(inputs)?;
        let assign = self.solve_and_check(&id_inputs).map_err(|e| {
            ProveError(xark_ir::diagnose::describe_unsatisfied(
                &e,
                &self.r1cs,
                self.sources.as_ref(),
            ))
        })?;
        let holes = solver::analyze_underconstrained(&self.prim, &assign);
        if holes.is_empty() {
            return Ok(());
        }
        let list: Vec<String> = holes
            .iter()
            .take(8)
            .map(|h| format!("  `{}`: {}", h.name, h.reason))
            .collect();
        Err(ProveError(format!(
            "{} witness variable(s) are under-constrained:\n{}",
            holes.len(),
            list.join("\n")
        )))
    }

    /// Prove `inputs` with the built circuit and its proving key
    /// (`<dir>/pk.bin`, from `xark setup`) and return the proof — the same
    /// streaming prover and the same bytes as `xark prove`, without the CLI. The
    /// inputs are checked first, with the same diagnostics as [`Self::check`].
    pub fn prove<I: ProveInputs>(&self, inputs: I) -> Result<CircuitProof, ProveError> {
        self.prove_with_key(self.dir.join("pk.bin"), inputs)
    }

    /// [`Self::prove`] with a proving key from elsewhere (e.g. a ceremony's
    /// `proving_key.bin`).
    pub fn prove_with_key<I: ProveInputs>(
        &self,
        pk_path: impl AsRef<std::path::Path>,
        inputs: I,
    ) -> Result<CircuitProof, ProveError> {
        use ark_serialize::CanonicalSerialize;
        use xark_groth16::PkSource;
        let pk_path = pk_path.as_ref();
        let id_inputs = self.resolve_inputs(inputs)?;
        let assign = self.solve_and_check(&id_inputs).map_err(|e| {
            ProveError(xark_ir::diagnose::describe_unsatisfied(
                &e,
                &self.r1cs,
                self.sources.as_ref(),
            ))
        })?;
        let fail = |what: &str, e: &dyn std::fmt::Display| {
            ProveError(format!("circuit `{}`: {what}: {e}", self.name))
        };
        let xbc_path = self.dir.join("circuit.xbc");
        let xbc = std::fs::read(&xbc_path)
            .map_err(|e| fail(&format!("reading {}", xbc_path.display()), &e))?;
        let mut pk = xark_groth16::SerializedPk::open(pk_path).map_err(|e| {
            fail(
                &format!(
                    "reading proving key {} (run `xark setup` first?)",
                    pk_path.display()
                ),
                &e,
            )
        })?;
        let cached = std::fs::read(pk_path.with_file_name("r1cs.stream")).ok();
        let src = rows_for_key(&xbc, pk.header().a_len, cached).map_err(|e| fail("rows", &e))?;
        let z = src.layout().assignment(|id| {
            assign.get(&id).map(|v| {
                v.as_bn254_fr()
                    .unwrap_or_else(|| fr_from_decimal(&v.to_decimal()))
            })
        });
        let proof = xark_groth16::prove(
            &*src,
            &z,
            &mut pk,
            &mut rand::rngs::OsRng,
            &xark_groth16::ProverConfig::default(),
        )
        .map_err(|e| fail("proving", &e))?;
        let public: Vec<Fr> = z[1..src.layout().num_instance()].to_vec();
        let mut out = CircuitProof {
            proof: Vec::new(),
            public_inputs: Vec::new(),
        };
        proof
            .serialize_compressed(&mut out.proof)
            .map_err(|e| fail("encoding the proof", &e))?;
        public
            .serialize_compressed(&mut out.public_inputs)
            .map_err(|e| fail("encoding the public inputs", &e))?;
        Ok(out)
    }

    /// The whole proving pipeline on throwaway keys — solve the witness, then a
    /// real (dev-mode, seed 1) Groth16 setup + prove + verify — with no `xark
    /// setup` needed. Returns `Ok(())` when the proof verifies, or an actionable
    /// `Err`: an unsatisfiable witness, or — past that — a genuine circuit/backend
    /// inconsistency. For a test that the circuit proves at all; [`Self::prove`]
    /// makes a proof you keep. Runs in seconds only in `--release`.
    pub fn prove_dev<I: ProveInputs>(&self, inputs: I) -> Result<(), ProveError> {
        let id_inputs = self.resolve_inputs(inputs)?;
        let assign_fp = self.solve_and_check(&id_inputs).map_err(|e| {
            ProveError(xark_ir::diagnose::describe_unsatisfied(
                &e,
                &self.r1cs,
                self.sources.as_ref(),
            ))
        })?;
        let assign = lower_witness(&assign_fp);

        let public = public_inputs(&self.r1cs, &assign);

        // Past here the witness satisfies every constraint, so any backend
        // failure is a genuine circuit/backend inconsistency, not a false
        // statement — surface it rather than swallowing it into a bare `false`.
        let (vk, proof) = dev_prove(&maybe_minimize(self.r1cs.clone()), &assign, 1)
            .map_err(|e| ProveError(format!("circuit `{}` solved but {e}", self.name)))?;
        match xark_groth16::verify(&vk, &public, &proof) {
            Ok(true) => Ok(()),
            Ok(false) | Err(_) => Err(ProveError(format!(
                "circuit `{}` has a satisfying witness but its proof did not verify — the R1CS \
                 and the witness generator disagree",
                self.name
            ))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use xark_ir::primitive::{Expression, MulTerm, Var, VarRole, WitnessGen};
    use xark_ir::r1cs::{DebugInfo, R1csConstraint};
    use xark_ir::{FieldConst, LinearCombination as Lc, Variable as IrVar};

    #[test]
    fn field_strings_read_as_the_codec_reads_them() {
        for s in ["27", " 27 ", "0x1b", "0X1B"] {
            assert_eq!(field_input_decimal(s).unwrap(), "27", "{s}");
        }
        for s in ["+27", "1_000", "-1", "", "0x", "0x1g", "27.0"] {
            assert!(field_input_decimal(s).is_err(), "{s:?} was accepted");
        }
    }

    // Circuit: prove `out == a * b` for public `out`, private `a`, `b`.
    // Derived `t = a*b` (witness-gen Product), pinned by `a·b = t` and `t = out`.
    fn demo() -> (R1csProgram, PrimitiveProgram) {
        let vars_r = vec![
            IrVar {
                id: 0,
                name: "a".into(),
                visibility: Visibility::Private,
            },
            IrVar {
                id: 1,
                name: "b".into(),
                visibility: Visibility::Private,
            },
            IrVar {
                id: 2,
                name: "out".into(),
                visibility: Visibility::Public,
            },
            IrVar {
                id: 3,
                name: "t".into(),
                visibility: Visibility::Internal,
            },
        ];
        let one = FieldConst::from_i64(1);
        let neg1 = FieldConst::from_i64(-1);
        let constraints = vec![
            // a * b = t
            R1csConstraint {
                id: 0,
                a: Lc::var(0),
                b: Lc::var(1),
                c: Lc::var(3),
                debug: None::<DebugInfo>,
            },
            // (t - out) * 1 = 0
            R1csConstraint {
                id: 1,
                a: Lc {
                    constant: FieldConst::from_i64(0),
                    terms: vec![
                        xark_ir::Term {
                            coeff: one.clone(),
                            var: 3,
                        },
                        xark_ir::Term {
                            coeff: neg1.clone(),
                            var: 2,
                        },
                    ],
                },
                b: Lc::one(),
                c: Lc::zero(),
                debug: None::<DebugInfo>,
            },
        ];
        let r1cs = R1csProgram {
            field: xark_ir::FieldSpec {
                name: "bn254".into(),
                modulus_decimal: Some(String::from_utf8(BN254_MODULUS.to_vec()).unwrap()),
            },
            variables: vars_r,
            constraints,
        };
        let prim = PrimitiveProgram {
            field: xark_ir::primitive::FieldSpec::bn254(),
            vars: vec![
                Var {
                    id: 0,
                    name: "a".into(),
                    role: VarRole::PrivateInput,
                },
                Var {
                    id: 1,
                    name: "b".into(),
                    role: VarRole::PrivateInput,
                },
                Var {
                    id: 2,
                    name: "out".into(),
                    role: VarRole::PublicInput,
                },
                Var {
                    id: 3,
                    name: "t".into(),
                    role: VarRole::Derived,
                },
            ],
            constraints: vec![
                Expression {
                    mul_terms: vec![MulTerm {
                        coeff: FieldConst::from_i64(1),
                        left: 0,
                        right: 1,
                    }],
                    linear_terms: vec![xark_ir::primitive::LinearTerm {
                        coeff: FieldConst::from_i64(-1),
                        var: 3,
                    }],
                    constant: FieldConst::from_i64(0),
                    note: None,
                },
                Expression {
                    mul_terms: vec![],
                    linear_terms: vec![
                        xark_ir::primitive::LinearTerm {
                            coeff: FieldConst::from_i64(1),
                            var: 3,
                        },
                        xark_ir::primitive::LinearTerm {
                            coeff: FieldConst::from_i64(-1),
                            var: 2,
                        },
                    ],
                    constant: FieldConst::from_i64(0),
                    note: None,
                },
            ],
            witness_gen: vec![WitnessGen::Product {
                out: 3,
                left: Lc::var(0),
                right: Lc::var(1),
            }],
        };
        (r1cs, prim)
    }

    #[test]
    fn validate_rejects_dangling_variable() {
        // A term referencing an undeclared variable id would panic in the
        // prover; validation must reject it cleanly.
        let (mut r1cs, _) = demo();
        r1cs.constraints[1].a.terms.push(xark_ir::Term {
            coeff: FieldConst::from_i64(1),
            var: 99,
        });
        let circuit = XarkCircuit::for_setup(r1cs);
        let err = circuit
            .validate()
            .expect_err("a dangling variable id must be rejected");
        assert!(err.contains("undefined variable id 99"), "got: {err}");
    }

    #[test]
    fn proves_and_verifies_valid_witness() {
        let (r1cs, prim) = demo();
        let mut inputs = BTreeMap::new();
        inputs.insert(0u32, "3".to_string());
        inputs.insert(1u32, "4".to_string());
        inputs.insert(2u32, "12".to_string()); // out = 3*4
        assert!(prove_and_verify(&r1cs, &prim, &inputs).unwrap());
    }

    #[test]
    fn tampered_public_input_fails_verification() {
        // Prove a valid statement (out = 3*4 = 12), then verify the proof
        // against a tampered public input (13) — must be rejected.
        let (r1cs, prim) = demo();
        let mut inputs = BTreeMap::new();
        inputs.insert(0u32, "3".to_string());
        inputs.insert(1u32, "4".to_string());
        inputs.insert(2u32, "12".to_string());
        let (vk, proof, public) = prove_only(&r1cs, &prim, &inputs).unwrap();
        assert!(xark_groth16::verify(&vk, &public, &proof).unwrap());

        let tampered = vec![public[0] + Fr::from(1u64)];
        assert!(!xark_groth16::verify(&vk, &tampered, &proof).unwrap());
    }

    #[test]
    fn try_fr_from_decimal_rejects_garbage() {
        assert!(try_fr_from_decimal("123").is_ok());
        assert!(try_fr_from_decimal("-7").is_ok());
        assert!(try_fr_from_decimal("not a number").is_err());
        assert!(try_fr_from_decimal("").is_err());
        assert!(try_fr_from_decimal("0x1f").is_err());
    }

    #[test]
    fn malformed_field_constant_is_rejected_not_panicked() {
        // A non-numeric coefficient is now *unrepresentable*: `FieldConst` holds
        // an `i64`/`BigInt`, so the prove path can never receive a malformed
        // constant. The guard lives at construction / deserialization — parsing a
        // bad constant must Err, not panic or silently corrupt.
        assert!(FieldConst::from_decimal("garbage").is_none());
        let err = serde_json::from_str::<FieldConst>("\"garbage\"").unwrap_err();
        assert!(
            err.to_string().contains("invalid field constant"),
            "unexpected error: {err}"
        );
    }
}
