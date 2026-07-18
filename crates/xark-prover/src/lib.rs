//! End-to-end Groth16 prover for the xark-lang IR.
//!
//! Consumes an [`R1csProgram`] (our `a·b = c` constraint form) plus a
//! [`PrimitiveProgram`] (the witness-generation hint program), runs the
//! reference [`solver`] to produce the full witness, lowers the constraints into
//! Arkworks `gr1cs`, and runs the exact Groth16/BN254 stack the `xark` backend
//! uses (ark 0.6). This closes the loop: a Rust circuit → MIR → xark-IR → R1CS →
//! a *verified* Groth16 proof, entirely within xark's own pipeline.

use std::collections::{BTreeMap, BTreeSet};

use ark_bn254::{Bn254, Fr};
use ark_ff::{PrimeField, Zero};
use ark_groth16::{Groth16, Proof, VerifyingKey};
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, SynthesisError, Variable,
};
use ark_snark::SNARK;
use num_bigint::{BigInt, Sign};

use xark_ir::primitive::{PrimitiveProgram, Var, VarRole};
use xark_ir::profile::ProfileProgram;
use xark_ir::solver;
use xark_ir::{FieldConst, LinearCombination as IrLc, R1csProgram, VarId, Visibility};

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
/// (e.g. a deserialized `r1cs.json`); it never panics.
pub fn try_fr_from_decimal(s: &str) -> Result<Fr, String> {
    // Fast path: small integer constants (the vast majority — `0`, `±1`, `±2`,
    // small gadget constants) go straight to `Fr` with no `BigInt` allocation and
    // no modulus reduction (`Fr::from` handles sign + reduction natively). This is
    // the hot path in both `validate_program_constants` and the constraint
    // synthesizer, which parse every R1CS coefficient.
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

/// Convert a [`FieldConst`] straight to `Fr`, skipping the decimal string that the
/// `fr_from_decimal(&fc.decimal())` path formats and reparses. The small-integer
/// fast path (the vast majority of coefficients) matches [`try_fr_from_decimal`];
/// the big path reduces the stored `BigInt`'s little-endian bytes directly
/// (`from_le_bytes_mod_order` handles the mod-p reduction). The Groth16 synthesizer
/// parses *every* coefficient of a dense minimized R1CS at both setup and prove, so
/// eliminating the `BigInt→String→BigInt` round-trip is the dominant synthesis
/// speedup. Infallible — a `FieldConst` is already a validated field value.
pub fn fr_from_fieldconst(fc: &FieldConst) -> Fr {
    if let Some(n) = fc.as_i64() {
        let mag = Fr::from(n.unsigned_abs());
        return if n < 0 { -mag } else { mag };
    }
    let (sign, bytes) = fc.big().to_bytes_le();
    let mag = Fr::from_le_bytes_mod_order(&bytes);
    if sign == Sign::Minus {
        -mag
    } else {
        mag
    }
}

/// Parse a `0x`-prefixed hex value as a field element (big-endian, reduced mod p)
/// and return its canonical decimal — for `--inputs` values written in hex.
/// Errors (never panics) on a missing prefix or a non-hex body.
pub fn hex_to_field_decimal(s: &str) -> Result<String, String> {
    let h = s
        .strip_prefix("0x")
        .or_else(|| s.strip_prefix("0X"))
        .ok_or_else(|| format!("expected a 0x-prefixed hex value, got {s:?}"))?;
    if h.is_empty() {
        return Err(format!("empty hex value {s:?}"));
    }
    let bi =
        BigInt::parse_bytes(h.as_bytes(), 16).ok_or_else(|| format!("invalid hex value {s:?}"))?;
    let modulus = BigInt::parse_bytes(BN254_MODULUS, 10).expect("BN254_MODULUS is a valid decimal");
    let mut r = bi % &modulus;
    if r.sign() == Sign::Minus {
        r += &modulus;
    }
    Ok(r.to_str_radix(10))
}

/// A synthesizable circuit over the xark-lang IR: our R1CS constraints plus a
/// variable assignment. Implements Arkworks `gr1cs` [`ConstraintSynthesizer`],
/// so it drops directly into the `xark` backend's generic `setup_from_ptau` /
/// `Groth16::prove` / `verify` — a generic Groth16 over the constraint system.
/// Supports both setup mode
/// (constraint shape only) and proving mode (with the witness assignment).
#[derive(Clone)]
pub struct XarkCircuit {
    prog: R1csProgram,
    assign: BTreeMap<VarId, Fr>,
}

/// Minimize the R1CS (linear-variable elimination to a fixpoint). **Default ON**;
/// `XARK_NO_MINIMIZE` (the `--no-minimize` flag) disables it. Both setup and
/// proving route through here, so both see the *identical* deterministic minimized
/// circuit — keys and proof stay consistent. Elimination is Gaussian, so
/// satisfiability is preserved exactly: the witness `assign` (keyed by original
/// ids, which surviving vars retain) remains a valid superset, and public-input
/// ids/order are untouched.
fn maybe_minimize(prog: R1csProgram) -> R1csProgram {
    // Three modes, chosen the same way in setup and proving so both see the
    // identical circuit:
    //  * default — the input is the per-template-reduced R1CS; run an *unguarded*
    //    boundary pass that eliminates the remaining cross-template plug
    //    materializations, reaching the same fixpoint as a full flat minimize
    //    (bounded, because every dense elimination was already done within a small
    //    template body).
    //  * `XARK_FLAT_MINIMIZE` — the input is the full (unreduced) expansion; run the
    //    *guarded* flat minimizer (fill cap, `XARK_MAX_FILL`) so a raw dense circuit
    //    can't cascade into a superlinear blowup.
    //  * `XARK_NO_MINIMIZE` — skip entirely.
    if dbg_flag("XARK_NO_MINIMIZE") {
        return prog;
    }
    let flat = dbg_flag("XARK_FLAT_MINIMIZE");
    let t = std::time::Instant::now();
    let out = if flat {
        xark_ir::minimize::minimize(&prog)
    } else {
        xark_ir::minimize::minimize_with_fill(&prog, usize::MAX)
    };
    // Reduction stats are diagnostic noise on a normal run; show them only under
    // the setup/prove timing flags.
    if dbg_flag("XARK_BUILD_TIME") || dbg_flag("PROVE_TIME") {
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

    /// For proving from an **already-minimized** `prog` (e.g. `xark setup`'s
    /// cached minimized R1CS) — skips `maybe_minimize`, since re-running it would
    /// just reproduce the same fixpoint. The `prog` must be the exact minimized
    /// circuit the proving key was generated from.
    pub fn for_proving_preminimized(prog: R1csProgram, assign: BTreeMap<VarId, Fr>) -> Self {
        Self { prog, assign }
    }

    /// The (minimized) R1CS this circuit will synthesize — used by `xark setup`
    /// to cache exactly what the proving key is keyed to.
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
    /// one this returns a descriptive `Err` instead of letting the (infallible)
    /// parse inside [`ConstraintSynthesizer::generate_constraints`] panic.
    ///
    /// Call this before handing a circuit built from *untrusted* input (e.g. a
    /// deserialized `r1cs.json`) to the Groth16 backend. [`prove_only`] runs it
    /// automatically.
    pub fn validate(&self) -> Result<(), String> {
        validate_program_constants(&self.prog)
    }
}

/// Reject an R1CS program that would crash the synthesizer, returning a
/// descriptive error. Used to fail gracefully on an untrusted program before the
/// panicking synthesis path runs.
fn validate_program_constants(prog: &R1csProgram) -> Result<(), String> {
    // Every term must reference a declared variable: `generate_constraints`
    // indexes `map[&t.var]`, which panics on a dangling id. Reject it here so a
    // malformed `r1cs.json` is a clean error, not a crash. Coefficients need no
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

impl ConstraintSynthesizer<Fr> for XarkCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // Allocate one arkworks variable per IR var, in id order. Public →
        // input variable, everything else → witness variable. Var ids are dense,
        // so the id→arkworks-var map is a `Vec` (O(1) per-term lookups in `build`,
        // vs a `BTreeMap`'s O(log n)); we sort a slice of *references*, avoiding a
        // clone of the whole `variables` vec on every synthesis.
        let mut order: Vec<_> = self.prog.variables.iter().collect();
        order.sort_by_key(|v| v.id);
        let max_id = order.last().map_or(0, |v| v.id) as usize;
        let mut map: Vec<Option<Variable>> = vec![None; max_id + 1];
        for v in order {
            let val = self.assign.get(&v.id).copied().unwrap_or_else(Fr::zero);
            let av = match v.visibility {
                Visibility::Public => cs.new_input_variable(|| Ok(val))?,
                _ => cs.new_witness_variable(|| Ok(val))?,
            };
            map[v.id as usize] = Some(av);
        }

        let build = |lc: &IrLc| -> LinearCombination<Fr> {
            let mut out = LinearCombination::zero();
            let c = fr_from_fieldconst(&lc.constant);
            if !c.is_zero() {
                out += (c, Variable::One);
            }
            for t in &lc.terms {
                // `validate_program_constants` guarantees every term var is a
                // declared (hence allocated) id.
                out += (fr_from_fieldconst(&t.coeff), map[t.var as usize].unwrap());
            }
            out
        };

        for con in &self.prog.constraints {
            let a = build(&con.a);
            let b = build(&con.b);
            let c = build(&con.c);
            cs.enforce_r1cs_constraint(|| a, || b, || c)?;
        }
        Ok(())
    }
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
/// exists for in-crate round-trip / differential tests. Never use it — or any
/// key it generates — in production; the CLI `xark setup` (ptau / ceremony) and
/// `xark prove` (`OsRng`) path is the real one.
// The tuple return (verifying key, proof, public inputs) is the natural result
// shape for a test/dev prove helper; a named struct would not add clarity.
#[allow(clippy::type_complexity)]
pub fn prove_only(
    r1cs: &R1csProgram,
    circuit: &PrimitiveProgram,
    inputs: &BTreeMap<VarId, String>,
) -> Result<(VerifyingKey<Bn254>, Proof<Bn254>, Vec<Fr>), String> {
    // Reject a malformed R1CS program (bad decimal constant) up front with a
    // descriptive error, rather than panicking inside Groth16 synthesis.
    validate_program_constants(r1cs)?;
    let assign_fp = solver::solve_and_check(circuit, inputs)
        .map_err(|e| format!("witness does not satisfy the circuit: {e:?}"))?;
    let assign: BTreeMap<VarId, Fr> = assign_fp
        .iter()
        // BN254 witness values come straight out of the solver as `Fr` (no
        // decimal-string round-trip); the non-BN254 fallback reparses.
        .map(|(k, v)| {
            (
                *k,
                v.as_bn254_fr()
                    .unwrap_or_else(|| fr_from_decimal(&v.to_decimal())),
            )
        })
        .collect();

    let public = public_inputs(r1cs, &assign);
    let circ = XarkCircuit::for_proving(r1cs.clone(), assign);

    use rand::SeedableRng;
    let mut rng = rand::rngs::StdRng::seed_from_u64(0);
    let (pk, vk) = Groth16::<Bn254>::circuit_specific_setup(circ.clone(), &mut rng)
        .map_err(|e| format!("setup: {e:?}"))?;
    let proof =
        Groth16::<Bn254>::prove(&pk, circ, &mut rng).map_err(|e| format!("prove: {e:?}"))?;
    Ok((vk, proof, public))
}

/// Run the full pipeline: solve the witness from `inputs`, lower to Groth16, and
/// return whether the resulting proof verifies against the public inputs.
pub fn prove_and_verify(
    r1cs: &R1csProgram,
    circuit: &PrimitiveProgram,
    inputs: &BTreeMap<VarId, String>,
) -> Result<bool, String> {
    let (vk, proof, public) = prove_only(r1cs, circuit, inputs)?;
    Groth16::<Bn254>::verify(&vk, &public, &proof).map_err(|e| format!("verify: {e:?}"))
}

// ===========================================================================
// In-crate testing API.
//
// Lets a circuit author unit-test their circuit with plain `cargo test` (via
// the `xark init` scaffold): load the built artifacts, feed positional inputs,
// and get back whether a dev-mode Groth16 proof verifies.
// ===========================================================================

/// A built circuit loaded from `target/xark/<name>/`, ready to prove against.
///
/// Obtain one with [`circuit`]; drive it with [`Circuit::prove`].
pub struct Circuit {
    /// The circuit name (for diagnostics), e.g. `<name>` in `target/xark/<name>/`.
    name: String,
    r1cs: R1csProgram,
    prim: PrimitiveProgram,
    /// Per-constraint source/function attribution, loaded from `profile.json` when
    /// present (built by `xark test` or `xark build --profile`). Used to explain
    /// *which* source line / function a failing constraint came from. `None` when
    /// the circuit was built without `--profile`.
    profile: Option<ProfileProgram>,
}

/// The error from [`Circuit::check`]: a human-readable, multi-line explanation
/// of why the witness does not satisfy the circuit (which constraint, and — when
/// profiled — its source line and function chain).
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
/// Each declared parameter fans out to one `(leaf-name, decimal-value)` pair per
/// witness leaf it occupies: a scalar `Private<Field>` is a single leaf
/// (`("k", "3")`); a `Private<[u8; 56]>` is 56 byte leaves
/// (`("input[0]", "97"), …`); a `Public<[u8; 32]>` expected hash is a `Digest`'s
/// 256 bit leaves (`("result.bits[0][0]", "1"), …`). The leaf **names** are the
/// compiler's structural-flatten names and the **values** are decimal strings
/// (so digest bits / curve coordinates that overflow `i128` are representable);
/// [`Circuit::resolve_inputs`] matches each name to its variable.
pub trait ProveInputs {
    fn into_inputs(self) -> Vec<(String, String)>;
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

/// Load a circuit built by `xark build` from `target/xark/<name>/`, relative to
/// the current directory (where `cargo test` runs, i.e. the crate root).
///
/// Panics with a clear message if the artifacts are missing — run `xark build`
/// first.
pub fn circuit(name: &str) -> Circuit {
    circuit_at(std::path::Path::new("target/xark").join(name))
}

/// Load a circuit from an explicit artifact directory (`<dir>/circuit.xbc`, or the
/// legacy `circuit.json` + `r1cs.json` pair). [`circuit`] is the sugar for the
/// conventional `target/xark/<name>/` location. The circuit name (for diagnostics)
/// is the directory's final component.
pub fn circuit_at(dir: impl AsRef<std::path::Path>) -> Circuit {
    let dir = dir.as_ref();
    let name = dir
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("circuit")
        .to_string();
    let xbc_path = dir.join("circuit.xbc");
    let circuit_path = dir.join("circuit.json");
    let r1cs_path = dir.join("r1cs.json");

    // The common failure is "forgot to build". Check for the artifact up front and
    // explain exactly what to do — with the fix command on its own line — rather
    // than surfacing a raw file/parse error from deeper in the load.
    if !xbc_path.exists() && !circuit_path.exists() {
        panic!("{}", not_built_message(&name, &xbc_path));
    }

    // The compact binary `circuit.xbc` that `xark build` always writes is
    // self-contained: expanding it once yields BOTH the solver's primitive view
    // and the backend's R1CS. Fall back to the JSON pair (`circuit.json` +
    // `r1cs.json`) only for older / `--emit-json` builds.
    let (prim, r1cs) = if xbc_path.exists() {
        let bytes = std::fs::read(&xbc_path)
            .unwrap_or_else(|e| panic!("reading {}: {e}", xbc_path.display()));
        let cp = xark_ir::function_decode::expand_function_blob(&bytes)
            .unwrap_or_else(|e| panic!("expanding {}: {e}", xbc_path.display()));
        (cp.to_primitive(), cp.to_r1cs())
    } else {
        let cj = std::fs::read_to_string(&circuit_path).unwrap_or_else(|_| {
            panic!(
                "circuit `{name}` not built — run `xark build` first (expected {})",
                xbc_path.display()
            )
        });
        let prim = xark_ir::primitive::from_json(&cj)
            .unwrap_or_else(|e| panic!("parsing {}: {e}", circuit_path.display()));
        let rj = std::fs::read_to_string(&r1cs_path).unwrap_or_else(|_| {
            panic!(
                "circuit `{name}` not built — run `xark build` first (expected {})",
                r1cs_path.display()
            )
        });
        let r1cs = xark_ir::json::from_json(&rj)
            .unwrap_or_else(|e| panic!("parsing {}: {e}", r1cs_path.display()));
        (prim, r1cs)
    };
    // Best-effort: load the per-constraint attribution if the circuit was built
    // with `--profile` (as `xark test` does). Absent or malformed → `None`; the
    // failure diagnostic then degrades to the constraint index + its debug note.
    let profile = std::fs::read_to_string(dir.join("profile.json"))
        .ok()
        .and_then(|s| xark_ir::profile::from_json(&s).ok());
    Circuit {
        name,
        r1cs,
        prim,
        profile,
    }
}

impl Circuit {
    /// Resolve the typed `inputs` into `VarId → decimal` for the solver.
    ///
    /// Panics on a name that isn't a declared input, or a count mismatch — those
    /// are test-authoring bugs (the generated `<Fn>Inputs` struct can't produce
    /// them), so failing loudly is correct.
    fn resolve_inputs<I: ProveInputs>(&self, inputs: I) -> BTreeMap<VarId, String> {
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
            id_inputs.insert(id, val);
        }
        id_inputs
    }

    /// Check that `inputs` **satisfy the circuit**: solve the witness and verify
    /// it meets every constraint. Returns `Ok(())` when it does, or an actionable
    /// `Err` naming the first failing constraint — and, when the circuit was built
    /// with `--profile` (as `xark test` does), its source line and function chain.
    ///
    /// This is the fast, everyday circuit test. A satisfying witness *is* the
    /// proof the stated relation holds for these inputs, so the **positive** test
    /// is `c.check(good).unwrap()` (its panic message points at the offending line
    /// on failure) and the **negative** test is `assert!(c.check(bad).is_err())`.
    ///
    /// It deliberately does **not** run Groth16: producing a real proof over a
    /// large circuit is orders of magnitude slower and exercises the *backend*,
    /// not the circuit. If a witness satisfies the R1CS, a correct Groth16 backend
    /// proves and verifies it — a property the backend's own tests cover, not one
    /// re-checked per circuit. Use [`Self::prove`] when you specifically want the
    /// full proving pipeline.
    ///
    /// Panics only on malformed `inputs` (see [`Self::resolve_inputs`]).
    pub fn check<I: ProveInputs>(&self, inputs: I) -> Result<(), ProveError> {
        let id_inputs = self.resolve_inputs(inputs);
        // An unsatisfiable witness means the stated relation is false; explain
        // *which* constraint (and its source line / function, when profiled)
        // failed, via the shared diagnostic.
        solver::solve_and_check(&self.prim, &id_inputs).map_err(|e| {
            ProveError(xark_ir::diagnose::describe_unsatisfied(
                &e,
                &self.r1cs,
                self.profile.as_ref(),
            ))
        })?;
        Ok(())
    }

    /// Prove the circuit against `inputs` **end to end** — solve the witness, then
    /// run a real (dev-mode, seed 1) Groth16 setup + prove + verify. Returns
    /// `Ok(())` when the proof verifies, or an actionable `Err`: an unsatisfiable
    /// witness, or — past that — a genuine `r1cs.json`/`circuit.json` inconsistency.
    ///
    /// Prefer [`Self::check`] for ordinary tests — it's the same witness
    /// satisfaction check without the much slower Groth16 (which exercises the
    /// backend, not the circuit). Reach for `prove` to confirm the whole proving
    /// pipeline for one circuit. Runs in seconds only in `--release`; a large
    /// circuit takes minutes in debug.
    pub fn prove<I: ProveInputs>(&self, inputs: I) -> Result<(), ProveError> {
        let id_inputs = self.resolve_inputs(inputs);
        let assign_fp = solver::solve_and_check(&self.prim, &id_inputs).map_err(|e| {
            ProveError(xark_ir::diagnose::describe_unsatisfied(
                &e,
                &self.r1cs,
                self.profile.as_ref(),
            ))
        })?;
        let assign: BTreeMap<VarId, Fr> = assign_fp
            .iter()
            // BN254 witness values come straight out of the solver as `Fr` (no
            // decimal-string round-trip); the non-BN254 fallback reparses.
            .map(|(k, v)| {
                (
                    *k,
                    v.as_bn254_fr()
                        .unwrap_or_else(|| fr_from_decimal(&v.to_decimal())),
                )
            })
            .collect();

        let public = public_inputs(&self.r1cs, &assign);
        let circ = XarkCircuit::for_proving(self.r1cs.clone(), assign);

        // Past here the witness satisfies every constraint, so any backend
        // failure is a genuine circuit/backend inconsistency, not a false
        // statement — surface it rather than swallowing it into a bare `false`.
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(1);
        let (pk, vk) =
            Groth16::<Bn254>::circuit_specific_setup(circ.clone(), &mut rng).map_err(|e| {
                ProveError(format!(
                    "circuit `{}` solved but Groth16 setup failed: {e}",
                    self.name
                ))
            })?;
        let proof = Groth16::<Bn254>::prove(&pk, circ, &mut rng).map_err(|e| {
            ProveError(format!(
                "circuit `{}` solved but Groth16 prove failed: {e}",
                self.name
            ))
        })?;
        match Groth16::<Bn254>::verify(&vk, &public, &proof) {
            Ok(true) => Ok(()),
            Ok(false) | Err(_) => Err(ProveError(format!(
                "circuit `{}` has a satisfying witness but its proof did not verify — the R1CS \
                 and witness-gen (`r1cs.json` vs `circuit.json`) disagree",
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
        // A term referencing an undeclared variable id would panic at
        // `map[&t.var]` during synthesis; validation must reject it cleanly.
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
        assert!(Groth16::<Bn254>::verify(&vk, &public, &proof).unwrap());

        let tampered = vec![public[0] + Fr::from(1u64)];
        assert!(!Groth16::<Bn254>::verify(&vk, &tampered, &proof).unwrap());
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
