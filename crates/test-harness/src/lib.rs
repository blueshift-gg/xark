//! Shared test harness: compile a circuit source with the `xark` compiler and
//! read back its emitted artifacts (no shell script). Used by the snapshot
//! suite and every gadget crate's `vec.rs`.
//!
//! Builds the `xark` lib and the gadget crates once per test process for wasm32
//! (`--cfg xark`, in an isolated `target/xark-compile-wasm`), then compiles each
//! circuit source with stable `rustc` against them and lowers the module with
//! `xark-frontend`.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};

use xark_ir::primitive::{self, PrimitiveProgram};

pub mod bignum;

/// The result of compiling one circuit source.
pub struct Compiled {
    pub status_success: bool,
    pub stderr: String,
    pub out_dir: PathBuf,
}

impl Compiled {
    /// The primitive program — decoded from the compact `circuit.xbc` (the sole
    /// default artifact), not the `--emit-json`-only `circuit.json`. So tests that
    /// need the program don't force the slow multi-GB JSON emission.
    pub fn program(&self) -> PrimitiveProgram {
        let xbc = self.out_dir.join("circuit.xbc");
        let bytes = std::fs::read(&xbc).unwrap_or_else(|e| panic!("read {}: {e}", xbc.display()));
        xark_ir::function_decode::expand_function_blob(&bytes)
            .unwrap_or_else(|e| panic!("expand {}: {e}", xbc.display()))
            .to_primitive()
    }

    /// The number of R1CS **multiplication gates** (`a·b` rows where both sides
    /// carry a variable), streamed from `circuit.xbc` — O(1) memory, no flat R1CS.
    /// For the R1CS↔Lean gate-count bridges, in place of parsing `r1cs.json`.
    pub fn mul_gate_count(&self) -> usize {
        let xbc = self.out_dir.join("circuit.xbc");
        let bytes = std::fs::read(&xbc).unwrap_or_else(|e| panic!("read {}: {e}", xbc.display()));
        xark_ir::function_decode::stream_count_mul_gates(&bytes)
    }

    /// A stable 128-bit fingerprint of the R1CS the circuit expands to, streamed
    /// straight from `circuit.xbc` — O(1) memory, no expand-then-minimize. Use it
    /// as a regression pin (`assert_eq!(c.circuit_digest(), 0x…)`) in place of a
    /// materializing constraint-count check; any change to the proven circuit
    /// flips the digest.
    pub fn circuit_digest(&self) -> u128 {
        let xbc = self.out_dir.join("circuit.xbc");
        let bytes = std::fs::read(&xbc).unwrap_or_else(|e| panic!("read {}: {e}", xbc.display()));
        xark_ir::function_decode::stream_digest(&bytes)
    }

    /// The **minimized** R1CS constraint count — the invariant the prover
    /// actually proves. Setup and proving both expand `circuit.xbc` and run
    /// `minimize_with_fill(.., usize::MAX)`; this reproduces that pipeline. Use
    /// it for constraint-count pins instead of the raw `circuit.json`, whose flat
    /// expansion carries function plug-materialization that minimization removes
    /// (so cached vs. inlined differ in the flat count but not in what is proven).
    pub fn minimized_r1cs_len(&self) -> usize {
        let bytes = std::fs::read(self.out_dir.join("circuit.xbc"))
            .unwrap_or_else(|e| panic!("read {}: {e}", self.out_dir.join("circuit.xbc").display()));
        // From the per-template-reduced expansion: unbounded fill-in is safe (and
        // reaches the same fixpoint) there, but not on the raw flat expansion,
        // where it took 34 GB on grumpkin_ipa_fold.
        let cp = xark_ir::function_decode::expand_function_blob_reduced(&bytes)
            .unwrap_or_else(|e| panic!("expand circuit.xbc: {e}"));
        xark_ir::minimize::minimize_with_fill(&cp.into_r1cs(), usize::MAX)
            .constraints
            .len()
    }

    /// Check that native `inputs` **satisfy** this compiled circuit — the
    /// in-memory analogue of `xark_prover::Circuit::check`, for a circuit
    /// compiled straight from source with [`compile_file`] (no `xark build`).
    ///
    /// Each `(name, value)` fans out to witness leaves via [`bignum::LeafInput`],
    /// names resolve against the actual compiled program (an unknown/missing leaf
    /// is a loud `Err`), the witness is solved, and the circuit is confirmed
    /// fully constrained (analyzer-clean). Returns `Ok(())` when the inputs
    /// satisfy every constraint, else a descriptive `Err` — so a genuine
    /// signature is `check(..).unwrap()` and a tampered one
    /// `assert!(check(..).is_err())`.
    pub fn check(&self, inputs: &[(&str, &dyn bignum::LeafInput)]) -> Result<(), String> {
        let (bytes, id_inputs) = self.resolve_inputs(inputs)?;

        // Satisfiability + the global under-constraint soundness pass, both
        // streamed straight from the compact `circuit.xbc`: the witness is solved
        // once, then a single parallel sweep checks every row `a·b = c` and
        // classifies every variable into one flag byte (never the flat
        // `Expression` system, and — unlike a naive stream — never the
        // per-reference univariate reductions either). Peak memory is the witness
        // plus ~1 byte/var, so this beats the flat path even when the witness
        // dominates (heavy non-native EC). Verdicts are identical to
        // `analyze_underconstrained` (asserted by `streaming_core_matches_flat_on_underconstrained`,
        // `stream_analyze_matches_flat_analyzer`, and `cp_solver_matches_primitive_path`).
        let under = xark_ir::function_decode::stream_verify(&bytes, &id_inputs)
            .map_err(|e| format!("inputs do not satisfy the circuit: {e}"))?;

        // The analyzer inspects only `Derived` (advice/internal) vars. A
        // `witness_only` derivation (e.g. the secp256k1 GLV lattice reduction)
        // computes advice through SCRATCH vars that no constraint references; they
        // only derive pinned outputs and are removed by `minimize` before proving.
        // Such a var is causally disconnected — in no constraint, so changing it
        // alters no constraint's satisfaction and no public output — hence not a
        // forgery vector. Ignore that benign reason; still fail on a var that IS
        // referenced but left free (a genuine, forgeable under-constraint).
        const UNREFERENCED: &str = "no constraint references this variable";
        let real: Vec<_> = under
            .into_iter()
            .filter(|u| u.reason != UNREFERENCED)
            .collect();
        if !real.is_empty() {
            return Err(format!(
                "circuit is under-constrained ({} forgeable witness var(s): {:?})",
                real.len(),
                real.iter().take(12).collect::<Vec<_>>()
            ));
        }
        Ok(())
    }

    /// Read `circuit.xbc` and resolve named `inputs` to the compiled circuit's
    /// input var ids, without expanding any constraints. Shared by [`check`] and
    /// [`check_satisfies`]; returns the raw bytes (so the caller can stream) plus
    /// the `var id -> decimal` witness inputs.
    fn resolve_inputs(
        &self,
        inputs: &[(&str, &dyn bignum::LeafInput)],
    ) -> Result<(Vec<u8>, std::collections::BTreeMap<u32, String>), String> {
        use xark_ir::primitive::VarRole;
        let bytes = std::fs::read(self.out_dir.join("circuit.xbc"))
            .map_err(|e| format!("read circuit.xbc: {e}"))?;
        let vars = xark_ir::function_decode::decode_vars(&bytes);
        let input_vars: Vec<&primitive::Var> = vars
            .iter()
            .filter(|v| matches!(v.role, VarRole::PublicInput | VarRole::PrivateInput))
            .collect();
        let by_name: std::collections::BTreeMap<&str, u32> =
            input_vars.iter().map(|v| (v.name.as_str(), v.id)).collect();

        let pairs: Vec<(String, String)> =
            inputs.iter().flat_map(|(name, v)| v.leaves(name)).collect();
        if pairs.len() != input_vars.len() {
            let expected: Vec<&str> = input_vars.iter().map(|v| v.name.as_str()).collect();
            return Err(format!(
                "circuit expects {} input leaf(s) {:?}, got {} from these values",
                input_vars.len(),
                expected,
                pairs.len(),
            ));
        }
        let mut id_inputs: std::collections::BTreeMap<u32, String> =
            std::collections::BTreeMap::new();
        for (name, val) in pairs {
            let id = by_name.get(name.as_str()).ok_or_else(|| {
                let expected: Vec<&str> = input_vars.iter().map(|v| v.name.as_str()).collect();
                format!("unknown circuit input leaf `{name}`; expected one of {expected:?}")
            })?;
            id_inputs.insert(*id, val);
        }
        Ok((bytes, id_inputs))
    }

    /// Streaming correctness check for circuits with **raw field inputs** given by
    /// variable name → decimal value (e.g. a hash KAT that feeds the message block
    /// and the expected digest words). Solves + checks satisfiability + runs the
    /// under-constraint analyzer, all streamed from `circuit.xbc` — the low-memory
    /// analogue of `from_json` + `solve_and_check` + `analyze_underconstrained`.
    /// `Ok(())` iff every constraint holds and no referenced var is forgeable.
    pub fn check_named(
        &self,
        inputs: &std::collections::BTreeMap<String, String>,
    ) -> Result<(), String> {
        let xbc = self.out_dir.join("circuit.xbc");
        let bytes = std::fs::read(&xbc).map_err(|e| format!("read {}: {e}", xbc.display()))?;
        let vars = xark_ir::function_decode::decode_vars(&bytes);
        let by_name: std::collections::BTreeMap<&str, u32> =
            vars.iter().map(|v| (v.name.as_str(), v.id)).collect();
        let mut id_inputs: std::collections::BTreeMap<u32, String> =
            std::collections::BTreeMap::new();
        for (name, val) in inputs {
            let id = by_name
                .get(name.as_str())
                .ok_or_else(|| format!("unknown circuit input `{name}`"))?;
            id_inputs.insert(*id, val.clone());
        }
        const UNREFERENCED: &str = "no constraint references this variable";
        let real: Vec<_> = xark_ir::function_decode::stream_verify(&bytes, &id_inputs)?
            .into_iter()
            .filter(|u| u.reason != UNREFERENCED)
            .collect();
        if !real.is_empty() {
            return Err(format!(
                "circuit is under-constrained ({} forgeable var(s): {:?})",
                real.len(),
                real.iter().take(8).collect::<Vec<_>>()
            ));
        }
        Ok(())
    }
}

/// The workspace root, computed from *this* crate's manifest dir (stable no
/// matter which crate's tests call in).
fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .canonicalize()
        .expect("canonicalize workspace root")
}

/// One `--extern name=path` per circuit rlib (newest per crate; skip stray
/// non-hashed artifacts and the non-circuit libraries).
fn externs(deps: &Path) -> Vec<String> {
    let mut rlibs: Vec<PathBuf> = std::fs::read_dir(deps)
        .into_iter()
        .flatten()
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| {
            let n = p.file_name().and_then(|s| s.to_str()).unwrap_or("");
            // `libxark_foo-<hash>.rlib` for the gadget crates *and*
            // `libxark-<hash>.rlib` for the merged `xark` lib itself (the
            // language markers), which gadgets now depend on.
            (n.starts_with("libxark_") || n.starts_with("libxark-")) && n.ends_with(".rlib")
        })
        .collect();
    rlibs.sort_by_key(|p| std::fs::metadata(p).and_then(|m| m.modified()).ok());
    rlibs.reverse(); // newest first

    let mut seen = std::collections::BTreeSet::new();
    let mut out = Vec::new();
    for p in &rlibs {
        let file = p.file_name().unwrap().to_string_lossy();
        // `libxark_foo-<hash>.rlib` → `xark_foo`; require the `-<hash>` (skips
        // stray non-cargo artifacts that would otherwise keep the `.rlib`).
        let Some(stem) = file
            .strip_prefix("lib")
            .and_then(|s| s.strip_suffix(".rlib"))
        else {
            continue;
        };
        let Some((name, _hash)) = stem.rsplit_once('-') else {
            continue;
        };
        if matches!(name, "xark_ir" | "xark_prover" | "xark_test_harness") {
            continue;
        }
        if seen.insert(name.to_string()) {
            out.push(format!("{name}={}", p.display()));
        }
    }
    out
}

static LOCK: Mutex<()> = Mutex::new(());

/// Compile a circuit source **file** to `circuit.xbc` under `target/test-out/<out_name>`.
/// Matches a normal `xark build`: the compact artifact only, no JSON. Tests read
/// the program via [`Compiled::program`]/[`Compiled::circuit_digest`] (both from
/// `circuit.xbc`); use [`compile_file_json`] only when a test reads the
/// `--emit-json`-only `circuit.json` / `r1cs.json` / `graph.dot` directly.
pub fn compile_file(src: &Path, out_name: &str, field: &str) -> Compiled {
    compile_file_inner(src, out_name, field, false)
}

/// Like [`compile_file`], but also emits `circuit.json` / `r1cs.json` /
/// `graph.dot` (`--emit-json`). Serializing those is slow (multi-GB on heavy
/// circuits), so reserve it for the snapshot suite and fixture regeneration.
pub fn compile_file_json(src: &Path, out_name: &str, field: &str) -> Compiled {
    compile_file_inner(src, out_name, field, true)
}

/// The gadget crates (`gadgets/xark-*`) plus the `xark` lib, built once for wasm32
/// with `--cfg xark`; returns `(wasm deps dir, host deps dir)` (the proc macros
/// are host artifacts).
fn built_wasm() -> &'static (PathBuf, PathBuf) {
    static BUILT: OnceLock<(PathBuf, PathBuf)> = OnceLock::new();
    BUILT.get_or_init(|| {
        let root = workspace_root();
        let target = root.join("target/xark-compile-wasm");
        let mut args: Vec<String> = [
            "build",
            "--release",
            "--target",
            "wasm32-unknown-unknown",
            "-p",
            "xark",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        let mut names: Vec<String> = std::fs::read_dir(root.join("gadgets"))
            .expect("read gadgets/")
            .filter_map(|e| e.ok())
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .filter(|n| n.starts_with("xark-"))
            .collect();
        names.sort();
        for n in names {
            args.push("-p".into());
            args.push(n);
        }
        let ok = Command::new("cargo")
            .args(&args)
            .env("RUSTFLAGS", "--cfg xark --allow=unexpected_cfgs")
            .env("CARGO_TARGET_DIR", &target)
            .env_remove("RUSTUP_TOOLCHAIN")
            .current_dir(&root)
            .status()
            .expect("run cargo build (wasm gadgets)")
            .success();
        assert!(ok, "building wasm gadget rlibs failed");
        (
            target.join("wasm32-unknown-unknown/release/deps"),
            target.join("release/deps"),
        )
    })
}

fn compile_file_stable(src: &Path, out_name: &str, field: &str, emit_json: bool) -> Compiled {
    let _guard = LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let (deps, host_deps) = built_wasm();
    let root = workspace_root();
    let out_dir = root.join("target/test-out").join(out_name);
    let _ = std::fs::remove_dir_all(&out_dir);
    std::fs::create_dir_all(&out_dir).expect("create out dir");
    let wasm = out_dir.join("circuit.wasm");
    // The frontend's entry is the `#[circuit]` fn. A test source written as a bare
    // `pub fn` whose params are all `Private<…>`/`Public<…>` gets the attribute
    // added here.
    let text = std::fs::read_to_string(src).expect("read circuit source");
    let src_path = if text.contains("circuit]") {
        src.to_path_buf()
    } else {
        let annotated = annotate_entry(&text);
        let p = out_dir.join("annotated.rs");
        std::fs::write(&p, annotated).expect("write annotated source");
        p
    };
    let src = src_path.as_path();
    let mut cmd = Command::new("rustc");
    cmd.env_remove("RUSTUP_TOOLCHAIN").args([
        "--crate-type=cdylib",
        "--edition=2021",
        "--target=wasm32-unknown-unknown",
        "--cfg=xark",
        "--allow=unexpected_cfgs",
        "-Copt-level=s",
        "-Cpanic=abort",
        "-Coverflow-checks=on",
    ]);
    for e in externs(deps) {
        cmd.arg("--extern").arg(e);
    }
    cmd.arg("-L")
        .arg(format!("dependency={}", deps.display()))
        .arg("-L")
        .arg(format!("dependency={}", host_deps.display()));
    let output = cmd
        .arg(src)
        .arg("-o")
        .arg(&wasm)
        .current_dir(&root)
        .output()
        .expect("run rustc");
    if !output.status.success() {
        return Compiled {
            status_success: false,
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            out_dir,
        };
    }
    let bytes = std::fs::read(&wasm).expect("read circuit.wasm");
    let spec = if field == "unknown" {
        xark_ir::FieldSpec::unknown()
    } else {
        xark_ir::FieldSpec::named(field)
    };
    // Debug notes and variable names only for the JSON views that show them:
    // `circuit.xbc` is the same either way, and on a large circuit they cost GBs
    // (34 GB on grumpkin_ipa_fold).
    match xark_frontend::lower_module(&bytes, spec, false, emit_json) {
        Ok(l) => {
            xark_frontend::write_outputs(&out_dir, &l.output, emit_json, false)
                .expect("write outputs");
            let _ = std::fs::write(
                out_dir.join("schema.json"),
                serde_json::to_string_pretty(&l.schema).unwrap_or_default() + "\n",
            );
            Compiled {
                status_success: true,
                stderr: String::new(),
                out_dir,
            }
        }
        Err(e) => Compiled {
            status_success: false,
            stderr: format!("error: {e}"),
            out_dir,
        },
    }
}

/// Add `#[::xark::circuit]` before the first top-level `pub fn` whose parameters
/// all use the `Private<…>`/`Public<…>` markers.
fn annotate_entry(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 32);
    let mut done = false;
    let mut rest = text;
    while let Some(i) = rest.find("pub fn ") {
        let (head, tail) = rest.split_at(i);
        out.push_str(head);
        let sig_end = tail.find('{').unwrap_or(tail.len());
        let sig = &tail[..sig_end];
        let params = sig
            .split_once('(')
            .and_then(|(_, p)| p.rsplit_once(')'))
            .map(|(p, _)| p)
            .unwrap_or("");
        let at_line_start = head.is_empty() || head.ends_with('\n');
        let all_marked = !params.trim().is_empty()
            && params
                .split(',')
                .filter(|a| a.contains(':'))
                .all(|a| a.contains("Private<") || a.contains("Public<"));
        // Failing that, a `pub fn circuit(…)` with unmarked params: annotate it so
        // `#[circuit]` rejects the params with its diagnostic.
        let fallback = !text_has_marked_entry(text) && sig.starts_with("pub fn circuit(");
        if !done && at_line_start && (all_marked || fallback) {
            out.push_str("#[::xark::circuit]\n");
            done = true;
        }
        out.push_str("pub fn ");
        rest = &tail["pub fn ".len()..];
    }
    out.push_str(rest);
    out
}

/// Whether some top-level `pub fn` has only `Private<…>`/`Public<…>` params.
fn text_has_marked_entry(text: &str) -> bool {
    text.split("pub fn ").skip(1).any(|f| {
        let sig = &f[..f.find('{').unwrap_or(f.len())];
        let params = sig
            .split_once('(')
            .and_then(|(_, p)| p.rsplit_once(')'))
            .map(|(p, _)| p)
            .unwrap_or("");
        !params.trim().is_empty()
            && params
                .split(',')
                .filter(|a| a.contains(':'))
                .all(|a| a.contains("Private<") || a.contains("Public<"))
    })
}

fn compile_file_inner(src: &Path, out_name: &str, field: &str, emit_json: bool) -> Compiled {
    compile_file_stable(src, out_name, field, emit_json)
}

/// Compile a circuit source **string** (written to a temp file) to `circuit.xbc`.
pub fn compile_source(name: &str, src: &str, field: &str) -> Compiled {
    let path = std::env::temp_dir().join(format!("xark_harness_{name}.rs"));
    std::fs::write(&path, src).expect("write temp source");
    compile_file(&path, name, field)
}
