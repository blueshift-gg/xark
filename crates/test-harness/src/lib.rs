//! Shared test harness: compile a circuit source with the `xark` compiler and
//! read back its emitted artifacts (no shell script). Used by the snapshot
//! suite and every gadget crate's `vec.rs`.
//!
//! Builds the `xark` lib and the gadget crates once per test process for wasm32
//! (`--cfg xark`, in an isolated `target/xark-compile-wasm`), then compiles each
//! circuit source with stable `rustc` against them and lowers the module with
//! `xark-frontend`.

use std::collections::{BTreeMap, BTreeSet};
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
    ) -> Result<(Vec<u8>, BTreeMap<u32, String>), String> {
        use xark_ir::primitive::VarRole;
        let bytes = std::fs::read(self.out_dir.join("circuit.xbc"))
            .map_err(|e| format!("read circuit.xbc: {e}"))?;
        let vars = xark_ir::function_decode::decode_vars(&bytes);
        let input_vars: Vec<&primitive::Var> = vars
            .iter()
            .filter(|v| matches!(v.role, VarRole::PublicInput | VarRole::PrivateInput))
            .collect();
        let by_name: BTreeMap<&str, u32> =
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
        let mut id_inputs: BTreeMap<u32, String> = BTreeMap::new();
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
    pub fn check_named(&self, inputs: &BTreeMap<String, String>) -> Result<(), String> {
        let xbc = self.out_dir.join("circuit.xbc");
        let bytes = std::fs::read(&xbc).map_err(|e| format!("read {}: {e}", xbc.display()))?;
        let vars = xark_ir::function_decode::decode_vars(&bytes);
        let by_name: BTreeMap<&str, u32> = vars.iter().map(|v| (v.name.as_str(), v.id)).collect();
        let mut id_inputs: BTreeMap<u32, String> = BTreeMap::new();
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

/// The wasm libraries a circuit is compiled against: the `xark` lib and the
/// gadget crates, built once per test process.
struct WasmLibs {
    /// The workspace root the libraries and each circuit's output live under.
    root: PathBuf,
    /// The `--extern` name and rlib path for every library the circuit is built against.
    externs: BTreeMap<String, PathBuf>,
    /// The build's artifact directories, searched for the rlibs' dependencies.
    library_dirs: BTreeSet<PathBuf>,
}

impl WasmLibs {
    /// Build the libraries once for this process.
    fn get() -> &'static Self {
        static LIBS: OnceLock<WasmLibs> = OnceLock::new();
        LIBS.get_or_init(Self::build)
    }

    fn build() -> Self {
        let root = workspace_root();
        let target = root.join("target/xark-compile-wasm");
        let wasm_target = target.join("wasm32-unknown-unknown");
        let mut packages: Vec<String> = std::fs::read_dir(root.join("gadgets"))
            .expect("unable to read the workspace's gadgets/ directory")
            .filter_map(|entry| entry.ok())
            .filter_map(|entry| entry.file_name().into_string().ok())
            .filter(|name| name.starts_with("xark-"))
            .collect();
        packages.sort();

        // Cargo's lib target names use underscores in place of package-name
        // hyphens. `xark` itself is not under `gadgets/`.
        let mut requested_targets = BTreeSet::from(["xark".to_owned()]);
        requested_targets.extend(packages.iter().map(|name| name.replace('-', "_")));

        // Every test process builds the libraries, and every build, a fresh one
        // too, removes and rewrites the uplifted `lib<name>.rlib`s the circuits
        // link: a compile in one process could find one missing or half written
        // while another's build ran (`cannot find crate xark`, `rust-lld`
        // failures). So the build and a copy of those files, which the compiles
        // then link instead, happen under this lock (see `snapshot`).
        std::fs::create_dir_all(&target).expect("create target/xark-compile-wasm");
        let lock = std::fs::File::create(target.join(".harness.lock"))
            .expect("create target/xark-compile-wasm/.harness.lock");
        lock.lock()
            .expect("lock target/xark-compile-wasm/.harness.lock");

        let output = Command::new("cargo")
            .args([
                "build",
                "--release",
                "--target",
                "wasm32-unknown-unknown",
                "-p",
                "xark",
            ])
            .args(packages.iter().flat_map(|name| ["-p", name.as_str()]))
            .arg("--message-format=json-render-diagnostics")
            .env("RUSTFLAGS", "--cfg xark --allow=unexpected_cfgs")
            .env("CARGO_TARGET_DIR", &target)
            .env_remove("RUSTUP_TOOLCHAIN")
            .current_dir(&root)
            .output()
            .expect("run cargo build (wasm gadgets)");

        assert!(
            output.status.success(),
            "building wasm gadget rlibs failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );

        let mut externs = BTreeMap::new();
        let mut library_dirs = BTreeSet::new();

        for line in output.stdout.split(|b| *b == b'\n') {
            let Ok(msg) = serde_json::from_slice::<serde_json::Value>(line) else {
                continue;
            };
            if msg["reason"] != "compiler-artifact" {
                continue;
            }
            let Some(name) = msg["target"]["name"].as_str() else {
                continue;
            };

            for file in msg["filenames"].as_array().into_iter().flatten() {
                let Some(file) = file.as_str() else { continue };
                let file = Path::new(file);

                // -L takes directories, not files.
                if let Some(dir) = file.parent() {
                    library_dirs.insert(dir.to_path_buf());
                }

                // Only requested crates are externs; a target may be reported
                // for both host and wasm, so keep the first wasm rlib.
                if requested_targets.contains(name)
                    && file.starts_with(&wasm_target)
                    && file.extension().and_then(|ext| ext.to_str()) == Some("rlib")
                {
                    externs
                        .entry(name.to_owned())
                        .or_insert_with(|| file.to_path_buf());
                }
            }
        }

        assert!(
            !externs.is_empty(),
            "cargo build reported no circuit rlibs:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let (externs, library_dirs) = snapshot(&target, externs, library_dirs);
        drop(lock);

        Self {
            root,
            externs,
            library_dirs,
        }
    }
}

/// Copies of the uplifted rlibs in `externs`, in a directory no build writes,
/// and the search path with that directory in place of the uplifted ones; called
/// under the build's lock. Copies are keyed by the files' sizes and times, so
/// test processes over one build share a single copy, and a rebuild makes a new
/// one. Cargo's other artifacts (dependencies, proc macros) sit in hashed paths
/// a fresh build leaves alone, wherever its layout puts them.
fn snapshot(
    target: &Path,
    externs: BTreeMap<String, PathBuf>,
    mut library_dirs: BTreeSet<PathBuf>,
) -> (BTreeMap<String, PathBuf>, BTreeSet<PathBuf>) {
    use std::hash::{Hash, Hasher};
    let mut key = std::collections::hash_map::DefaultHasher::new();
    for (name, path) in &externs {
        let meta =
            std::fs::metadata(path).unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
        (name, meta.len(), meta.modified().ok()).hash(&mut key);
    }
    let dir = target
        .join("harness-libs")
        .join(format!("{:016x}", key.finish()));
    if !dir.exists() {
        let tmp = dir.with_extension(format!("tmp{}", std::process::id()));
        std::fs::create_dir_all(&tmp).expect("create the harness's rlib copies");
        for (name, path) in &externs {
            std::fs::copy(path, tmp.join(format!("lib{name}.rlib")))
                .unwrap_or_else(|e| panic!("copying {}: {e}", path.display()));
        }
        std::fs::rename(&tmp, &dir).expect("publish the harness's rlib copies");
    }
    for path in externs.values() {
        if let Some(parent) = path.parent() {
            library_dirs.remove(parent);
        }
    }
    library_dirs.insert(dir.clone());
    let externs = externs
        .into_keys()
        .map(|name| {
            let copy = dir.join(format!("lib{name}.rlib"));
            (name, copy)
        })
        .collect();
    (externs, library_dirs)
}

impl WasmLibs {
    /// Add these libraries to a `rustc` command: each rlib as an `--extern`,
    /// and every artifact directory as a dependency search path.
    fn link(&self, cmd: &mut Command) {
        for (name, path) in &self.externs {
            cmd.arg("--extern")
                .arg(format!("{name}={}", path.display()));
        }
        for dir in &self.library_dirs {
            cmd.arg("-L").arg(format!("dependency={}", dir.display()));
        }
    }
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

/// `target/test-out/<out_name>`, this process's until it exits: the caller reads the
/// out dir after compiling into it, so a runner that gives each test its own process
/// (`cargo nextest`) would otherwise let another test rewrite it meanwhile. If another
/// process holds it, this one gets `<out_name>-<pid>` instead (never waiting, so two
/// tests can't deadlock on two names). Each later claim in this process gets its own
/// `<dir>.<n>`: two tests compiling the same source by the same name may run at once.
fn claim_out_dir(test_out: &Path, out_name: &str) -> PathBuf {
    static HELD: Mutex<Vec<(String, PathBuf, std::fs::File, usize)>> = Mutex::new(Vec::new());
    let mut held = HELD.lock().unwrap_or_else(|e| e.into_inner());
    if let Some((_, dir, _, claims)) = held.iter_mut().find(|(n, ..)| n == out_name) {
        *claims += 1;
        let mut name = dir.file_name().expect("an out dir name").to_os_string();
        name.push(format!(".{claims}"));
        return dir.with_file_name(name);
    }
    std::fs::create_dir_all(test_out).expect("create target/test-out");
    let path = test_out.join(format!("{out_name}.lock"));
    let file = std::fs::File::create(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let dir = match file.try_lock() {
        Ok(()) => test_out.join(out_name),
        Err(std::fs::TryLockError::WouldBlock) => {
            test_out.join(format!("{out_name}-{}", std::process::id()))
        }
        Err(std::fs::TryLockError::Error(e)) => panic!("locking {}: {e}", path.display()),
    };
    held.push((out_name.to_string(), dir.clone(), file, 0));
    dir
}

fn compile_file_stable(src: &Path, out_name: &str, field: &str, emit_json: bool) -> Compiled {
    let libs = WasmLibs::get();
    let out_dir = claim_out_dir(&libs.root.join("target/test-out"), out_name);
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
    libs.link(&mut cmd);
    let output = cmd
        .arg(src)
        .arg("-o")
        .arg(&wasm)
        .current_dir(&libs.root)
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
    // One lowering at a time in this process; the rustc runs above are each their
    // own process on their own output directory, so a test that compiles many
    // small programs (the semantics fuzzer) compiles them across the cores.
    let _guard = LOCK.lock().unwrap_or_else(|e| e.into_inner());
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn libs_link_as_externs_and_search_paths() {
        let libs = WasmLibs {
            root: PathBuf::from("/repo"),
            externs: BTreeMap::from([(
                "xark".to_string(),
                PathBuf::from("/repo/target/libxark.rlib"),
            )]),
            library_dirs: BTreeSet::from([PathBuf::from("/repo/target/deps")]),
        };
        let mut cmd = Command::new("rustc");
        libs.link(&mut cmd);
        let args: Vec<_> = cmd
            .get_args()
            .map(|a| a.to_string_lossy().into_owned())
            .collect();
        assert_eq!(
            args.join(" "),
            "--extern xark=/repo/target/libxark.rlib -L dependency=/repo/target/deps"
        );
    }
}
