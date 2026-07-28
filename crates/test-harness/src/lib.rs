//! Shared test harness: compile a circuit source with the `xark` compiler and
//! read back its emitted artifacts (no shell script). Used by the snapshot
//! suite and every gadget crate's `vec.rs`.
//!
//! Handles the repo's build layout once per test process. `crates/lang` (the
//! compiler) is excluded from the root workspace and needs nightly
//! (`rustc_private`) with its own `target/`; the gadget crates are root-workspace
//! members. So this builds:
//!   1. the gadget rlibs (`-Zalways-encode-mir`, so their MIR is inlinable) into
//!      an isolated `target/xark-compile`, apart from the root `target/` so a
//!      `cargo test -p <gadget>` can't collide with them (rustc E0514);
//!   2. the compiler binary in `crates/lang`'s own target (a rustc *driver*, so
//!      its deps needn't match the circuit's).
//!
//! Then it invokes the compiler with an `--extern` per gadget rlib.

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
        let cp = xark_ir::function_decode::expand_function_blob(&bytes)
            .unwrap_or_else(|e| panic!("expand circuit.xbc: {e}"));
        xark_ir::minimize::minimize_with_fill(&cp.to_r1cs(), usize::MAX)
            .constraints
            .len()
    }

    /// Check that native `inputs` **satisfy** this compiled circuit — the
    /// in-memory analogue of [`xark_prover::Circuit::check`], for a circuit
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

    /// **Streaming** satisfiability check — like [`check`](Self::check) but
    /// verifies the witness by streaming each R1CS row out of the compact
    /// `circuit.xbc` (never materializing the flat system), so peak memory is the
    /// witness + one row and the walk is parallel. Skips the global
    /// under-constraint analyzer (a separate soundness pass that must
    /// materialize) — use [`check`](Self::check) when you want that too.
    pub fn check_satisfies(&self, inputs: &[(&str, &dyn bignum::LeafInput)]) -> Result<(), String> {
        let (bytes, id_inputs) = self.resolve_inputs(inputs)?;
        xark_ir::function_decode::stream_check(&bytes, &id_inputs)
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

/// The nightly channel the compiler is pinned to (in `crates/rustc`, the
/// rustc-driver crate, not root).
fn nightly_channel(root: &Path) -> String {
    let toml =
        std::fs::read_to_string(root.join("crates/rustc/rust-toolchain.toml")).unwrap_or_default();
    for line in toml.lines() {
        let t = line.trim();
        if t.starts_with("channel")
            && let Some(v) = t.split('"').nth(1)
        {
            return v.to_string();
        }
    }
    "nightly".to_string()
}

const RUSTFLAGS: &str = "--allow=unexpected_cfgs -Zalways-encode-mir -Zmir-opt-level=0";

/// Build the compiler binary + gadget rlibs once; return `(binary, deps_dir)`.
fn built() -> &'static (PathBuf, PathBuf) {
    static BUILT: OnceLock<(PathBuf, PathBuf)> = OnceLock::new();
    BUILT.get_or_init(|| {
        let root = workspace_root();
        let target = root.join("target/xark-compile");
        let channel = nightly_channel(&root);

        // 1. The rustc-driver binary in crates/rustc's own target (excluded
        //    nightly pkg with its own pinned `rust-toolchain.toml`). Built *first*
        //    so it can serve as `RUSTC` for the gadget rlibs below.
        let ok = Command::new("cargo")
            // `--features debug` compiles in the diagnostic markers the tests require
            // on; a `--features` build still lands at `target/release/xark-rustc`.
            .args(["build", "--release", "--features", "debug"])
            .env("RUSTUP_TOOLCHAIN", &channel)
            .env("RUSTFLAGS", RUSTFLAGS)
            .env_remove("CARGO_TARGET_DIR")
            .current_dir(root.join("crates/rustc"))
            .status()
            .expect("run cargo build (compiler)")
            .success();
        assert!(ok, "building the xark-rustc driver failed");
        let driver = root.join("crates/rustc/target/release/xark-rustc");

        // 2. Gadget rlibs → isolated target (all root-member `xark-*` crates
        //    except the non-circuit libraries and excluded packages). Built with
        //    the driver as `RUSTC` (like the real `xark build`): it reports the
        //    `xark` cfg on `--print cfg`, so Cargo gates each crate's
        //    `[target.'cfg(not(xark))'.dependencies]` (host prover/num-bigint) out
        //    and the sources compile their lean circuit shape — exactly what links
        //    into the circuit crate. No `RUSTUP_TOOLCHAIN`: the driver resolves its
        //    own pinned sysroot.
        let mut args = vec!["build".to_string(), "--release".to_string()];
        let mut names: Vec<String> = std::fs::read_dir(root.join("crates"))
            .expect("read crates/")
            .filter_map(|e| e.ok())
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .filter(|n| {
                n.starts_with("xark-")
                    && !matches!(
                        n.as_str(),
                        "xark"
                            | "xark-ir"
                            | "xark-prover"
                            | "xark-test-harness"
                            | "xark-cli"
                            | "xark-rustc"
                            | "xark-wasm"
                    )
            })
            .collect();
        names.sort();
        for n in names {
            args.push("-p".to_string());
            args.push(n);
        }
        let ok = Command::new("cargo")
            .args(&args)
            .env("RUSTC", &driver)
            .env("RUSTFLAGS", RUSTFLAGS)
            .env("CARGO_TARGET_DIR", &target)
            .current_dir(&root)
            .status()
            .expect("run cargo build (gadgets)")
            .success();
        assert!(ok, "building gadget rlibs failed");

        // The rustc_driver shim (invoked directly with `--r1cs-out`), not the
        // `xark` CLI — the driver lives in a separate binary/crate now.
        (driver, target.join("release/deps"))
    })
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

fn compile_file_inner(src: &Path, out_name: &str, field: &str, emit_json: bool) -> Compiled {
    let _guard = LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let (bin, deps) = built();
    let root = workspace_root();
    let out_dir = root.join("target/test-out").join(out_name);
    let _ = std::fs::remove_dir_all(&out_dir);

    let mut cmd = Command::new(bin);
    // Soundness gate: the driver is built with `--features debug`, so
    // `XARK_VERIFY=1` makes every compiled circuit self-check that its bytecode
    // artifact expands byte-identically to the flat R1CS. The prover proves the
    // artifact, so an artifact≠flat drift (e.g. a revived mul-product missing from
    // the artifact) is a forgeable under-constraint — caught on every test build
    // (the drift is invisible to solve tests, which use the flat).
    cmd.env("XARK_VERIFY", "1");
    cmd.args([
        "--crate-type=lib",
        "--edition=2021",
        "-Z",
        "mir-opt-level=0",
    ]);
    for e in externs(deps) {
        cmd.arg("--extern").arg(e);
    }
    cmd.arg("-L")
        .arg(format!("dependency={}", deps.display()))
        .arg("--field")
        .arg(field);
    if emit_json {
        cmd.arg("--emit-json");
    }
    let output = cmd
        .arg(src)
        .arg("--r1cs-out")
        .arg(&out_dir)
        .current_dir(&root)
        .output()
        .expect("run xark compiler");

    Compiled {
        status_success: output.status.success(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        out_dir,
    }
}

/// Compile a circuit source **string** (written to a temp file) to `circuit.xbc`.
pub fn compile_source(name: &str, src: &str, field: &str) -> Compiled {
    let path = std::env::temp_dir().join(format!("xark_harness_{name}.rs"));
    std::fs::write(&path, src).expect("write temp source");
    compile_file(&path, name, field)
}

/// [`compile_source`] but with `--emit-json` (for tests reading `r1cs.json` etc.).
pub fn compile_source_json(name: &str, src: &str, field: &str) -> Compiled {
    let path = std::env::temp_dir().join(format!("xark_harness_{name}.rs"));
    std::fs::write(&path, src).expect("write temp source");
    compile_file_json(&path, name, field)
}
