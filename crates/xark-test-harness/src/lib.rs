//! Shared test harness: compile a circuit source with the `xark` compiler and
//! read back its emitted artifacts — **no shell script**. Used by the snapshot
//! suite and by every gadget crate's `vec.rs`.
//!
//! It handles the repo's awkward build layout for you, once per test process:
//! `crates/xark` (the compiler) is *excluded* from the root workspace and needs
//! **nightly** (`rustc_private`) with its own `target/`, while the gadget crates
//! are root-workspace members. So this builds:
//!   1. the gadget rlibs (with `-Zalways-encode-mir` so their MIR is inlinable)
//!      into an isolated `target/xark-compile`, kept apart from the root `target/`
//!      so a stable `cargo test -p <gadget>` can't collide with them (rustc E0514);
//!   2. the compiler binary in `crates/xark`'s own target (it's a rustc *driver*,
//!      so its own deps needn't match the circuit's).
//! Then it invokes the compiler with an `--extern` per gadget rlib.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};

use xark_ir::primitive::{self, PrimitiveProgram};

/// The result of compiling one circuit source.
pub struct Compiled {
    pub status_success: bool,
    pub stderr: String,
    pub out_dir: PathBuf,
}

impl Compiled {
    /// Parse the emitted primitive program (`circuit.json`).
    pub fn program(&self) -> PrimitiveProgram {
        let json = std::fs::read_to_string(self.out_dir.join("circuit.json"))
            .unwrap_or_else(|e| panic!("read {}: {e}", self.out_dir.join("circuit.json").display()));
        primitive::from_json(&json).expect("valid circuit.json")
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

/// The nightly channel the compiler is pinned to (in `crates/xark`, not root).
fn nightly_channel(root: &Path) -> String {
    let toml = std::fs::read_to_string(root.join("crates/xark/rust-toolchain.toml")).unwrap_or_default();
    for line in toml.lines() {
        let t = line.trim();
        if t.starts_with("channel") {
            if let Some(v) = t.split('"').nth(1) {
                return v.to_string();
            }
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

        // 1. Gadget rlibs → isolated target (all root-member `xark-*` crates
        //    except the non-circuit libraries and the excluded packages).
        let mut args = vec!["build".to_string(), "--release".to_string()];
        let mut names: Vec<String> = std::fs::read_dir(root.join("crates"))
            .expect("read crates/")
            .filter_map(|e| e.ok())
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .filter(|n| {
                n.starts_with("xark-")
                    && !matches!(
                        n.as_str(),
                        "xark" | "xark-ir" | "xark-prover" | "xark-test-harness"
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
            .env("RUSTUP_TOOLCHAIN", &channel)
            .env("RUSTFLAGS", RUSTFLAGS)
            .env("CARGO_TARGET_DIR", &target)
            .current_dir(&root)
            .status()
            .expect("run cargo build (gadgets)")
            .success();
        assert!(ok, "building gadget rlibs failed");

        // 2. Compiler binary in crates/xark's own target (excluded nightly pkg).
        let ok = Command::new("cargo")
            .args(["build", "--release", "--features", "cli"])
            .env("RUSTUP_TOOLCHAIN", &channel)
            .env("RUSTFLAGS", RUSTFLAGS)
            .env_remove("CARGO_TARGET_DIR")
            .current_dir(root.join("crates/xark"))
            .status()
            .expect("run cargo build (compiler)")
            .success();
        assert!(ok, "building the xark compiler failed");

        (
            root.join("crates/xark/target/release/xark"),
            target.join("release/deps"),
        )
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
        let Some(stem) = file.strip_prefix("lib").and_then(|s| s.strip_suffix(".rlib")) else {
            continue;
        };
        let Some((name, _hash)) = stem.rsplit_once('-') else { continue };
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

/// Compile a circuit source **file** to R1CS + IR under `target/test-out/<out_name>`.
pub fn compile_file(src: &Path, out_name: &str, field: &str) -> Compiled {
    let _guard = LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let (bin, deps) = built();
    let root = workspace_root();
    let out_dir = root.join("target/test-out").join(out_name);
    let _ = std::fs::remove_dir_all(&out_dir);

    let mut cmd = Command::new(bin);
    cmd.args(["--crate-type=lib", "--edition=2021", "-Z", "mir-opt-level=0"]);
    for e in externs(deps) {
        cmd.arg("--extern").arg(e);
    }
    let output = cmd
        .arg("-L")
        .arg(format!("dependency={}", deps.display()))
        .arg("--field")
        .arg(field)
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

/// Compile a circuit source **string** (written to a temp file) to R1CS + IR.
pub fn compile_source(name: &str, src: &str, field: &str) -> Compiled {
    let path = std::env::temp_dir().join(format!("xark_harness_{name}.rs"));
    std::fs::write(&path, src).expect("write temp source");
    compile_file(&path, name, field)
}
