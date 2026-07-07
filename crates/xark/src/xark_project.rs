//! Path inference for the `xark` backend subcommands — the unified analog of
//! master's Noir `noir_project` inference, keyed on the `target/xark/` layout
//! that `xark build` writes.
//!
//! `xark build <crate>` emits `circuit.json` + `r1cs.json` under
//! `<crate>/target/xark/`; `xark setup`/`prove`/`verify`/`export`/`inspect`
//! then read and write their artifacts from that same directory. Rather than
//! make the user retype those paths, each command resolves an [`XarkProject`]
//! from an optional path argument (defaulting to the current directory) and
//! derives every file path from it. Explicit `--…` flags always override the
//! derived defaults.

use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

/// A resolved xark build output directory (`<crate>/target/xark/`) plus the
/// canonical artifact paths derived from it.
#[derive(Debug, Clone)]
pub struct XarkProject {
    /// The `target/xark/` directory holding the build output + backend keys.
    pub xark_dir: PathBuf,
}

impl XarkProject {
    /// Resolve a project from an optional path argument.
    ///
    /// `path` may be:
    /// * a crate directory (containing `Cargo.toml` and/or `target/xark/`) —
    ///   the output dir is `<path>/target/xark/`;
    /// * a `target/xark/` directory itself (containing `r1cs.json`) — used
    ///   directly;
    /// * omitted — the search starts from the current directory and walks up
    ///   to the nearest crate root.
    pub fn resolve(path: Option<PathBuf>) -> Result<Self> {
        let base = match path {
            Some(p) => p,
            None => std::env::current_dir().context("resolving current directory")?,
        };
        Ok(Self {
            xark_dir: resolve_xark_dir(&base),
        })
    }

    pub fn circuit_json(&self) -> PathBuf {
        self.xark_dir.join("circuit.json")
    }

    pub fn r1cs_json(&self) -> PathBuf {
        self.xark_dir.join("r1cs.json")
    }

    pub fn proving_key(&self) -> PathBuf {
        self.xark_dir.join("pk.bin")
    }

    pub fn verifying_key(&self) -> PathBuf {
        self.xark_dir.join("vk.bin")
    }

    pub fn proof(&self) -> PathBuf {
        self.xark_dir.join("proof.bin")
    }

    pub fn public_inputs(&self) -> PathBuf {
        self.xark_dir.join("public_inputs.json")
    }

    /// Default output directory for `xark export`'s generated verifier crate.
    pub fn export_dir(&self) -> PathBuf {
        self.xark_dir.join("verifier")
    }

    /// Auto-detect a Powers-of-Tau (`.ptau`) transcript for production setup.
    ///
    /// Searches `target/xark/`, `target/xark/ptau/`, the crate root, and
    /// `<root>/ptau/`, returning the first `*.ptau` found.
    pub fn find_ptau(&self) -> Option<PathBuf> {
        let mut dirs = vec![self.xark_dir.clone(), self.xark_dir.join("ptau")];
        // `target/xark/` → crate root is two levels up (`../../`).
        if let Some(root) = self.xark_dir.parent().and_then(Path::parent) {
            dirs.push(root.to_path_buf());
            dirs.push(root.join("ptau"));
        }
        for dir in dirs {
            if let Ok(entries) = std::fs::read_dir(&dir) {
                for entry in entries.flatten() {
                    let path = entry.path();
                    if path.extension().is_some_and(|e| e == "ptau") {
                        return Some(path);
                    }
                }
            }
        }
        None
    }
}

/// Resolve the `target/xark/` output directory from a user-supplied base path.
fn resolve_xark_dir(base: &Path) -> PathBuf {
    // 1. `base` is already a build output dir (has r1cs.json / circuit.json).
    if base.join("r1cs.json").is_file() || base.join("circuit.json").is_file() {
        return base.to_path_buf();
    }
    // 2. `base` is a crate dir whose build output already exists.
    let direct = base.join("target").join("xark");
    if direct.join("r1cs.json").is_file() || direct.is_dir() {
        return direct;
    }
    // 3. Walk up from `base` to the nearest crate root (a `Cargo.toml`) and use
    //    its `target/xark/`.
    let mut dir = base.to_path_buf();
    if !dir.is_dir() {
        dir.pop();
    }
    loop {
        if dir.join("Cargo.toml").is_file() {
            return dir.join("target").join("xark");
        }
        if !dir.pop() {
            break;
        }
    }
    // 4. Fallback: treat `base` itself as the output dir (setup will surface a
    //    clear "missing r1cs.json" error if it is wrong).
    base.to_path_buf()
}
