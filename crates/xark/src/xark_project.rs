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

use anyhow::{bail, Context, Result};

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
            xark_dir: resolve_xark_dir(&base)?,
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
        self.xark_dir.join("public_inputs.bin")
    }

    /// The circuit's name — the `target/xark/<name>/` subdirectory name, which
    /// `xark build` scopes to the crate's `[package] name`. Falls back to
    /// `"circuit"` when the output dir has no usable file name.
    pub fn circuit_name(&self) -> String {
        self.xark_dir
            .file_name()
            .and_then(|s| s.to_str())
            .filter(|s| !s.is_empty() && *s != "xark")
            .unwrap_or("circuit")
            .to_string()
    }

    /// The circuit's entry function name, from the `entry` marker `xark build`
    /// writes beside the artifacts. Drives the IDL / generated struct name.
    ///
    /// Falls back to the directory (crate) name when the marker is absent (older
    /// builds) or the entry is the *generic* `circuit` — so a `pub fn circuit`
    /// circuit keeps its meaningful crate name, while a named entry
    /// (`pub fn my_square`) drives the name itself.
    pub fn entry_name(&self) -> String {
        std::fs::read_to_string(self.xark_dir.join("entry"))
            .ok()
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty() && s != "circuit")
            .unwrap_or_else(|| self.circuit_name())
    }

    /// The machine-readable circuit interface (`<name>.idl.json`) — the single
    /// ABI file a client generator or integrator consumes. Named by
    /// [`Self::entry_name`] so the filename matches the const/type baked inside
    /// it (and what `xark client` writes).
    pub fn idl_json(&self) -> PathBuf {
        self.xark_dir
            .join(format!("{}.idl.json", self.entry_name()))
    }

    /// The typed TypeScript IDL (`<name>.idl.ts`) — the same IDL as an
    /// `as const` constant + exported type, so `xark-client` infers the
    /// circuit's shape at compile time (the Anchor `Program<Idl>` pattern).
    pub fn idl_ts(&self) -> PathBuf {
        self.xark_dir.join(format!("{}.idl.ts", self.entry_name()))
    }

    /// Key metadata sidecar (`metadata.json`) written by setup.
    pub fn metadata(&self) -> PathBuf {
        self.xark_dir.join("metadata.json")
    }

    /// Default output directory for `xark export`'s generated verifier crate.
    pub fn export_dir(&self) -> PathBuf {
        self.xark_dir.join("verifier")
    }

    /// Default output directory for `xark client`'s generated TypeScript client.
    pub fn client_dir(&self) -> PathBuf {
        self.xark_dir.join("client")
    }

    /// Auto-detect a Powers-of-Tau (`.ptau`) transcript for production setup.
    ///
    /// Searches `target/xark/`, `target/xark/ptau/`, the crate root, and
    /// `<root>/ptau/`, returning the first `*.ptau` found.
    pub fn find_ptau(&self) -> Option<PathBuf> {
        let mut dirs = vec![self.xark_dir.clone(), self.xark_dir.join("ptau")];
        // `target/xark/<pkg>/` → the shared `target/xark/` is one level up …
        if let Some(shared) = self.xark_dir.parent() {
            dirs.push(shared.to_path_buf());
            dirs.push(shared.join("ptau"));
            // … and the crate root is three levels up (`../../../`).
            if let Some(root) = shared.parent().and_then(Path::parent) {
                dirs.push(root.to_path_buf());
                dirs.push(root.join("ptau"));
            }
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

/// Resolve the name-scoped `target/xark/<pkg-name>/` output directory from a
/// user-supplied base path.
///
/// `xark build` now writes each circuit's artifacts to its own subdirectory
/// (`target/xark/<pkg-name>/`) so a workspace of circuits stays isolated. This
/// resolver mirrors that layout.
fn resolve_xark_dir(base: &Path) -> Result<PathBuf> {
    // 1. `base` is already a scoped output dir (a `target/xark/<name>/` holding
    //    r1cs.json / circuit.json) — use it directly.
    if base.join("r1cs.json").is_file() || base.join("circuit.json").is_file() {
        return Ok(base.to_path_buf());
    }
    // 2. `base` is a crate dir → `target/xark/<pkg-name>/`.
    if base.join("Cargo.toml").is_file() {
        return Ok(scoped_dir(base));
    }
    // 3. `base` is a bare `target/xark/` holding one or more `<name>/` subdirs.
    //    A single subdir resolves unambiguously; several are ambiguous.
    if let Some(dir) = single_named_subdir(base)? {
        return Ok(dir);
    }
    // 4. Walk up from `base` to the nearest crate root (a `Cargo.toml`) and use
    //    its `target/xark/<pkg-name>/`.
    let mut dir = base.to_path_buf();
    if !dir.is_dir() {
        dir.pop();
    }
    loop {
        if dir.join("Cargo.toml").is_file() {
            return Ok(scoped_dir(&dir));
        }
        if !dir.pop() {
            break;
        }
    }
    // 5. Fallback: treat `base` itself as the output dir (setup will surface a
    //    clear "missing r1cs.json" error if it is wrong).
    Ok(base.to_path_buf())
}

/// The name-scoped output dir for a crate: `<crate>/target/xark/<pkg-name>/`,
/// where `<pkg-name>` is the crate's `[package] name` (falling back to the
/// directory name when the `Cargo.toml` can't be parsed).
fn scoped_dir(crate_dir: &Path) -> PathBuf {
    let target_xark = crate_dir.join("target").join("xark");
    let name = read_pkg_name(crate_dir).unwrap_or_else(|| {
        crate_dir
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("circuit")
            .to_string()
    });
    target_xark.join(name)
}

/// When `base` is a bare `target/xark/`, find the single circuit subdir under
/// it (a `<name>/` holding r1cs.json / circuit.json). Returns `Ok(None)` if
/// there are none; errors if there is more than one (the user must name one).
fn single_named_subdir(base: &Path) -> Result<Option<PathBuf>> {
    if !base.is_dir() {
        return Ok(None);
    }
    let mut candidates: Vec<PathBuf> = Vec::new();
    if let Ok(entries) = std::fs::read_dir(base) {
        for entry in entries.flatten() {
            let p = entry.path();
            if p.is_dir() && (p.join("r1cs.json").is_file() || p.join("circuit.json").is_file()) {
                candidates.push(p);
            }
        }
    }
    candidates.sort();
    match candidates.len() {
        0 => Ok(None),
        1 => Ok(Some(candidates.remove(0))),
        _ => {
            let names: Vec<String> = candidates
                .iter()
                .filter_map(|p| p.file_name().and_then(|s| s.to_str()).map(String::from))
                .collect();
            bail!(
                "ambiguous circuit: {} holds multiple built circuits ({}). \
                 Point at one explicitly, e.g. `{}/{}`.",
                base.display(),
                names.join(", "),
                base.display(),
                names.first().map(String::as_str).unwrap_or("<name>"),
            )
        }
    }
}

/// Parse a crate's `[package] name` out of its `Cargo.toml`. Best-effort line
/// scanner (no TOML dependency): finds the first `name = "..."` after a
/// `[package]` header. Returns `None` if the file is missing or unparseable.
pub(crate) fn read_pkg_name(crate_dir: &Path) -> Option<String> {
    let text = std::fs::read_to_string(crate_dir.join("Cargo.toml")).ok()?;
    let mut in_package = false;
    for raw in text.lines() {
        let line = raw.trim();
        if line.starts_with('[') {
            in_package = line == "[package]";
            continue;
        }
        if in_package {
            if let Some(rest) = line.strip_prefix("name") {
                let rest = rest.trim_start();
                if let Some(val) = rest.strip_prefix('=') {
                    let val = val.trim().trim_matches('"').trim_matches('\'');
                    if !val.is_empty() {
                        return Some(val.to_string());
                    }
                }
            }
        }
    }
    None
}
