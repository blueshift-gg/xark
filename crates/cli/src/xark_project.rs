//! Path inference for the `xark` backend subcommands, keyed on the
//! `target/xark/` layout `xark build` writes.
//!
//! Each command resolves an [`XarkProject`] from an optional path argument
//! (defaulting to the current directory) and derives every artifact path from
//! it, so the user need not retype them. Explicit `--…` flags always override
//! the derived defaults.

use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};

/// A resolved xark build output directory (`<crate>/target/xark/`) plus the
/// canonical artifact paths derived from it.
#[derive(Debug, Clone)]
pub struct XarkProject {
    /// The `target/xark/` directory holding the build output + backend keys.
    pub xark_dir: PathBuf,
}

impl XarkProject {
    /// Resolve a project from an optional path argument: a crate directory, a
    /// `target/xark/` directory itself, or omitted (walk up from the current
    /// directory to the nearest crate root).
    pub fn resolve(path: Option<PathBuf>) -> Result<Self> {
        let base = match path {
            Some(p) if !p.exists() => bail!("no such directory: {}", p.display()),
            // Absolute, so the walk up to the crate root below can leave it.
            Some(p) => p.canonicalize().unwrap_or(p),
            None => std::env::current_dir().context("resolving current directory")?,
        };
        Ok(Self {
            xark_dir: resolve_xark_dir(&base)?,
        })
    }

    pub fn circuit_xbc(&self) -> PathBuf {
        self.xark_dir.join("circuit.xbc")
    }

    pub fn proving_key(&self) -> PathBuf {
        self.key_dir().join("pk.bin")
    }

    pub fn verifying_key(&self) -> PathBuf {
        self.key_dir().join("vk.bin")
    }

    /// Where `xark setup` puts the keys (and their `metadata.json`). In a project,
    /// `keys/<name>/` at its root, committed: a verifier embedding the key is
    /// committed too, so a key only in the gitignored `target/` would be replaced
    /// on every fresh clone. Otherwise the build's own directory.
    pub fn key_dir(&self) -> PathBuf {
        match (self.project_root(), self.name()) {
            (Some(root), Some(name)) if self.crate_dir().is_some() => root.join("keys").join(name),
            _ => self.xark_dir.clone(),
        }
    }

    /// The verifying key the generated verifier crate embeds, when there is one.
    pub fn committed_verifier_key(&self) -> Option<PathBuf> {
        let vk = self.clients_dir().join("rust/verifying_key.solana.bin");
        vk.is_file().then_some(vk)
    }

    /// Making a key where there's none is only for a circuit nothing verifies yet:
    /// a verifier that embeds a key (`clients/…/rust/`) means it was lost (a fresh
    /// clone of a project whose keys weren't committed), and a new one would quietly
    /// stop matching the deployed program and everyone's proofs.
    pub fn may_make_key(&self) -> Result<()> {
        if let Some(vk) = self.committed_verifier_key() {
            bail!(
                "no key in {}, but {} embeds one: restore the keys (a project commits \
                 `keys/`), or make new ones on purpose with `xark setup` (the deployed \
                 program then needs the new verifier)",
                crate::commands::shown(&self.key_dir()),
                crate::commands::shown(&vk)
            );
        }
        Ok(())
    }

    pub fn proof(&self) -> PathBuf {
        self.xark_dir.join("proof.bin")
    }

    pub fn public_inputs(&self) -> PathBuf {
        self.xark_dir.join("public_inputs.bin")
    }

    /// The crate a `target/xark/<name>/` directory belongs to (`None` for a build
    /// output elsewhere, e.g. `xark build --out`).
    pub fn crate_dir(&self) -> Option<PathBuf> {
        let target = self.xark_dir.parent()?.parent()?;
        (target.file_name()? == "target").then(|| target.parent().map(PathBuf::from))?
    }

    /// Where the generated clients go by default: `rust/` for `xark export`'s
    /// verifier crate and `ts/` for `xark client`'s. In a project (a `xark.toml`
    /// above the crate), `clients/<name>/` at its root, a member of its workspace;
    /// otherwise `<crate>/clients/`, beside the circuit's sources (the verifier
    /// crate nested with its own `[workspace]`, so the circuit crate neither builds
    /// nor packages it). Either way git tracks them and `cargo clean` leaves them. A
    /// build output outside a crate's `target/` keeps them there.
    pub fn clients_dir(&self) -> PathBuf {
        match (self.crate_dir(), self.project_root(), self.name()) {
            (Some(_), Some(root), Some(name)) => root.join("clients").join(name),
            (Some(krate), _, _) => krate.join("clients"),
            _ => self.xark_dir.join("clients"),
        }
    }

    /// The project the circuit is one of: the directory with a `xark.toml` whose
    /// `circuits/` holds its crate. (Another crate somewhere under a project isn't
    /// one of its circuits, and keeps its keys and clients beside it.)
    pub fn project_root(&self) -> Option<PathBuf> {
        let krate = std::path::absolute(self.crate_dir()?).ok()?;
        let circuits = krate.parent()?;
        let root = circuits.parent()?;
        (circuits.file_name()? == "circuits" && root.join(PROJECT_FILE).is_file())
            .then(|| root.to_path_buf())
    }

    /// The package the build is named after (`target/xark/<name>/`).
    pub fn name(&self) -> Option<String> {
        Some(self.xark_dir.file_name()?.to_string_lossy().into_owned())
    }

    /// Auto-detect a Powers-of-Tau (`.ptau`) transcript for production setup.
    ///
    /// Searches `target/xark/<name>/`, `target/xark/`, and the crate root, each
    /// with its `ptau/` subdir, returning the first `*.ptau` found.
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
                    if path.extension().is_some_and(|e| e == "ptau") && path.is_file() {
                        return Some(path);
                    }
                }
            }
        }
        None
    }
}

/// The project `dir` is in: the nearest directory, `dir` itself or above it, with a
/// `xark.toml`.
pub fn project_root(dir: &Path) -> Option<PathBuf> {
    let dir = std::path::absolute(dir).ok()?;
    dir.ancestors()
        .find(|d| d.join(PROJECT_FILE).is_file())
        .map(Path::to_path_buf)
}

/// What makes a directory a project.
pub const PROJECT_FILE: &str = "xark.toml";

/// The project's workspace members: each of `circuits/*`, `programs/*` and
/// `clients/*/rust` that holds a crate. Cargo reads a glob that matches nothing as
/// a path that isn't there, so one is listed only once something is in it. The
/// `default-members` are the programs, so a bare `cargo build-sbf` (or `cargo
/// test`) at the root builds them alone: built together with the circuits, the
/// circuits' host dependencies would join the SBF build. Only these globs are
/// added or removed; anything else in the manifest (members of your own, comments,
/// layout) stays as it is.
pub fn sync_members(root: &Path) -> Result<()> {
    const OURS: [&str; 3] = ["circuits/*", "programs/*", "clients/*/rust"];
    let has_crate = |pattern: &str| -> bool {
        let (dir, rest) = pattern.split_once("/*").unwrap_or((pattern, ""));
        std::fs::read_dir(root.join(dir)).is_ok_and(|entries| {
            entries.flatten().any(|e| {
                e.path()
                    .join(rest.trim_start_matches('/'))
                    .join("Cargo.toml")
                    .is_file()
            })
        })
    };
    let manifest = root.join("Cargo.toml");
    let text = std::fs::read_to_string(&manifest)
        .with_context(|| format!("reading {}", manifest.display()))?;
    let mut doc: toml_edit::DocumentMut = text
        .parse()
        .with_context(|| format!("reading {}", manifest.display()))?;
    let Some(ws) = doc.get_mut("workspace").and_then(|w| w.as_table_like_mut()) else {
        bail!("{} has no [workspace]", manifest.display());
    };
    // `key`'s entries: ours that hold a crate, then whatever else was there.
    let mut set = |key: &str, ours: &[&str]| {
        let others: Vec<String> = ws
            .get(key)
            .and_then(|v| v.as_array())
            .into_iter()
            .flatten()
            .filter_map(|v| v.as_str())
            .filter(|v| !OURS.contains(v))
            .map(str::to_string)
            .collect();
        let wanted: Vec<String> = ours
            .iter()
            .filter(|p| has_crate(p))
            .map(|p| p.to_string())
            .chain(others)
            .collect();
        if wanted.is_empty() && key == "default-members" {
            ws.remove(key);
            return;
        }
        // Changed in place, so the comments around it stay.
        match ws.get_mut(key).and_then(|v| v.as_array_mut()) {
            Some(array) => {
                let current: Vec<&str> = array.iter().filter_map(|v| v.as_str()).collect();
                if current != wanted {
                    array.clear();
                    array.extend(wanted.iter().map(String::as_str));
                }
            }
            None => {
                ws.insert(key, toml_edit::value(toml_edit::Array::from_iter(wanted)));
            }
        }
    };
    set("members", &OURS);
    set("default-members", &["programs/*"]);
    let new = doc.to_string();
    if new != text {
        std::fs::write(&manifest, new)
            .with_context(|| format!("writing {}", manifest.display()))?;
    }
    Ok(())
}

/// Resolve the name-scoped `target/xark/<pkg-name>/` output directory from a
/// user-supplied base path, mirroring the per-circuit subdir layout `xark build`
/// writes.
fn resolve_xark_dir(base: &Path) -> Result<PathBuf> {
    // 0. `base` is a project's root: its circuit, when it has one.
    if base.join(PROJECT_FILE).is_file() {
        let circuits = crate::commands::project::members(base, "circuits");
        return match circuits.as_slice() {
            [one] => Ok(scoped_dir(one)),
            [] => bail!(
                "the project at {} has no circuits yet: `xark add circuit <name>`",
                base.display()
            ),
            _ => {
                let names: Vec<String> = circuits
                    .iter()
                    .filter_map(|c| Some(format!("circuits/{}", c.file_name()?.to_str()?)))
                    .collect();
                bail!(
                    "the project has {} circuits: name one ({})",
                    circuits.len(),
                    names.join(", ")
                )
            }
        };
    }
    // 1. `base` is already a scoped output dir (a `target/xark/<name>/` holding
    //    circuit.xbc, the artifact every build writes) — use it directly.
    if base.join("circuit.xbc").is_file() {
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
    //    clear "run `xark build` first" error if it is wrong).
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
/// it (a `<name>/` holding `circuit.xbc`). Returns `Ok(None)` if
/// there are none; errors if there is more than one (the user must name one).
fn single_named_subdir(base: &Path) -> Result<Option<PathBuf>> {
    if !base.is_dir() {
        return Ok(None);
    }
    let mut candidates: Vec<PathBuf> = Vec::new();
    if let Ok(entries) = std::fs::read_dir(base) {
        for entry in entries.flatten() {
            let p = entry.path();
            if p.is_dir() && p.join("circuit.xbc").is_file() {
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
        if in_package && let Some(rest) = line.strip_prefix("name") {
            let rest = rest.trim_start();
            if let Some(val) = rest.strip_prefix('=') {
                let val = val.trim();
                let val = if let Some(rest) = val.strip_prefix('"') {
                    rest.split_once('"').map(|(name, _)| name)?
                } else {
                    val.strip_prefix('\'')?
                        .split_once('\'')
                        .map(|(name, _)| name)?
                };
                if !val.is_empty() {
                    return Some(val.to_string());
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::XarkProject;
    use std::fs;
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicUsize, Ordering};

    static NEXT_DIR: AtomicUsize = AtomicUsize::new(0);

    struct TestDir(PathBuf);

    impl TestDir {
        fn new() -> Self {
            let id = NEXT_DIR.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("xark-ptau-discovery-{}-{id}", std::process::id()));
            fs::create_dir_all(&path).unwrap();
            Self(path)
        }

        fn xark_dir(&self) -> PathBuf {
            let path = self.0.join("target/xark/circuit");
            fs::create_dir_all(&path).unwrap();
            path
        }
    }

    impl Drop for TestDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn skips_directory_before_searching_ptau_subdirectory() {
        let temp = TestDir::new();
        let xark_dir = temp.xark_dir();
        fs::create_dir(xark_dir.join("fake.ptau")).unwrap();
        let real_file = xark_dir.join("ptau/ceremony.ptau");
        fs::create_dir_all(real_file.parent().unwrap()).unwrap();
        fs::write(&real_file, b"transcript").unwrap();

        assert_eq!(XarkProject { xark_dir }.find_ptau(), Some(real_file));
    }

    #[test]
    fn ignores_directory_when_no_transcript_file_exists() {
        let temp = TestDir::new();
        let xark_dir = temp.xark_dir();
        fs::create_dir(xark_dir.join("fake.ptau")).unwrap();

        assert_eq!(XarkProject { xark_dir }.find_ptau(), None);
    }

    #[test]
    fn skips_shared_directory_before_searching_crate_root() {
        let temp = TestDir::new();
        let xark_dir = temp.xark_dir();
        fs::create_dir(xark_dir.parent().unwrap().join("fake.ptau")).unwrap();
        let real_file = temp.0.join("ceremony.ptau");
        fs::write(&real_file, b"transcript").unwrap();

        assert_eq!(XarkProject { xark_dir }.find_ptau(), Some(real_file));
    }

    #[test]
    fn still_finds_a_ptau_file_in_the_first_search_directory() {
        let temp = TestDir::new();
        let xark_dir = temp.xark_dir();
        let real_file = xark_dir.join("ceremony.ptau");
        fs::write(&real_file, b"transcript").unwrap();

        assert_eq!(XarkProject { xark_dir }.find_ptau(), Some(real_file));
    }

    #[test]
    fn package_name_with_inline_comment_scopes_build_output_correctly() {
        let temp = TestDir::new();
        fs::write(
            temp.0.join("Cargo.toml"),
            "[package]\nname = \"example-circuit\" # comment after the value\nversion = \"0.1.0\"\n",
        )
        .unwrap();

        let project = XarkProject::resolve(Some(temp.0.clone())).unwrap();
        let crate_dir = temp.0.canonicalize().unwrap();

        assert_eq!(
            project.xark_dir,
            crate_dir.join("target/xark/example-circuit")
        );
    }

    #[test]
    fn package_name_accepts_a_toml_literal_string() {
        let temp = TestDir::new();
        fs::write(
            temp.0.join("Cargo.toml"),
            "[package]\nname = 'example-circuit' # comment\nversion = \"0.1.0\"\n",
        )
        .unwrap();

        assert_eq!(
            super::read_pkg_name(&temp.0).as_deref(),
            Some("example-circuit")
        );
    }
}
