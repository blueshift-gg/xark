use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use serde::Deserialize;

#[derive(Debug, Clone)]
pub struct NoirProject {
    root: PathBuf,
    package_name: String,
}

impl NoirProject {
    /// Walk up from `start` looking for `Nargo.toml`. Returns `None` when
    /// no manifest is found, `Err` only for a malformed one.
    pub fn find_at(start: &Path) -> Result<Option<Self>> {
        let mut dir = start.to_path_buf();
        if !dir.is_dir() {
            dir.pop();
        }
        loop {
            let candidate = dir.join("Nargo.toml");
            if candidate.is_file() {
                return Ok(Some(Self::from_manifest(candidate)?));
            }
            if !dir.pop() {
                return Ok(None);
            }
        }
    }

    /// Parse from an explicit `Nargo.toml` path.
    #[inline]
    fn from_manifest(manifest: PathBuf) -> Result<Self> {
        let root = manifest
            .parent()
            .map(Path::to_path_buf)
            .ok_or_else(|| anyhow::anyhow!("Invalid Nargo.toml path"))?;

        let content = std::fs::read_to_string(&manifest)
            .with_context(|| format!("Failed to read {}", manifest.display()))?;

        let parsed: NargoManifest = toml::from_str(&content)
            .with_context(|| format!("Failed to parse {}", manifest.display()))?;

        let package_name = parsed
            .package
            .and_then(|p| p.name)
            .filter(|n| !n.trim().is_empty())
            .ok_or_else(|| anyhow::anyhow!("Missing [package].name in {}", manifest.display()))?;

        Ok(Self { root, package_name })
    }

    pub fn artifact_path(&self) -> PathBuf {
        self.target_dir()
            .join(format!("{}.json", self.package_name))
    }

    pub fn export_dir(&self) -> PathBuf {
        self.target_dir()
            .join(format!("{}-xark-verifier", self.package_name))
    }

    pub fn witness_path(&self) -> PathBuf {
        self.target_dir().join(format!("{}.gz", self.package_name))
    }

    pub fn proving_key_path(&self) -> PathBuf {
        self.groth16_dir().join("proving_key.bin")
    }

    pub fn verifying_key_path(&self) -> PathBuf {
        self.groth16_dir().join("verifying_key.bin")
    }

    pub fn proof_path(&self) -> PathBuf {
        self.groth16_dir().join("proof.bin")
    }

    pub fn public_inputs_path(&self) -> PathBuf {
        self.groth16_dir().join("public_inputs.json")
    }

    // --- Private helpers ---

    fn target_dir(&self) -> PathBuf {
        self.root.join("target")
    }

    pub fn groth16_dir(&self) -> PathBuf {
        self.target_dir().join("groth16")
    }

    /// Look for a `.ptau` file in standard project locations.
    ///
    /// Searches `<root>/ptau/*.ptau`, `<root>/ceremony/*.ptau`, then
    /// `<root>/*.ptau`. Returns the first match found, or `None` if no
    /// `.ptau` is present.
    pub fn find_ptau(&self) -> Option<PathBuf> {
        for dir in [
            self.root.join("ptau"),
            self.root.join("ceremony"),
            self.root.clone(),
        ] {
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

#[derive(Debug, Deserialize)]
struct NargoManifest {
    package: Option<NargoPackage>,
}

#[derive(Debug, Deserialize)]
struct NargoPackage {
    name: Option<String>,
}
