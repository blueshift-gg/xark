//! `xark add circuit|program <name>` — grow a project `xark init` made: circuits in
//! `circuits/`, Solana programs in `programs/`, and each circuit's generated clients
//! in `clients/<circuit>/`, members of one Cargo workspace; see `docs/projects.md`.

use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use clap::{Args, Subcommand};

use crate::xark_project::{PROJECT_FILE, project_root, sync_members};

#[derive(Args, Debug)]
pub struct AddArgs {
    #[command(subcommand)]
    pub what: What,
}

#[derive(Subcommand, Debug)]
pub enum What {
    /// A circuit in `circuits/<name>/`: the crate `xark init` makes.
    Circuit {
        /// Its name: the crate's, and its `#[circuit]` fn's.
        name: String,
    },
    /// A Pinocchio program in `programs/<name>/` that verifies a circuit's proofs,
    /// with a LiteSVM test in `tests/<name>.test.ts`. Generates the circuit's
    /// clients first if they're missing.
    Program {
        /// Its name: the crate is `<name>-program`.
        name: String,
        /// The circuit it verifies. Defaults to the one named `<name>`.
        #[arg(long)]
        circuit: Option<String>,
        /// Program scaffolder: `pinocchio`.
        #[arg(long, default_value = "pinocchio")]
        framework: String,
    },
}

/// A template, by its path under `templates/project/`.
macro_rules! template {
    ($path:literal) => {
        include_str!(concat!("../../templates/project/", $path))
    };
}

pub fn run(args: AddArgs) -> Result<()> {
    let cwd = std::env::current_dir().context("resolving current directory")?;
    let Some(root) = project_root(&cwd) else {
        bail!(
            "not in a xark project (no {PROJECT_FILE} here or above): start one with `xark \
             init <name>`"
        );
    };
    super::project::check_release(&root);
    match args.what {
        What::Circuit { name } => add_circuit(&root, &name),
        What::Program {
            name,
            circuit,
            framework,
        } => {
            let circuit = circuit.unwrap_or_else(|| name.clone());
            let scaffolder = super::scaffold::find(&framework).ok_or_else(|| {
                anyhow::anyhow!(
                    "unknown program framework `{framework}` (known: {})",
                    super::scaffold::ids().join(", ")
                )
            })?;
            let request = super::scaffold::ProgramScaffold::new(&root, &circuit, &name)?;
            super::scaffold::scaffold_program(&request, scaffolder)?;
            eprintln!(
                "✅ Solana program `{name}-program` in {}, verifying `{circuit}`",
                root.join("programs").join(&name).display()
            );
            eprintln!("{}", crate::style::next_steps(&scaffolder.next_steps()));
            Ok(())
        }
    }
}

/// `xark init`: make `dir` a project (its `xark.toml`, workspace, `.gitignore` and
/// editor settings) with a starter circuit, `circuits/<name>/`.
pub fn init_project(dir: &Path, name: &str) -> Result<()> {
    if dir.join(PROJECT_FILE).exists() {
        bail!(
            "{} is already a xark project: run `xark add` to add a circuit or a program",
            dir.display()
        );
    }
    if dir.join("Cargo.toml").exists() {
        bail!(
            "{} already has a Cargo.toml: start a project in a new directory (`xark init \
             <name>`)",
            dir.display()
        );
    }
    check_circuit_name(dir, name)?;
    let circuit = dir.join("circuits").join(name);
    if circuit.exists() {
        bail!("{} already exists", circuit.display());
    }
    // Everything checked: nothing below refuses halfway, leaving half a project.
    let xark = xark_ir::major_minor(env!("CARGO_PKG_VERSION"));
    write_new(
        dir,
        PROJECT_FILE,
        &template!("xark.toml").replace("{{xark}}", &xark),
    )?;
    write_new(dir, "Cargo.toml", template!("Cargo.toml.tmpl"))?;
    // A directory may already have these (a `git init`, a template repository):
    // `.gitignore` gets the lines it's missing, the others are kept as they are.
    let ignore = dir.join(".gitignore");
    let ours = template!("gitignore");
    match fs::read_to_string(&ignore) {
        Ok(theirs) => {
            let missing: Vec<&str> = ours
                .lines()
                .filter(|l| !l.starts_with('#') && !theirs.lines().any(|t| t.trim() == *l))
                .collect();
            if !missing.is_empty() {
                let sep = if theirs.ends_with('\n') || theirs.is_empty() {
                    ""
                } else {
                    "\n"
                };
                fs::write(&ignore, format!("{theirs}{sep}{}\n", missing.join("\n")))
                    .with_context(|| format!("writing {}", ignore.display()))?;
            }
        }
        Err(_) => write_new(dir, ".gitignore", ours)?,
    }
    // rust-analyzer runs `xark check` at the root: `cargo check` over the workspace,
    // then xark's validation of each circuit. `rust-analyzer.toml` is the
    // editor-agnostic form; `.vscode/settings.json` covers VS Code.
    let cmd = "[\"xark\", \"check\", \".\", \"--message-format=json\"]";
    for (path, text) in [
        (
            ".github/workflows/ci.yml",
            template!("github/ci.yml").replace("{{xark_version}}", env!("CARGO_PKG_VERSION")),
        ),
        (
            "rust-analyzer.toml",
            format!(
                "# Run xark's subset validator on save so unsupported constructs show inline.\n\
                 # Needs `xark` on PATH. Replaces rust-analyzer's `cargo check`, which `xark\n\
                 # check` runs over the whole workspace too.\n\
                 [check]\noverrideCommand = {cmd}\n"
            ),
        ),
        (
            ".vscode/settings.json",
            format!("{{\n  \"rust-analyzer.check.overrideCommand\": {cmd}\n}}\n"),
        ),
    ] {
        if dir.join(path).exists() {
            eprintln!(
                "{} keeping your {path} (xark's would run `xark build --check` and \
                 `xark test`, or `xark check` for rust-analyzer)",
                crate::style::tag()
            );
        } else {
            write_new(dir, path, &text)?;
        }
    }
    if crate::cli::scaffold_circuit(&circuit, true).is_err() {
        bail!("couldn't scaffold the circuit (see above)");
    }
    sync_members(dir)
}

fn add_circuit(root: &Path, name: &str) -> Result<()> {
    check_circuit_name(root, name)?;
    let dir = root.join("circuits").join(name);
    if dir.exists() {
        bail!("{} already exists", dir.display());
    }
    if crate::cli::scaffold_circuit(&dir, true).is_err() {
        bail!("couldn't scaffold the circuit (see above)");
    }
    sync_members(root)?;
    eprintln!(
        "{}",
        crate::style::next_steps(&[
            (
                "xark test".to_string(),
                "build the circuits and run their tests"
            ),
            (
                format!("xark add program {name}"),
                "a Solana program that verifies its proofs, with a LiteSVM test",
            ),
        ])
    );
    Ok(())
}

/// A circuit's name: a crate name (one path component), and not one the crates
/// xark adds beside it could clash with in the workspace (`<name>-program`,
/// `<name>-client`).
pub fn check_circuit_name(root: &Path, name: &str) -> Result<()> {
    crate::cli::check_crate_name(name)
        .map_err(|why| anyhow::anyhow!("can't name a circuit `{name}`: {why}"))?;
    for suffix in ["-program", "_program", "-client", "_client"] {
        if name.ends_with(suffix) {
            bail!(
                "can't name a circuit `{name}`: `xark add` names its program `<name>-program` \
                 and its client crate `<name>-client`, so a circuit's name can't end in \
                 `{suffix}`"
            );
        }
    }
    let names = package_names(root);
    for taken in [name.to_string(), super::export::client_crate_name(name)] {
        if names.contains(&taken) {
            bail!("the workspace already has a crate `{taken}`: pick another name");
        }
    }
    Ok(())
}

/// The package names of the project's crates.
pub(crate) fn package_names(root: &Path) -> Vec<String> {
    let mut dirs = super::project::members(root, "circuits");
    dirs.extend(super::project::members(root, "programs"));
    dirs.extend(
        std::fs::read_dir(root.join("clients"))
            .into_iter()
            .flatten()
            .flatten()
            .map(|e| e.path().join("rust"))
            .filter(|p| p.join("Cargo.toml").is_file()),
    );
    dirs.iter()
        .filter_map(|d| crate::xark_project::read_pkg_name(d))
        .collect()
}

/// Write `text` to `dir/rel`, refusing to replace a file.
pub(crate) fn write_new(dir: &Path, rel: &str, text: &str) -> Result<()> {
    let path: PathBuf = dir.join(rel);
    if path.exists() {
        bail!("{} already exists", path.display());
    }
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
    }
    fs::write(&path, text).with_context(|| format!("writing {}", path.display()))
}
