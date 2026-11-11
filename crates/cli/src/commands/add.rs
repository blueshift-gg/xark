//! `xark add circuit|program <name>` — grow a project `xark init` made: circuits in
//! `circuits/`, Solana programs in `programs/`, and each circuit's generated clients
//! in `clients/<circuit>/`, members of one Cargo workspace; see `docs/projects.md`.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, bail};
use clap::{Args, Subcommand};
use serde_json::Value;

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
    match args.what {
        What::Circuit { name } => add_circuit(&root, &name),
        What::Program { name, circuit } => {
            let circuit = circuit.unwrap_or_else(|| name.clone());
            add_program(&root, &name, &circuit)
        }
    }
}

/// `xark init`: make `dir` a project (its `xark.toml`, workspace, `.gitignore` and
/// editor settings) with a starter circuit, `circuits/<name>/`.
pub fn init_project(dir: &Path, name: &str) -> Result<()> {
    if dir.join(PROJECT_FILE).exists() {
        bail!(
            "{} is already a xark project: `xark add` grows it",
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
    let xark = xark_ir::major_minor(env!("CARGO_PKG_VERSION"));
    write_new(
        dir,
        PROJECT_FILE,
        &template!("xark.toml").replace("{{xark}}", &xark),
    )?;
    write_new(dir, "Cargo.toml", template!("Cargo.toml.tmpl"))?;
    write_new(dir, ".gitignore", template!("gitignore"))?;
    // rust-analyzer runs `xark check` at the root: `cargo check` over the workspace,
    // then xark's validation of each circuit. `rust-analyzer.toml` is the
    // editor-agnostic form; `.vscode/settings.json` covers VS Code.
    let cmd = "[\"xark\", \"check\", \".\", \"--message-format=json\"]";
    write_new(
        dir,
        "rust-analyzer.toml",
        &format!(
            "# Run xark's subset validator on save so unsupported constructs show inline.\n\
             # Needs `xark` on PATH. Replaces rust-analyzer's `cargo check`, which `xark\n\
             # check` runs over the whole workspace too.\n\
             [check]\noverrideCommand = {cmd}\n"
        ),
    )?;
    write_new(
        dir,
        ".vscode/settings.json",
        &format!("{{\n  \"rust-analyzer.check.overrideCommand\": {cmd}\n}}\n"),
    )?;
    if crate::cli::scaffold_circuit(&dir.join("circuits").join(name), true).is_err() {
        bail!("couldn't scaffold the circuit (see above)");
    }
    sync_members(dir)
}

fn add_circuit(root: &Path, name: &str) -> Result<()> {
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

fn add_program(root: &Path, name: &str, circuit: &str) -> Result<()> {
    let circuit_dir = root.join("circuits").join(circuit);
    if !circuit_dir.join("Cargo.toml").is_file() {
        bail!(
            "no circuit `{circuit}` in {}: add it with `xark add circuit {circuit}`, or name \
             another with `--circuit`",
            root.join("circuits").display()
        );
    }
    let dir = root.join("programs").join(name);
    if dir.exists() {
        bail!("{} already exists", dir.display());
    }
    let crate_name = format!("{name}-program");
    crate::cli::check_crate_name(&crate_name)
        .map_err(|why| anyhow::anyhow!("can't name a crate `{crate_name}`: {why}"))?;

    // The TypeScript tests' setup, once per project (first, so the client
    // generated below finds the runtime listed).
    let project = root
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("xark-project")
        .to_string();
    let npm = env!("CARGO_PKG_VERSION");
    for (path, text) in [
        ("package.json", template!("package.json")),
        ("tsconfig.json", template!("tsconfig.json")),
        ("vitest.config.ts", template!("vitest.config.ts")),
    ] {
        if !root.join(path).exists() {
            let text = text
                .replace("{{project}}", &project)
                .replace("{{xark_npm}}", npm);
            write_new(root, path, &text)?;
        }
    }
    // The program depends on the circuit's verifier crate, and the test on its
    // TypeScript client: generate them when they're missing.
    let clients = root.join("clients").join(circuit);
    if !clients.join("rust/Cargo.toml").is_file() || !clients.join("ts").is_dir() {
        let path = circuit_dir.display().to_string();
        for step in [
            vec!["build", &path],
            vec!["setup", &path],
            vec!["export", &path],
            vec!["client", &path],
        ] {
            xark(root, &step)?;
        }
    }
    let xark_dir = circuit_dir.join("target/xark").join(circuit);
    let schema: Value = serde_json::from_str(
        &fs::read_to_string(xark_dir.join("schema.json"))
            .context("reading the circuit's schema")?,
    )?;
    let circuit_fn = schema["circuit"].as_str().unwrap_or(circuit).to_string();
    let verifier = format!("{circuit}-verifier");
    let pascal = super::client::ts::pascal(&circuit_fn);
    let error = format!(
        "{}Error",
        super::client::ts::pascal(&name.replace('-', "_"))
    );
    let (inputs, inputs_doc) = sample_inputs(&schema, &xark_dir, &pascal);

    let fill = |t: &str| {
        t.replace("{{name}}", name)
            .replace("{{crate}}", &crate_name)
            .replace("{{circuit}}", circuit)
            .replace("{{circuit_file}}", &circuit_fn)
            .replace("{{verifier}}", &verifier)
            .replace("{{verifier_ident}}", &verifier.replace('-', "_"))
            .replace("{{Error}}", &error)
            .replace("{{Pascal}}", &pascal)
            .replace("{{inputs}}", &inputs)
            .replace("{{inputs_doc}}", &inputs_doc)
    };
    for (path, text) in [
        ("Cargo.toml", template!("program/Cargo.toml.tmpl")),
        ("src/lib.rs", template!("program/src/lib.rs")),
        ("src/errors.rs", template!("program/src/errors.rs")),
        (
            "src/instructions/mod.rs",
            template!("program/src/instructions/mod.rs"),
        ),
        (
            "src/instructions/verify.rs",
            template!("program/src/instructions/verify.rs"),
        ),
    ] {
        write_new(&dir, path, &fill(text))?;
    }
    sync_members(root)?;
    write_new(
        root,
        &format!("tests/{name}.test.ts"),
        &fill(template!("tests/program.test.ts")),
    )?;

    eprintln!(
        "{} added program `{crate_name}` in {}, verifying `{circuit}`",
        crate::style::tag(),
        dir.display()
    );
    eprintln!(
        "{}",
        crate::style::next_steps(&[
            (
                "xark build".to_string(),
                "the circuits, their clients, then the programs (cargo build-sbf)",
            ),
            (
                "npm install && xark test".to_string(),
                "the circuits' tests, then prove and verify onchain in LiteSVM",
            ),
        ])
    );
    Ok(())
}

/// The test's inputs: the starter circuit's known answer, or the circuit's
/// `inputs.example.json` (camelCase, as the client takes them) to fill in.
fn sample_inputs(schema: &Value, xark_dir: &Path, pascal: &str) -> (String, String) {
    let names: Vec<(&str, &str)> = schema["inputs"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|i| Some((i["name"].as_str()?, i["visibility"].as_str()?)))
        .collect();
    if names == [("secret", "private"), ("result", "public")] {
        return (
            "{ secret: 3, result: 9 }".into(),
            "/** 3 squared is 9: the starter circuit's statement. */\n".into(),
        );
    }
    let example = fs::read_to_string(xark_dir.join("inputs.example.json"))
        .ok()
        .and_then(|t| serde_json::from_str::<Value>(&t).ok())
        .unwrap_or(Value::Object(Default::default()));
    // Placeholders aren't values of the input types: the cast goes once they're
    // replaced.
    (
        format!(
            "{} as unknown as {pascal}Inputs",
            serde_json::to_string_pretty(&camel_keys(example)).unwrap_or_default()
        ),
        "/** Replace each placeholder with a value the circuit accepts. */\n".into(),
    )
}

fn camel_keys(v: Value) -> Value {
    match v {
        Value::Object(m) => Value::Object(
            m.into_iter()
                .map(|(k, v)| (xark_schema::camel(&k), camel_keys(v)))
                .collect(),
        ),
        Value::Array(a) => Value::Array(a.into_iter().map(camel_keys).collect()),
        v => v,
    }
}

/// Run this `xark` with `args` in `dir`.
fn xark(dir: &Path, args: &[&str]) -> Result<()> {
    let exe = std::env::current_exe().context("finding the xark binary")?;
    let status = Command::new(exe)
        .args(args)
        .env(crate::style::NESTED, "1")
        .current_dir(dir)
        .status()
        .with_context(|| format!("running `xark {}`", args.join(" ")))?;
    if !status.success() {
        bail!("`xark {}` failed (see above)", args.join(" "));
    }
    Ok(())
}

/// Write `text` to `dir/rel`, refusing to replace a file.
fn write_new(dir: &Path, rel: &str, text: &str) -> Result<()> {
    let path: PathBuf = dir.join(rel);
    if path.exists() {
        bail!("{} already exists", path.display());
    }
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
    }
    fs::write(&path, text).with_context(|| format!("writing {}", path.display()))
}
