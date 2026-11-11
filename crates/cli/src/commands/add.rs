//! `xark add circuit|program <name>` — grow a project: circuits in `circuits/`,
//! Solana programs in `programs/`, and each circuit's generated clients in
//! `clients/<circuit>/`, members of one Cargo workspace. The first `add` makes the
//! project where it runs (a `xark.toml`, the workspace `Cargo.toml`, a
//! `.gitignore`); see `docs/projects.md`.

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
    let root = match project_root(&cwd) {
        Some(root) => root,
        None => {
            new_project(&cwd)?;
            cwd
        }
    };
    match args.what {
        What::Circuit { name } => add_circuit(&root, &name),
        What::Program { name, circuit } => {
            let circuit = circuit.unwrap_or_else(|| name.clone());
            add_program(&root, &name, &circuit)
        }
    }
}

/// Make `dir` a project: its `xark.toml`, workspace and `.gitignore`.
fn new_project(dir: &Path) -> Result<()> {
    if dir.join("Cargo.toml").exists() {
        bail!(
            "{} already has a Cargo.toml: a project is a new directory (`mkdir my-app && cd \
             my-app && xark add circuit …`)",
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
    eprintln!(
        "{} made a project in {}: circuits/, programs/ and clients/ in one workspace",
        crate::style::tag(),
        dir.display()
    );
    Ok(())
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
                format!("xark test circuits/{name}"),
                "build the circuit and run its tests",
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

    // The TypeScript tests' setup, once per project.
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
    eprintln!(
        "{} added program `{crate_name}` in {}, verifying `{circuit}`",
        crate::style::tag(),
        dir.display()
    );
    eprintln!(
        "{}",
        crate::style::next_steps(&[
            (
                format!("cargo build-sbf --manifest-path programs/{name}/Cargo.toml"),
                "build the program (into target/deploy/)",
            ),
            (
                "npm install && npm test".to_string(),
                "prove with the TypeScript client and verify onchain in LiteSVM",
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
