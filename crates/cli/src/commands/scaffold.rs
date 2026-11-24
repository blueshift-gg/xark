//! Program scaffolding for `xark init` and `xark add program`. A scaffolder
//! owns the files a framework needs and the commands that build and test them;
//! xark prints, but does not run, the framework's commands.

use std::fs;
use std::io::{self, IsTerminal};
use std::path::Path;

use anyhow::{Context, Result, bail};
use dialoguer::{Input, Select, theme::ColorfulTheme};
use serde_json::Value;

use super::add::{package_names, write_new};
use crate::xark_project::sync_program_members;

/// A template, by its path under `templates/project/`.
macro_rules! template {
    ($path:literal) => {
        include_str!(concat!("../../templates/project/", $path))
    };
}

/// The inputs a scaffolder needs: the project, the circuit it verifies, and the
/// program's name.
pub struct ProgramScaffold<'a> {
    root: &'a Path,
    circuit: &'a str,
    name: &'a str,
}

impl<'a> ProgramScaffold<'a> {
    pub fn new(root: &'a Path, circuit: &'a str, name: &'a str) -> Result<Self> {
        Self::check_name(name)?;
        // A circuit is a directory name in `circuits/`, not a path: joining an
        // unvalidated `--circuit` would let it read outside the project.
        let mut parts = Path::new(circuit).components();
        if !matches!(parts.next(), Some(std::path::Component::Normal(_))) || parts.next().is_some()
        {
            bail!("circuit name `{circuit}` must be a single name under circuits/, not a path");
        }
        if !root
            .join("circuits")
            .join(circuit)
            .join("Cargo.toml")
            .is_file()
        {
            bail!(
                "no circuit `{circuit}` in {}: add it with `xark add circuit {circuit}`, or \
                 name another with `--circuit`",
                root.join("circuits").display()
            );
        }
        let dir = root.join("programs").join(name);
        if dir.exists() {
            bail!("{} already exists", dir.display());
        }
        let crate_name = format!("{name}-program");
        if package_names(root).contains(&crate_name) {
            bail!("the workspace already has a crate `{crate_name}`: pick another program name");
        }
        Ok(Self {
            root,
            circuit,
            name,
        })
    }

    /// Just the crate-name check, for `xark init` to run before it writes
    /// anything: the circuit [`ProgramScaffold::new`] would look for doesn't
    /// exist until the project does.
    fn check_name(name: &str) -> Result<()> {
        crate::cli::check_crate_name(name).map_err(|why| {
            anyhow::anyhow!(
                "can't name a program `{name}`: {why}: pick another name, e.g. `{}`",
                crate::cli::suggest_crate_name(name)
            )
        })
    }
}

pub struct ProgramScaffolder {
    pub id: &'static str,
    /// The menu's name for it, saying what the program is tested with.
    pub label: &'static str,
    pub scaffold: fn(&ProgramScaffold<'_>) -> Result<()>,
    /// What to run after `scaffold`: the circuit's tests, then the framework's
    /// commands for the program. xark prints them but does not run them.
    next_steps: &'static [(&'static str, &'static str)],
}

impl ProgramScaffolder {
    /// The steps to print after adding this framework's program, as
    /// `style::next_steps` rows.
    pub fn next_steps(&self) -> Vec<(String, &'static str)> {
        self.next_steps
            .iter()
            .map(|(command, what)| ((*command).to_string(), *what))
            .collect()
    }
}

pub const PINOCCHIO: ProgramScaffolder = ProgramScaffolder {
    id: "pinocchio",
    label: "Pinocchio + LiteSVM test",
    scaffold: pinocchio,
    next_steps: &[
        ("xark test", "build the circuits and run their tests"),
        ("cargo build-sbf", "the program"),
        ("npm install && npm test", "the program's LiteSVM test"),
    ],
};

pub const SCAFFOLDERS: &[ProgramScaffolder] = &[PINOCCHIO];

pub fn find(id: &str) -> Option<&'static ProgramScaffolder> {
    SCAFFOLDERS.iter().find(|s| s.id == id)
}

pub fn ids() -> Vec<&'static str> {
    SCAFFOLDERS.iter().map(|s| s.id).collect()
}

#[derive(Clone, Copy)]
pub enum ProgramChoice {
    None,
    Scaffold(&'static ProgramScaffolder),
}

pub fn is_interactive() -> bool {
    io::stdin().is_terminal() && io::stderr().is_terminal()
}

/// Resolve `--program`, otherwise prompt on a terminal or default to `none`.
pub fn resolve_program_choice(arg: Option<&str>, interactive: bool) -> Result<ProgramChoice> {
    if let Some(id) = arg {
        return choice_from_id(id);
    }
    if interactive {
        print_banner();
        choose_program()
    } else {
        Ok(ProgramChoice::None)
    }
}

fn choice_from_id(id: &str) -> Result<ProgramChoice> {
    if id == "none" {
        return Ok(ProgramChoice::None);
    }
    find(id).map(ProgramChoice::Scaffold).ok_or_else(|| {
        anyhow::anyhow!(
            "unknown program scaffolder `{id}` (known: none, {})",
            ids().join(", ")
        )
    })
}

/// The banner a terminal `xark init` opens with: the wordmark and the one-line
/// description, so the wizard reads as xark's from the first line.
fn print_banner() {
    eprintln!();
    eprintln!("  {}", crate::style::brand("xark"));
    eprintln!(
        "  {}",
        crate::style::dim("Zero-knowledge circuits in plain Rust, verified on Solana.")
    );
    eprintln!();
}

/// Ask for a scaffolder. The arrow keys move and Enter picks the highlighted
/// item; Esc cancels the wizard.
fn choose_program() -> Result<ProgramChoice> {
    let mut items: Vec<&str> = vec!["None (circuit only)"];
    items.extend(SCAFFOLDERS.iter().map(|s| s.label));
    let none = 0;
    let picked = Select::with_theme(&ColorfulTheme::default())
        .with_prompt("Add a Solana program")
        .items(&items)
        .default(none)
        .interact_opt()
        .context("asking which program to scaffold")?;
    let Some(i) = picked else {
        bail!("cancelled");
    };
    if i == none {
        Ok(ProgramChoice::None)
    } else {
        Ok(ProgramChoice::Scaffold(&SCAFFOLDERS[i - 1]))
    }
}

/// Why a program can't take this name, as a prompt shows it.
fn validate_program_name(name: &str) -> Result<(), String> {
    let name = name.trim();
    crate::cli::check_crate_name(name)
        .map_err(|why| format!("can't name a program `{name}`: {why}"))
}

/// Ask for a program name, defaulting to the circuit. A name that can't be a
/// crate is refused and asked for again, rather than failing the whole `init`.
pub fn prompt_program_name(default: &str) -> Result<String> {
    eprintln!(
        "  {}",
        crate::style::dim("The program's crate gets a `-program` suffix.")
    );

    let name = Input::<String>::with_theme(&ColorfulTheme::default())
        .with_prompt("Program name")
        .default(default.to_string())
        .validate_with(|input: &String| validate_program_name(input))
        .report(false)
        .interact_text()
        .context("asking for the program's name")?;
    let name = name.trim();

    Ok(name.to_string())
}

/// The program `xark init` scaffolds, if any: the flag's choice or the wizard's,
/// then a name — prompted on a terminal, otherwise `default_name`, the first
/// circuit's (`--circuit` can name it apart from the project). Runs before the
/// project is written, so a refused name doesn't leave one behind.
pub fn init_program(
    default_name: &str,
    program: Option<&str>,
    program_name: Option<&str>,
    interactive: bool,
) -> Result<Option<(&'static ProgramScaffolder, String)>> {
    let scaffolder = match resolve_program_choice(program, interactive)? {
        ProgramChoice::None => {
            if program_name.is_some() {
                bail!("`--program-name` needs a program (drop `--program none`, or pick one)");
            }
            return Ok(None);
        }
        ProgramChoice::Scaffold(scaffolder) => scaffolder,
    };
    let name = match program_name {
        Some(name) => name.to_string(),
        None if interactive && program.is_none() => prompt_program_name(default_name)?,
        None => default_name.to_string(),
    };
    ProgramScaffold::check_name(&name)?;
    Ok(Some((scaffolder, name)))
}

pub fn scaffold_program(
    request: &ProgramScaffold<'_>,
    scaffolder: &ProgramScaffolder,
) -> Result<()> {
    (scaffolder.scaffold)(request)
}

fn pinocchio(request: &ProgramScaffold<'_>) -> Result<()> {
    let ProgramScaffold {
        root,
        circuit,
        name,
    } = request;
    let circuit_dir = root.join("circuits").join(circuit);
    let dir = root.join("programs").join(name);
    let crate_name = format!("{name}-program");
    // A `programs/*` member left behind by a deleted program is a cargo error, and
    // `build_circuit` below loads the workspace: repair the members first.
    crate::xark_project::sync_members(root)?;

    ensure_ts_setup(root)?;
    // The program depends on the circuit's verifier crate, and the test on its
    // TypeScript client: generate them as `xark build` does. A missing key is
    // bootstrapped there; a changed dev key is rotated.
    if super::project::build_circuit(root, &circuit_dir, false).is_err() {
        bail!("couldn't build `{circuit}` and its clients (see above)");
    }
    let xark_dir = circuit_dir.join("target/xark").join(circuit);
    let schema_text =
        fs::read_to_string(xark_dir.join("schema.json")).context("reading the circuit's schema")?;
    let schema: Value = serde_json::from_str(&schema_text)?;
    let input_schema =
        xark_schema::Schema::parse(&schema_text).map_err(|e| anyhow::anyhow!("{e}"))?;
    let circuit_fn = schema["circuit"].as_str().unwrap_or(circuit).to_string();
    // The name `xark export` gave the crate: a new one is `<name>-client`
    // (`shielded_transact` → `shielded-transact-client`); a 0.4.0 project's keeps
    // the `-verifier` its program already depends on.
    let verifier =
        crate::xark_project::read_pkg_name(&root.join("clients").join(circuit).join("rust"))
            .unwrap_or_else(|| super::export::client_crate_name(circuit));
    let pascal = super::client::ts::pascal(&circuit_fn);
    let error = format!(
        "{}Error",
        super::client::ts::pascal(&name.replace('-', "_"))
    );
    let (inputs, inputs_doc, test) = sample_inputs(&schema, &input_schema, &pascal);

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
            .replace("{{test}}", test)
    };
    let test_path = format!("tests/{name}.test.ts");
    let test_text = fill(template!("tests/program.test.ts"));
    let keep_test = root.join(&test_path).is_file();
    if keep_test {
        let existing = fs::read_to_string(root.join(&test_path))
            .with_context(|| format!("reading {}", root.join(&test_path).display()))?;
        if existing != test_text {
            bail!(
                "{test_path} already exists and is not the generated test for `{name}` \
                 verifying `{circuit}`: remove or update it, then run `xark add program {name}` \
                 again"
            );
        }
    }
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
    sync_program_members(root)?;
    if keep_test {
        eprintln!(
            "{} keeping your {test_path} (it matches the generated test)",
            crate::style::tag()
        );
    } else {
        write_new(root, &test_path, &test_text)?;
    }
    // The program's framework owns its build and tests: give this program its own
    // workflow, scoped to it, so programs from another framework are left alone
    // and the project's `ci.yml` stays circuit-only.
    let workflow = format!(".github/workflows/{name}-program.yml");
    if root.join(&workflow).is_file() {
        eprintln!("{} keeping your {workflow}", crate::style::tag());
    } else {
        let text = fill(template!("github/pinocchio-program.yml"))
            .replace("{{xark_version}}", env!("CARGO_PKG_VERSION"));
        write_new(root, &workflow, &text)?;
    }
    Ok(())
}

/// The TypeScript tests' setup, once per project: `package.json`, `tsconfig.json`
/// and `vitest.config.ts`. Written before the client is generated, so it finds
/// the runtime listed.
fn ensure_ts_setup(root: &Path) -> Result<()> {
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
    Ok(())
}

/// The test's inputs, their doc, and the test function: the starter circuit's
/// known answer, run; or the circuit's `inputs.example.json` (camelCase, as the
/// client takes them) to fill in, its test skipped until then so the project's
/// tests (and CI) stay green.
fn sample_inputs(
    schema: &Value,
    input_schema: &xark_schema::Schema,
    pascal: &str,
) -> (String, String, &'static str) {
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
            "test",
        );
    }
    let example = input_schema
        .inputs_example()
        .and_then(|t| serde_json::from_str::<Value>(&t).ok())
        .unwrap_or(Value::Object(Default::default()));
    // Placeholders aren't values of the input types: the cast goes once they're
    // replaced.
    (
        format!(
            "{} as unknown as {pascal}Inputs",
            serde_json::to_string_pretty(&camel_keys(example)).unwrap_or_default()
        ),
        "/**\n * Replace each placeholder with a value the circuit accepts, then remove the\n * test's `.skip`.\n */\n".into(),
        "test.skip",
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

#[cfg(test)]
mod tests {
    use super::*;

    fn is_pinocchio(choice: ProgramChoice) -> bool {
        matches!(choice, ProgramChoice::Scaffold(s) if s.id == PINOCCHIO.id)
    }

    #[test]
    fn the_flag_picks_a_scaffolder_by_id() {
        assert!(is_pinocchio(choice_from_id("pinocchio").unwrap()));
        assert!(matches!(
            choice_from_id("none").unwrap(),
            ProgramChoice::None
        ));
        assert!(choice_from_id("nope").is_err());
    }

    #[test]
    fn a_program_name_must_be_a_crate_name() {
        assert!(validate_program_name("verifier").is_ok());
        assert!(validate_program_name("Bad Name").is_err());
        assert!(validate_program_name("1st").is_err());
    }

    /// xark prints but never runs a framework's commands: a scaffolder that prints
    /// none leaves the user with files nothing says how to build or test.
    #[test]
    fn every_scaffolder_says_how_to_build_and_test_its_program() {
        for scaffolder in SCAFFOLDERS {
            let steps = scaffolder.next_steps();
            assert!(
                !steps.is_empty(),
                "`{}` prints no next steps",
                scaffolder.id
            );
            assert!(
                steps
                    .iter()
                    .all(|(command, what)| !command.is_empty() && !what.is_empty()),
                "`{}` has an empty next step",
                scaffolder.id
            );
        }
    }

    /// A project root with one circuit crate, for the request checks.
    fn project_with(circuit: &str) -> std::path::PathBuf {
        let root = std::env::temp_dir().join(format!(
            "xark-scaffold-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(root.join("circuits").join(circuit)).unwrap();
        std::fs::write(
            root.join("circuits").join(circuit).join("Cargo.toml"),
            format!("[package]\nname = \"{circuit}\"\nversion = \"0.1.0\"\n"),
        )
        .unwrap();
        root
    }

    #[test]
    fn init_program_asks_only_on_a_terminal_and_needs_a_program_for_a_name() {
        assert!(
            init_program("demo", Some("none"), None, false)
                .unwrap()
                .is_none()
        );
        assert!(init_program("demo", None, None, false).unwrap().is_none());
        assert!(init_program("demo", Some("none"), Some("app"), false).is_err());

        let (scaffolder, name) = init_program("demo", Some("pinocchio"), None, false)
            .unwrap()
            .expect("a program");
        assert_eq!(scaffolder.id, PINOCCHIO.id);
        assert_eq!(name, "demo");

        let (_, named) = init_program("demo", Some("pinocchio"), Some("app"), false)
            .unwrap()
            .expect("a program");
        assert_eq!(named, "app");
        assert!(init_program("demo", Some("pinocchio"), Some("Bad Name"), false).is_err());
    }

    #[test]
    fn a_program_defaults_to_the_circuit_it_verifies() {
        let root = project_with("foo");
        // `xark init demo --circuit foo`: the first circuit is `foo`, whatever the
        // directory is called, so the program defaults to `foo` too.
        let (_, name) = init_program("foo", Some("pinocchio"), None, false)
            .unwrap()
            .expect("a program");
        assert_eq!(name, "foo");
        let request = ProgramScaffold::new(&root, "foo", &name).expect("a valid request");
        assert_eq!(request.circuit, "foo");
        assert_eq!(request.name, "foo");
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn a_program_request_is_checked_before_a_scaffolder_sees_it() {
        let root = project_with("claim");
        assert!(ProgramScaffold::new(&root, "claim", "app").is_ok());
        assert!(ProgramScaffold::new(&root, "../claim", "app").is_err());
        assert!(ProgramScaffold::new(&root, "claim/sub", "app").is_err());
        assert!(ProgramScaffold::new(&root, "missing", "app").is_err());
        assert!(ProgramScaffold::new(&root, "claim", "Bad Name").is_err());
        std::fs::create_dir_all(root.join("programs/app")).unwrap();
        assert!(ProgramScaffold::new(&root, "claim", "app").is_err());
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn a_program_name_a_crate_already_has_is_refused() {
        let root = project_with("claim");
        std::fs::create_dir_all(root.join("programs/other")).unwrap();
        std::fs::write(
            root.join("programs/other/Cargo.toml"),
            "[package]\nname = \"app-program\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        assert!(ProgramScaffold::new(&root, "claim", "app").is_err());
        std::fs::remove_dir_all(root).unwrap();
    }
}
