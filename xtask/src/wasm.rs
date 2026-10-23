//! `cargo xtask wasm`: xark-wasm's JavaScript packages, into `crates/wasm/dist/`.
//!
//! * `nodejs`, `web`, `bundler`: `wasm-pack build --target <it>`, into `dist/node`,
//!   `dist/web`, `dist/bundler`;
//! * `module`: `wasm-bindgen --target module` (workerd needs a self-instantiating
//!   `WebAssembly.Module`, which wasm-pack can't emit), into `dist/module`;
//! * `all`: `nodejs`, `web` and `module`, what the npm package ships.

use std::path::PathBuf;
use std::process::Command;

use anyhow::{Context, Result, bail};

#[derive(Clone, Copy, PartialEq, clap::ValueEnum)]
pub enum Target {
    Nodejs,
    Web,
    Bundler,
    Module,
    All,
}

#[derive(clap::Args)]
pub struct Args {
    /// The package to build.
    #[arg(value_enum, default_value = "bundler")]
    target: Target,
    /// A debug build (faster to build, much slower to run).
    #[arg(long)]
    dev: bool,
}

pub fn run(args: Args) -> Result<()> {
    let targets = match args.target {
        Target::All => vec![Target::Nodejs, Target::Web, Target::Module],
        t => vec![t],
    };
    for t in targets {
        let out = match t {
            Target::Module => module(args.dev)?,
            t => wasm_pack(t, args.dev)?,
        };
        println!(
            "built {} ({})",
            out.display(),
            if args.dev { "dev" } else { "release" }
        );
    }
    Ok(())
}

fn crate_dir() -> PathBuf {
    crate::root().join("crates/wasm")
}

/// Run `cmd`, its output shown as it goes.
fn status(cmd: &mut Command) -> Result<()> {
    let s = cmd.status().with_context(|| format!("running {cmd:?}"))?;
    if !s.success() {
        bail!("{cmd:?} failed ({s})");
    }
    Ok(())
}

/// `wasm-pack build --target <t>`, into `dist/<dir>`; returns `dist/<dir>`.
fn wasm_pack(t: Target, dev: bool) -> Result<PathBuf> {
    let (target, dir) = match t {
        Target::Nodejs => ("nodejs", "dist/node"),
        Target::Web => ("web", "dist/web"),
        Target::Bundler => ("bundler", "dist/bundler"),
        _ => unreachable!("not a wasm-pack target"),
    };
    status(
        Command::new("wasm-pack")
            .args(["build", "--target", target])
            .arg(if dev { "--dev" } else { "--release" })
            .args(["--out-dir", dir, "--no-pack"])
            .current_dir(crate_dir()),
    )
    .context("wasm-pack (install it with `cargo install wasm-pack --locked`)")?;
    let out = crate_dir().join(dir);
    // wasm-pack's `.gitignore` of everything would keep the files out of `npm pack`.
    let _ = std::fs::remove_file(out.join(".gitignore"));
    Ok(out)
}

/// The `module` package, with the `wasm-bindgen` CLI the library was locked to.
fn module(dev: bool) -> Result<PathBuf> {
    let want = locked_wasm_bindgen()?;
    let have = Command::new("wasm-bindgen")
        .arg("--version")
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .and_then(|v| v.split_whitespace().nth(1).map(str::to_string));
    // The CLI must match the library baked into the .wasm exactly, or the JS glue
    // it writes doesn't match the module (and fails only at runtime).
    match have {
        None => {
            println!("wasm-bindgen CLI not found; installing {want}");
            status(Command::new("cargo").args([
                "install",
                "wasm-bindgen-cli",
                "--version",
                &want,
                "--locked",
            ]))?;
        }
        Some(have) if have != want => bail!(
            "wasm-bindgen CLI {have}, but Cargo.lock has {want}: \
             cargo install wasm-bindgen-cli --version {want} --locked --force"
        ),
        Some(_) => {}
    }

    let profile = if dev { "debug" } else { "release" };
    let mut build = Command::new("cargo");
    build
        .args([
            "build",
            "-p",
            "xark-wasm",
            "--target",
            "wasm32-unknown-unknown",
        ])
        .current_dir(crate::root());
    if !dev {
        build.arg("--release");
    }
    status(&mut build)?;
    let out = crate_dir().join("dist/module");
    let wasm = crate::target_dir().join(format!("wasm32-unknown-unknown/{profile}/xark_wasm.wasm"));
    status(
        Command::new("wasm-bindgen")
            .arg(&wasm)
            .arg("--out-dir")
            .arg(&out)
            .args(["--target", "module", "--out-name", "xark_wasm"]),
    )?;
    // workerd and esbuild reject the `import source` keyword: a plain import.
    let js = out.join("xark_wasm.js");
    let text = std::fs::read_to_string(&js)?;
    std::fs::write(&js, rewrite_import_source(&text))?;

    // A release ships wasm-opt's module, as the bundler package has it.
    if !dev {
        let bundler = wasm_pack(Target::Bundler, false)?;
        std::fs::copy(
            bundler.join("xark_wasm_bg.wasm"),
            out.join("xark_wasm_bg.wasm"),
        )?;
    }
    Ok(out)
}

/// `import source x from …` lines as `import x from …`.
fn rewrite_import_source(js: &str) -> String {
    js.split_inclusive('\n')
        .map(|l| match l.strip_prefix("import source ") {
            Some(rest) => format!("import {rest}"),
            None => l.to_string(),
        })
        .collect()
}

/// The `wasm-bindgen` version in the workspace's `Cargo.lock`.
fn locked_wasm_bindgen() -> Result<String> {
    let lock = std::fs::read_to_string(crate::root().join("Cargo.lock"))?;
    version_in_lock(&lock, "wasm-bindgen").context("no wasm-bindgen in Cargo.lock")
}

fn version_in_lock(lock: &str, name: &str) -> Option<String> {
    let mut lines = lock.lines();
    while let Some(l) = lines.next() {
        if l == format!("name = \"{name}\"") {
            let v = lines.next()?.strip_prefix("version = \"")?;
            return Some(v.trim_end_matches('"').to_string());
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::{rewrite_import_source, version_in_lock};

    #[test]
    fn reads_the_locked_version() {
        let lock = "[[package]]\nname = \"wasm-bindgen\"\nversion = \"0.2.100\"\n";
        assert_eq!(
            version_in_lock(lock, "wasm-bindgen").as_deref(),
            Some("0.2.100")
        );
        assert_eq!(version_in_lock(lock, "serde"), None);
    }

    #[test]
    fn rewrites_import_source() {
        let js = "import source m from './x.wasm';\nimport { a } from './a.js';\n";
        assert_eq!(
            rewrite_import_source(js),
            "import m from './x.wasm';\nimport { a } from './a.js';\n"
        );
    }
}
