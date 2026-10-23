//! xark's stable-Rust frontend.
//!
//! A circuit crate is compiled by stock **stable** `rustc` to `wasm32-unknown-unknown`
//! with `--cfg xark`. In that build every circuit operation (`Field` arithmetic,
//! comparisons, hints, `require_eq`, input binding) is a call to an opaque `xark.*`
//! wasm import, so the compiler can neither drop, duplicate nor reorder them. This
//! crate runs the module in an interpreter that implements those imports as the
//! circuit builder: concrete values (constants, loop counters, indices) just execute,
//! while witness values are tracked symbolically. A branch on a witness `bool` runs
//! both arms (guarded: an arm's requirements bind only when it is taken) and merges
//! what differs into selects.

mod builder;
mod debuginfo;
mod error;
mod host;
mod interp;
mod output;
mod templates;

pub use error::{CompileError, CompileResult, ErrorSite};
pub use output::LowerOutput;

/// A lowered circuit and the name of its `#[circuit]` fn.
pub struct Lowered {
    pub output: LowerOutput,
    pub entry: Option<String>,
    /// The input interface (`schema.json`).
    pub schema: serde_json::Value,
    /// Each constraint's source statement (`sources.json`; see [`write_sources`]).
    pub sources: xark_ir::SourceMap,
}

/// Lower a circuit module (`wasm32`, built with `--cfg xark`) to a circuit, and the
/// circuit's name. `notes`: build the
/// constraints' debug notes and internal variable names (only the JSON views show
/// them; `circuit.xbc` is identical either way).
pub fn lower_module(
    wasm: &[u8],
    field: xark_ir::FieldSpec,
    profile: bool,
    notes: bool,
) -> CompileResult<Lowered> {
    let timing = std::env::var_os("XARK_FRONTEND_TIME").is_some();
    let t = std::time::Instant::now();
    // Sites are always recorded (an interned id per constraint): every build
    // writes `sources.json`. `profile` adds the full per-constraint attribution.
    let mut host = host::Host::new(true, notes, field.modulus_decimal.as_deref());
    let module = interp::Module::parse(wasm)?;
    let mut machine = interp::Machine::new(&module)?;
    machine
        .run_export(&module, "__xark_main", &mut host)
        .map_err(|e| locate(&module, e))?;
    if timing {
        eprintln!(
            "FRONTEND_TIME: run    = {:?} ({} wasm instructions)",
            t.elapsed(),
            machine.steps()
        );
        eprintln!(
            "FRONTEND_TIME: host calls = {:.3}s, mem {} MB",
            machine.host_ns as f64 / 1e9,
            machine.mem.len() >> 20
        );
        eprintln!("FRONTEND_TIME: forks {}", machine.forks);
    }
    let schema = host.schema(module.entry.as_deref().unwrap_or("circuit"))?;
    let sites = std::mem::take(&mut host.sites);
    let t = std::time::Instant::now();
    let mut output = host.finish(field).map_err(|e| locate(&module, e))?;
    let mut r = debuginfo::Resolver::new(&module);
    let resolved: Vec<debuginfo::Attribution> = sites.iter().map(|s| r.attribute(s)).collect();
    let sources = source_map(&output.profile, &resolved);
    if profile {
        attribute(&resolved, &mut output.profile);
    } else {
        output.profile = Vec::new();
    }
    if timing {
        eprintln!("FRONTEND_TIME: finish = {:?}", t.elapsed());
    }
    Ok(Lowered {
        output,
        entry: module.entry.clone(),
        schema,
        sources,
    })
}

/// Map an error's wasm call stack to the user source line it happened at.
fn locate(module: &interp::Module, mut e: CompileError) -> CompileError {
    let Some(site) = e.site.as_ref().map(|s| s.stack.clone()) else {
        return e;
    };
    let site = &site[..];
    let mut r = debuginfo::Resolver::new(module);
    let (at, inner) = r.error_location(site);
    if let Some((file, line, col)) = at {
        if e.location.is_none() {
            e.location = Some(format!("{file}:{line}:{col}"));
            if let Some(inner) = inner {
                e.notes.push(inner);
            }
        }
        if let Some(s) = e.site.as_mut() {
            s.span = Some((file, line, col));
        }
    }
    if !r.has_lines() {
        // No line tables: name the wasm functions instead.
        let chain: Vec<String> = r
            .stack(site)
            .iter()
            .map(|f| debuginfo::short_name(&f.function).to_string())
            .filter(|n| !n.starts_with("__xark") && !n.starts_with("xark_"))
            .collect();
        if !chain.is_empty() && e.location.is_none() {
            e.notes.push(format!("in {}", chain.join(" → ")));
        }
    }
    e
}

/// The source map of constraints whose sites (interned ids, carried in each
/// profile record's `line`) resolve to `resolved`.
fn source_map(
    profile: &[xark_ir::profile::ConstraintProfile],
    resolved: &[debuginfo::Attribution],
) -> xark_ir::SourceMap {
    // Distinct statements: many interned call stacks resolve to the same one.
    let mut sites: Vec<xark_ir::Site> = Vec::new();
    let mut index: std::collections::HashMap<xark_ir::Site, u32> = Default::default();
    let ids: Vec<u32> = resolved
        .iter()
        .map(|a| {
            let site = xark_ir::Site {
                file: a.file.clone(),
                line: a.line,
                col: a.col,
                text: String::new(),
                chain: a.chain.clone(),
            };
            *index.entry(site.clone()).or_insert_with(|| {
                sites.push(site);
                sites.len() as u32 - 1
            })
        })
        .collect();
    let rows = profile.iter().map(|p| {
        ids.get(p.line as usize)
            .copied()
            .unwrap_or(xark_ir::sources::NO_SITE)
    });
    xark_ir::SourceMap::new(rows, &sites)
}

/// Resolve each profiled constraint's site (its interned id, carried in `line`)
/// to the source attribution.
fn attribute(
    resolved: &[debuginfo::Attribution],
    profile: &mut [xark_ir::profile::ConstraintProfile],
) {
    use xark_ir::profile::ConstraintKind;
    for p in profile.iter_mut() {
        let Some(a) = resolved.get(p.line as usize) else {
            p.line = 0;
            continue;
        };
        p.file = a.file.clone();
        p.line = a.line;
        p.col = a.col;
        p.chain = a.chain.clone();
        if let Some(k) = a.kind_hint
            && matches!(p.kind, ConstraintKind::Mul | ConstraintKind::Other)
        {
            p.kind = k;
        }
    }
}

/// Write a lowered circuit's artifacts to `out_dir`:
/// `circuit.xbc` always; `circuit.json` / `r1cs.json` / `graph.dot` with
/// `emit_json`; `profile.json` with `profile`.
pub fn write_outputs(
    out_dir: &std::path::Path,
    out: &LowerOutput,
    emit_json: bool,
    profile: bool,
) -> std::io::Result<()> {
    let cwd = std::env::current_dir().unwrap_or_default();
    write_outputs_in(out_dir, out, emit_json, profile, &cwd)
}

/// [`write_outputs`], with `profile.json`'s relative source paths resolving
/// against `source_root` (the circuit crate's directory; see [`relativize_profile`]).
pub fn write_outputs_in(
    out_dir: &std::path::Path,
    out: &LowerOutput,
    emit_json: bool,
    profile: bool,
    source_root: &std::path::Path,
) -> std::io::Result<()> {
    use std::io::Write;
    std::fs::create_dir_all(out_dir)?;
    if emit_json {
        let mut w = std::io::BufWriter::new(std::fs::File::create(out_dir.join("circuit.json"))?);
        xark_ir::primitive::write_json(&out.primitive, &mut w)?;
        w.write_all(b"\n")?;
        drop(w);
        const DEBUG_R1CS_MAX_CONSTRAINTS: usize = 1_000_000;
        let mut w = std::io::BufWriter::new(std::fs::File::create(out_dir.join("r1cs.json"))?);
        if out.r1cs.constraints.len() <= DEBUG_R1CS_MAX_CONSTRAINTS {
            xark_ir::json::write_json_pretty(&out.r1cs, &mut w)?;
            w.write_all(b"\n")?;
            std::fs::write(out_dir.join("graph.dot"), xark_ir::to_dot(&out.r1cs))?;
        } else {
            xark_ir::json::write_json(&out.r1cs, &mut w)?;
            w.write_all(b"\n")?;
        }
    }
    if profile {
        let prof = xark_ir::ProfileProgram {
            source_root: source_root.display().to_string(),
            field: Some(out.r1cs.field.clone()),
            constraints: out.profile.clone(),
        };
        std::fs::write(
            out_dir.join("profile.json"),
            format!("{}\n", xark_ir::profile::to_json_pretty(&prof)),
        )?;
    }
    std::fs::write(out_dir.join("circuit.xbc"), &out.xbc)
}

/// Write `sources.json` to `out_dir`: `sources` with paths made relative to the
/// circuit crate `root` and each statement's source line filled in.
pub fn write_sources(
    out_dir: &std::path::Path,
    sources: &mut xark_ir::SourceMap,
    root: &std::path::Path,
) -> std::io::Result<()> {
    let canon_root = root.canonicalize().unwrap_or_else(|_| root.to_path_buf());
    for s in &mut sources.sites {
        let path = root.join(&s.file); // a no-op for an absolute path
        let path = path.canonicalize().unwrap_or(path);
        s.file = match path.strip_prefix(&canon_root) {
            Ok(rel) => rel.display().to_string(),
            // Outside the crate (a dependency): from its crate dir on, so the file
            // doesn't carry this machine's paths (`xark-poseidon2/src/lib.rs`).
            Err(_) => {
                let parts: Vec<_> = path.iter().collect();
                match parts.iter().rposition(|p| *p == "src") {
                    Some(i) if i > 0 => parts[i - 1..]
                        .iter()
                        .collect::<std::path::PathBuf>()
                        .display()
                        .to_string(),
                    _ => path
                        .file_name()
                        .map_or(String::new(), |f| f.to_string_lossy().into()),
                }
            }
        };
    }
    sources.read_text(root);
    std::fs::write(out_dir.join("sources.json"), sources.to_json() + "\n")
}

/// Make the profile's source paths under `root` relative to it (`src/lib.rs`);
/// others (dependencies) stay absolute.
pub fn relativize_profile(out: &mut LowerOutput, root: &std::path::Path) {
    let root = root.canonicalize().unwrap_or_else(|_| root.to_path_buf());
    let mut cache: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    for p in &mut out.profile {
        if p.file.is_empty() {
            continue;
        }
        let rel = cache.entry(p.file.clone()).or_insert_with(|| {
            let path = std::path::Path::new(&p.file);
            let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
            path.strip_prefix(&root)
                .map(|r| r.display().to_string())
                .unwrap_or_else(|_| p.file.clone())
        });
        p.file = rel.clone();
    }
}

/// Build a circuit crate for the stable frontend: `cargo rustc --lib` for
/// `wasm32-unknown-unknown` with `--cfg xark`, as a `cdylib` (so the `#[circuit]`
/// export and everything it reaches are linked), with `panic = "abort"`. Returns the
/// module's bytes. `cargo` is whatever toolchain is ambient (stable is enough).
pub fn build_crate(
    crate_dir: &std::path::Path,
    target_dir: &std::path::Path,
) -> Result<Vec<u8>, String> {
    build_crate_with(crate_dir, target_dir, &BuildOptions::default())
}

/// Options for [`build_crate_with`].
#[derive(Clone, Debug)]
pub struct BuildOptions {
    /// Build with DWARF line tables (`debug = "line-tables-only"`; the default), so
    /// lowering can attribute constraints and errors to source lines. The circuit
    /// and the lowering time are identical either way, and the compile time is the
    /// same within noise (Ed25519: 2.8 s cold with, 3.2 s without); only the
    /// `.wasm` grows (49 KB → 0.9 MB). A cache built without them is rebuilt.
    pub line_tables: bool,
    /// Pass `--message-format=json` to cargo (its diagnostics go to stdout as
    /// JSON, for editors).
    pub json_diagnostics: bool,
    /// With `json_diagnostics`: diagnostics already reported (their `rendered`
    /// text), left out of the output — e.g. those a host `cargo check` of the
    /// same crate just printed.
    pub skip_rendered: std::collections::HashSet<String>,
}

impl Default for BuildOptions {
    fn default() -> Self {
        BuildOptions {
            line_tables: true,
            json_diagnostics: false,
            skip_rendered: Default::default(),
        }
    }
}

/// Build `crate_dir`'s host code as a plain wasm module for generated clients (the
/// "client build": `--cfg xark_client`, so `#[input]` methods become exports;
/// see `xark::client`), into `target_dir`. Its wasm bytes.
pub fn build_client(
    crate_dir: &std::path::Path,
    target_dir: &std::path::Path,
) -> Result<Vec<u8>, String> {
    let name = package_name(crate_dir)?;
    ensure_wasm_target(crate_dir)?;
    let _lock = lock_build(target_dir)?;
    let status = std::process::Command::new(std::env::var("CARGO").unwrap_or("cargo".into()))
        .current_dir(crate_dir)
        .env("RUSTFLAGS", "--cfg xark_client")
        .env("CARGO_TARGET_DIR", target_dir)
        .args([
            "rustc",
            "--quiet",
            "--release",
            "--lib",
            "--target",
            "wasm32-unknown-unknown",
            "--crate-type",
            "cdylib",
            "--config",
            "profile.release.panic=\"abort\"",
            // Small: a client downloads it (zkyc's: 250 KB, 100 KB gzipped). A call
            // is a few microseconds at any level.
            "--config",
            "profile.release.opt-level=\"z\"",
            "--config",
            "profile.release.lto=true",
            "--config",
            "profile.release.codegen-units=1",
            "--config",
            "profile.release.strip=true",
        ])
        .status()
        .map_err(|e| format!("running cargo: {e}"))?;
    if !status.success() {
        return Err("cargo build of the client module failed".into());
    }
    let wasm = target_dir
        .join("wasm32-unknown-unknown/release")
        .join(format!("{}.wasm", name.replace('-', "_")));
    std::fs::read(&wasm).map_err(|e| format!("reading {}: {e}", wasm.display()))
}

/// The contents of `wasm`'s custom sections named `name`, back to back.
pub fn custom_section(wasm: &[u8], name: &str) -> Vec<u8> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(wasm).flatten() {
        if let wasmparser::Payload::CustomSection(c) = payload
            && c.name() == name
        {
            out.extend_from_slice(c.data());
        }
    }
    out
}

/// The `[package]` name in `crate_dir/Cargo.toml`.
fn package_name(crate_dir: &std::path::Path) -> Result<String, String> {
    let manifest = std::fs::read_to_string(crate_dir.join("Cargo.toml"))
        .map_err(|e| format!("reading {}/Cargo.toml: {e}", crate_dir.display()))?;
    manifest
        .lines()
        .skip_while(|l| l.trim() != "[package]")
        .find_map(|l| {
            let l = l.trim();
            let v = l.strip_prefix("name")?.trim_start().strip_prefix('=')?;
            Some(v.trim().trim_matches('"').to_string())
        })
        .ok_or_else(|| "no package name in Cargo.toml".into())
}

/// Every local source file the last [`build_crate_with`] into `target_dir` read: the
/// circuit crate's, its path dependencies' (gadgets, `xark` itself), from cargo's
/// dep-info. (Registry crates don't change in place, so cargo leaves them out.)
pub fn circuit_sources(
    crate_dir: &std::path::Path,
    target_dir: &std::path::Path,
) -> Result<Vec<std::path::PathBuf>, String> {
    let name = package_name(crate_dir)?.replace('-', "_");
    let d = target_dir
        .join("wasm32-unknown-unknown/release")
        .join(format!("{name}.d"));
    let text = std::fs::read_to_string(&d).map_err(|e| format!("reading {}: {e}", d.display()))?;
    Ok(parse_dep_info(&text))
}

/// The prerequisites of a make-style dep-info file (`out: a b\ c`), unescaped.
fn parse_dep_info(text: &str) -> Vec<std::path::PathBuf> {
    let line = text.lines().next().unwrap_or_default();
    let deps = line.split_once(": ").map_or("", |(_, d)| d);
    let (mut out, mut cur, mut chars) = (Vec::new(), String::new(), deps.chars());
    while let Some(c) = chars.next() {
        match c {
            '\\' => cur.extend(chars.next()),
            ' ' => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur).into());
                }
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() {
        out.push(cur.into());
    }
    out
}

/// [`build_crate`] with [`BuildOptions`].
pub fn build_crate_with(
    crate_dir: &std::path::Path,
    target_dir: &std::path::Path,
    opts: &BuildOptions,
) -> Result<Vec<u8>, String> {
    let name = package_name(crate_dir)?;
    ensure_wasm_target(crate_dir)?;
    let _lock = lock_build(target_dir)?;
    let mut cmd = std::process::Command::new(std::env::var("CARGO").unwrap_or("cargo".into()));
    cmd.current_dir(crate_dir)
        .env("RUSTFLAGS", "--cfg xark")
        .env("CARGO_TARGET_DIR", target_dir)
        .args([
            "rustc",
            "--quiet",
            "--release",
            "--lib",
            "--target",
            "wasm32-unknown-unknown",
            "--crate-type",
            "cdylib",
            "--config",
            "profile.release.panic=\"abort\"",
            // Checked integer arithmetic, as Rust's debug semantics: an overflow on a
            // witness integer becomes a constraint.
            "--config",
            "profile.release.overflow-checks=true",
            // Size-optimized: LLVM inlines less, so more gadget calls stay wasm calls
            // and template (Ed25519's `circuit.xbc`: 2.5 MB at `3` → 0.78 MB). The
            // circuit itself is the same at every level.
            "--config",
            "profile.release.opt-level=\"s\"",
        ]);
    if opts.line_tables {
        cmd.args([
            "--config",
            "profile.release.debug=\"line-tables-only\"",
            "--config",
            "profile.release.strip=\"none\"",
        ]);
    }
    if opts.json_diagnostics {
        cmd.arg("--message-format=json-diagnostic-rendered-ansi");
    }
    let status = if opts.json_diagnostics && !opts.skip_rendered.is_empty() {
        // Relay cargo's JSON lines, minus the diagnostics already reported.
        use std::io::BufRead;
        let mut child = cmd
            .stdout(std::process::Stdio::piped())
            .spawn()
            .map_err(|e| format!("running cargo: {e}"))?;
        let stdout = child.stdout.take().expect("piped stdout");
        for line in std::io::BufReader::new(stdout)
            .lines()
            .map_while(Result::ok)
        {
            let seen = serde_json::from_str::<serde_json::Value>(&line)
                .ok()
                .and_then(|v| v["message"]["rendered"].as_str().map(str::to_string))
                .is_some_and(|r| opts.skip_rendered.contains(&r));
            if !seen {
                println!("{line}");
            }
        }
        child.wait().map_err(|e| format!("running cargo: {e}"))?
    } else {
        cmd.status().map_err(|e| format!("running cargo: {e}"))?
    };
    if !status.success() {
        return Err("cargo build of the circuit failed".into());
    }
    let wasm = target_dir
        .join("wasm32-unknown-unknown/release")
        .join(format!("{}.wasm", name.replace('-', "_")));
    std::fs::read(&wasm).map_err(|e| format!("reading {}: {e}", wasm.display()))
}

/// Hold `target_dir` for one build, from cargo's start until its `.wasm` is read.
/// Cargo locks only its own run: another build of the crate (an editor's `xark
/// check` beside a terminal's `xark build`) could otherwise replace the `.wasm`
/// while this one reads it ("No such file or directory"). Released when dropped.
fn lock_build(target_dir: &std::path::Path) -> Result<std::fs::File, String> {
    std::fs::create_dir_all(target_dir)
        .map_err(|e| format!("creating {}: {e}", target_dir.display()))?;
    let path = target_dir.join(".xark-build-lock");
    let file = std::fs::File::create(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    file.lock()
        .map_err(|e| format!("locking {}: {e}", path.display()))?;
    Ok(file)
}

/// Make sure the ambient toolchain has the `wasm32-unknown-unknown` standard library,
/// adding it with `rustup` when it's missing (the one toolchain piece the stable
/// frontend needs).
fn ensure_wasm_target(crate_dir: &std::path::Path) -> Result<(), String> {
    let sysroot = std::process::Command::new("rustc")
        .current_dir(crate_dir)
        .args(["--print", "sysroot"])
        .output()
        .map_err(|e| format!("running rustc: {e}"))?;
    let sysroot = String::from_utf8_lossy(&sysroot.stdout).trim().to_string();
    if std::path::Path::new(&sysroot)
        .join("lib/rustlib/wasm32-unknown-unknown")
        .exists()
    {
        return Ok(());
    }
    eprintln!("xark: installing the wasm32-unknown-unknown target (one-time)");
    let ok = std::process::Command::new("rustup")
        .current_dir(crate_dir)
        .args(["target", "add", "wasm32-unknown-unknown"])
        .status()
        .map(|s| s.success())
        .unwrap_or(false);
    if ok {
        Ok(())
    } else {
        Err(
            "the wasm32-unknown-unknown target is missing; install it with \
             `rustup target add wasm32-unknown-unknown`"
                .into(),
        )
    }
}

#[cfg(test)]
mod dep_info_tests {
    #[test]
    fn parses_escaped_paths() {
        let deps =
            super::parse_dep_info("/t/c.wasm: /a/src/lib.rs /my\\ dir/g.rs\n\n/a/src/lib.rs:\n");
        assert_eq!(
            deps,
            ["/a/src/lib.rs", "/my dir/g.rs"].map(std::path::PathBuf::from)
        );
    }
}
