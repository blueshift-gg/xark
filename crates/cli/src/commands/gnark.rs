//! `--backend gnark` — prove a xark circuit with gnark's Groth16 instead of xark's.
//!
//! xark still compiles the circuit and solves the witness; gnark does the setup,
//! the proof and the verification. The two meet in iden3's files, the formats
//! circom writes and snarkjs reads: the keyed rows as `circuit.r1cs` and
//! the solved witness as `witness.wtns` (`iden3.rs` writes both). `xark-gnark`, a small Go program whose
//! source is embedded here (`crates/cli/gnark/`), turns the rows into a gnark
//! constraint system and runs gnark on it. It is built with `go` on first use.
//!
//! ```text
//! <keys>/gnark/                 # `xark setup --backend gnark`
//!   circuit.r1cs                # the keyed rows, iden3 format
//!   circuit.ccs                 # the same rows as a gnark constraint system
//!   pk.bin  vk.bin              # gnark's keys
//!   metadata.json
//! target/xark/<name>/gnark/     # `xark prove --backend gnark`
//!   witness.wtns                # the solved witness, iden3 format: removed once
//!                               # gnark has read it, unless `--keep-witness`
//!   proof.bin                   # gnark's proof
//!   public_witness.bin          # gnark's public witness
//! ```
//!
//! The keys come from gnark's single-party setup: this machine's randomness, as
//! `xark setup` without a `.ptau`. Neither the keys nor the proofs are
//! interchangeable with xark's own, and the Solana verifier takes xark's.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, bail};

use super::iden3::{assignment, r1cs_wires, solve, write_r1cs, write_wtns};
use super::{prove::ProveArgs, setup, setup::SetupArgs, verify::VerifyArgs};
use crate::xark_project::XarkProject;

/// Which Groth16 implementation sets up, proves and verifies.
#[derive(clap::ValueEnum, Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Backend {
    /// xark's own streaming prover (arkworks-compatible keys and proofs).
    #[default]
    #[value(alias = "arkworks")]
    Xark,
    /// gnark's prover, through the `xark-gnark` helper (needs `go` installed).
    /// Its keys and proofs are gnark's, kept in a `gnark/` directory beside xark's.
    Gnark,
}

/// The helper's source: the whole Go module, written out and built on first use.
const TOOL_SOURCES: [(&str, &str); 3] = [
    ("main.go", include_str!("../../gnark/main.go")),
    ("go.mod", include_str!("../../gnark/go.mod")),
    ("go.sum", include_str!("../../gnark/go.sum")),
];

/// The helper's command line and report, as this file speaks them: `protocol` in
/// `crates/cli/gnark/main.go`. A helper named by `XARK_GNARK` may be an older
/// build; one that reports another number is refused.
const PROTOCOL: &str = "2";

/// The helper's exit code when gnark itself said no: the witness doesn't satisfy
/// the rows, or the proof doesn't verify (`exitRejected` in `main.go`). Any other
/// failure is the helper's, not a verdict.
const EXIT_REJECTED: i32 = 2;

/// Where the built helper is kept: the user's cache directory.
fn cache_dir() -> Result<PathBuf> {
    // No fallback to the temporary directory: where that is shared, the helper's
    // path there is one anybody can guess and put a program at, which this would
    // then run.
    std::env::var_os("XDG_CACHE_HOME")
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME")
                .filter(|v| !v.is_empty())
                .map(|h| PathBuf::from(h).join(".cache"))
        })
        .map(|c| c.join("xark"))
        .context(
            "the gnark helper is built into $XDG_CACHE_HOME or $HOME/.cache, and neither              is set: set one, or point XARK_GNARK at a built `xark-gnark`",
        )
}

/// The `xark-gnark` helper: `XARK_GNARK` if set (a prebuilt binary), otherwise
/// built from the embedded source into the user's cache, once per version of that
/// source.
fn tool() -> Result<PathBuf> {
    if let Some(path) = std::env::var_os("XARK_GNARK") {
        return Ok(path.into());
    }
    use sha2::Digest;
    let mut h = sha2::Sha256::new();
    for (name, text) in TOOL_SOURCES {
        h.update(name.as_bytes());
        h.update(text.as_bytes());
    }
    let tag = hex::encode(&h.finalize()[..8]);
    let cache = cache_dir()?;
    let dir = cache.join(format!("gnark-{tag}"));
    let name = format!("xark-gnark{}", std::env::consts::EXE_SUFFIX);
    let bin = dir.join(&name);
    if bin.is_file() {
        return Ok(bin);
    }
    eprintln!(
        "{} building the gnark helper in {} (once; needs `go`, and the network for \
         gnark's modules)…",
        crate::style::tag(),
        dir.display()
    );
    // Built in a directory of this process's own and renamed into place whole: two
    // first runs at once (a test binary's, say) don't write each other's sources
    // mid-build, and an interrupted build is never taken for the helper.
    let work = cache.join(format!("gnark-{tag}.{}.tmp", std::process::id()));
    let built = (|| {
        fs::create_dir_all(&work).with_context(|| format!("creating {}", work.display()))?;
        for (name, text) in TOOL_SOURCES {
            fs::write(work.join(name), text)?;
        }
        let status = Command::new("go")
            .args(["build", "-o", &name, "."])
            .current_dir(&work)
            .status()
            .context(
                "running `go build` for the gnark backend: install Go (https://go.dev/dl), \
                 or point XARK_GNARK at a built `xark-gnark`",
            )?;
        if !status.success() {
            bail!("`go build` of the gnark helper failed");
        }
        // Another process may have put the same build there first; a directory
        // without the helper is an older xark's interrupted build.
        if !bin.is_file() {
            let _ = fs::remove_dir_all(&dir);
            if let Err(e) = fs::rename(&work, &dir)
                && !bin.is_file()
            {
                return Err(e).with_context(|| format!("moving the helper to {}", dir.display()));
            }
        }
        Ok(())
    })();
    let _ = fs::remove_dir_all(&work);
    built?;
    Ok(bin)
}

/// What the helper reported: its `name=value` output lines.
type Report = BTreeMap<String, String>;

/// Run the helper. `Ok(None)` is gnark's own refusal ([`EXIT_REJECTED`]): a
/// witness that doesn't satisfy the rows, a proof that doesn't verify.
fn run_tool(args: &[&std::ffi::OsStr]) -> Result<Option<Report>> {
    let tool = tool()?;
    let out = Command::new(&tool)
        .args(args)
        .stderr(std::process::Stdio::inherit())
        .output()
        .with_context(|| format!("running the gnark helper {}", tool.display()))?;
    let report: Report = String::from_utf8_lossy(&out.stdout)
        .lines()
        .filter_map(|l| l.split_once('='))
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect();
    let rejected = out.status.code() == Some(EXIT_REJECTED);
    if (out.status.success() || rejected)
        && report.get("protocol").map(String::as_str) != Some(PROTOCOL)
    {
        bail!(
            "{} is not this xark's gnark helper (XARK_GNARK names an older build?): \
             build it again from crates/cli/gnark/",
            tool.display()
        );
    }
    if rejected {
        return Ok(None);
    }
    if !out.status.success() {
        bail!("the gnark helper failed (see above)");
    }
    Ok(Some(report))
}

fn key_dir(project: &XarkProject, out: &Option<PathBuf>) -> PathBuf {
    out.clone()
        .unwrap_or_else(|| project.key_dir())
        .join("gnark")
}

fn ms(report: &Report, key: &str) -> String {
    report
        .get(key)
        .and_then(|v| v.parse::<f64>().ok())
        .map_or_else(|| "?".into(), |v| format!("{:.2}s", v / 1000.0))
}

/// Removes the witness file when the proof is done with it, however it ends.
struct Unlink<'a>(Option<&'a Path>);

impl Drop for Unlink<'_> {
    fn drop(&mut self) {
        if let Some(path) = self.0 {
            let _ = fs::remove_file(path);
        }
    }
}

/// `xark setup --backend gnark`: export the keyed rows and run gnark's setup.
pub fn setup(args: &SetupArgs) -> Result<()> {
    if args.ptau_file.is_some()
        || args.deterministic_rng.is_some()
        || args.phase2_seed.is_some()
        || args.uncompressed
        || args.domain == setup::QapDomain::Smooth
    {
        bail!(
            "--backend gnark runs gnark's own single-party setup: --ptau-file, \
             --deterministic-rng, --phase2-seed, --uncompressed and --domain smooth \
             are xark's"
        );
    }
    let project = XarkProject::resolve(args.path.clone())?;
    crate::cli::build_if_needed(&project.xark_dir, true)?;
    let dir = key_dir(&project, &args.out);
    fs::create_dir_all(&dir).with_context(|| format!("creating {}", dir.display()))?;

    // The same choice of rows as a xark key over a 2^k domain, which is gnark's.
    let (keyed, form, why, hash, _, public, _) =
        setup::plan_keyed(args, &project, args.r1cs_form, true)?;
    println!("R1CS form: {form} ({why})");
    let r1cs = dir.join("circuit.r1cs");
    let (rows, wires) = keyed.with_source(|src| {
        write_r1cs(&r1cs, src)?;
        anyhow::Ok((src.num_constraints(), src.layout().num_vars()))
    })?;
    drop(keyed);
    println!("Wrote {}", r1cs.display());

    let report = run_tool(&["setup".as_ref(), r1cs.as_os_str(), dir.as_os_str()])?
        .context("gnark refused the circuit's rows (see above)")?;
    let digest = fs::read(project.circuit_xbc())
        .ok()
        .map(|b| super::r1cs_digest(&b));
    let metadata = serde_json::json!({
        "backend": "gnark",
        "circuit_hash": hash,
        "digest": digest,
        "r1cs_form": form,
        "num_constraints": rows,
        "num_variables": wires,
        "num_public_inputs": public,
        // gnark's `groth16.Setup`: one party's randomness.
        "production_safe": false,
    });
    fs::write(
        dir.join("metadata.json"),
        serde_json::to_string_pretty(&metadata)? + "\n",
    )?;
    for name in ["circuit.ccs", "pk.bin", "vk.bin"] {
        println!("Wrote {}", dir.join(name).display());
    }
    println!(
        "gnark setup: {rows} constraints, {wires} variables, {public} public inputs ({})",
        ms(&report, "setup_ms")
    );
    let p = super::path_arg(&args.path);
    // A key put elsewhere is named to `prove`, as xark's own is.
    let key = match &args.out {
        Some(_) => format!(" --proving-key {}", dir.join("pk.bin").display()),
        None => String::new(),
    };
    println!(
        "\n{}",
        crate::style::next_steps(&[(
            format!("xark prove {p} --backend gnark{key} --inputs '{{…}}'"),
            "prove with gnark",
        )])
    );
    Ok(())
}

/// `xark prove --backend gnark`: solve the witness with xark, prove with gnark.
pub fn prove(args: &ProveArgs) -> Result<()> {
    if args.deterministic_rng.is_some() || args.low_memory || args.cache {
        bail!(
            "--backend gnark proves from OS randomness, in memory, and reads its key \
             whole each time: --deterministic-rng, --low-memory and --cache are xark's"
        );
    }
    let project = XarkProject::resolve(args.path.clone())?;
    crate::cli::build_if_needed(&project.xark_dir, true)?;
    // `--proving-key` names the `pk.bin` of a key made elsewhere (`xark setup
    // --backend gnark --out`); the rest of the key is beside it.
    let keys = match &args.proving_key {
        Some(pk) => {
            if !pk.is_file() {
                bail!(
                    "there is no {} (--proving-key names a gnark key's `pk.bin`)",
                    pk.display()
                );
            }
            match pk.parent() {
                Some(dir) if !dir.as_os_str().is_empty() => dir.to_path_buf(),
                _ => PathBuf::from("."),
            }
        }
        None => {
            let keys = key_dir(&project, &None);
            if !keys.join("pk.bin").exists() {
                eprintln!(
                    "{} no gnark key found — making one with gnark's setup…",
                    crate::style::tag()
                );
                setup(&SetupArgs {
                    backend: Backend::Gnark,
                    ..SetupArgs::defaults(args.path.clone())
                })?;
            }
            keys
        }
    };
    let xbc = project.circuit_xbc();
    let bytes = fs::read(&xbc).with_context(|| format!("reading {}", xbc.display()))?;
    ensure_key_fits(&keys, &bytes)?;

    let t = std::time::Instant::now();
    let super::iden3::Solved {
        inputs: id_inputs,
        assign,
    } = solve(&project, &bytes, args.inputs.as_deref())?;
    // The rows the key was made for, told by their variable count as for a xark
    // key: the layout of the witness follows them.
    let wires = r1cs_wires(&keys.join("circuit.r1cs"))?;
    let src = xark_prover::rows_for_key(&bytes, wires, None).map_err(|e| anyhow::anyhow!(e))?;
    let z = assignment(src.as_ref(), &assign);
    drop(assign);
    if z.len() != wires {
        bail!(
            "the gnark key in {} was made for another form of this circuit: run `xark \
             setup --backend gnark` again",
            keys.display()
        );
    }
    drop(src);
    let solve_time = t.elapsed();

    let out = args
        .out
        .clone()
        .unwrap_or_else(|| project.xark_dir.clone())
        .join("gnark");
    fs::create_dir_all(&out).with_context(|| format!("creating {}", out.display()))?;
    let wtns = out.join("witness.wtns");
    // The witness holds the private inputs: like the default prover's spill file
    // (`--low-memory`), it doesn't outlive the proof unless asked to.
    let _unlink = Unlink((!args.keep_witness).then_some(&wtns));
    write_wtns(&wtns, &z)?;
    drop(z);
    let Some(report) = run_tool(&[
        "prove".as_ref(),
        keys.as_os_str(),
        wtns.as_os_str(),
        out.as_os_str(),
    ])?
    else {
        // gnark names the row it found unsatisfied; say which constraint of the
        // source that is, as `xark prove` does.
        super::explain_unsatisfied(
            &bytes,
            super::load_sources(&project.xark_dir).as_ref(),
            &id_inputs,
        )?;
        bail!("gnark made no proof: the witness doesn't satisfy the key's rows (see above)");
    };
    println!("Wrote {}", out.join("proof.bin").display());
    println!("Wrote {}", out.join("public_witness.bin").display());
    if args.keep_witness {
        println!(
            "Kept {} (it holds the private inputs: keep it as you keep them)",
            wtns.display()
        );
    }
    println!(
        "gnark proof: solve {:.2}s, prove {} (verified in {})",
        solve_time.as_secs_f64(),
        ms(&report, "prove_ms"),
        ms(&report, "verify_ms")
    );
    // The benchmark reads these; `PROVE_TIME=1` prints xark's own the same way.
    if super::dbg_flag("PROVE_TIME") {
        eprintln!(
            "PROVE_TIME: solve = {:.3}s, gnark prove = {}ms",
            solve_time.as_secs_f64(),
            report.get("prove_ms").map_or("?", String::as_str)
        );
    }
    let p = super::path_arg(&args.path);
    // A key and a proof put elsewhere are named to `verify`, as xark's own are.
    let mut named = String::new();
    if args.proving_key.is_some() {
        named += &format!(" --verifying-key {}", keys.join("vk.bin").display());
    }
    if args.out.is_some() {
        named += &format!(
            " --proof {} --public-inputs {}",
            out.join("proof.bin").display(),
            out.join("public_witness.bin").display()
        );
    }
    println!(
        "\n{}",
        crate::style::next_steps(&[(
            format!("xark verify {p} --backend gnark{named}"),
            "verify the proof with gnark",
        )])
    );
    Ok(())
}

/// A gnark key fits the build it was made from: the `circuit.xbc` its metadata
/// names, or another build of the same constraints.
fn ensure_key_fits(keys: &Path, xbc: &[u8]) -> Result<()> {
    let meta: serde_json::Value = fs::read_to_string(keys.join("metadata.json"))
        .ok()
        .and_then(|s| serde_json::from_str(&s).ok())
        .unwrap_or_default();
    let same = meta["circuit_hash"].as_str() == Some(super::sha256_hex(xbc).as_str())
        || meta["digest"].as_str() == Some(super::r1cs_digest(xbc).as_str());
    if !same {
        bail!(
            "the gnark key in {} was made for a different circuit (it changed since the \
             setup?): run `xark setup --backend gnark` again",
            keys.display()
        );
    }
    Ok(())
}

/// `xark verify --backend gnark`: gnark's verifier over gnark's files.
pub fn verify(args: &VerifyArgs) -> Result<()> {
    if args.inputs.is_some() {
        bail!(
            "--backend gnark verifies against the `public_witness.bin` that `xark prove \
             --backend gnark` wrote (--public-inputs names another): --inputs is xark's"
        );
    }
    let project = XarkProject::resolve(args.path.clone())?;
    let out = project.xark_dir.join("gnark");
    let vk = args
        .verifying_key
        .clone()
        .unwrap_or_else(|| key_dir(&project, &None).join("vk.bin"));
    let proof = args.proof.clone().unwrap_or_else(|| out.join("proof.bin"));
    let public = args
        .public_inputs
        .clone()
        .unwrap_or_else(|| out.join("public_witness.bin"));
    for (path, what) in [(&vk, "setup"), (&proof, "prove"), (&public, "prove")] {
        if !path.exists() {
            bail!(
                "there is no {} (run `xark {what} --backend gnark` first?)",
                path.display()
            );
        }
    }
    // Only gnark's own verdict is a failed verification (exit code 2, as the
    // default backend's); a helper that couldn't run or read a file is an error.
    match run_tool(&[
        "verify".as_ref(),
        vk.as_os_str(),
        proof.as_os_str(),
        public.as_os_str(),
    ])? {
        Some(_) => {
            println!("{}", crate::style::brand("✅ Proof verified (gnark)"));
            Ok(())
        }
        None => {
            println!("{}", crate::style::err("❌ Proof verification failed"));
            std::process::exit(2);
        }
    }
}
