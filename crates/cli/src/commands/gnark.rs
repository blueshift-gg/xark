//! `--backend gnark` — prove a xark circuit with gnark's Groth16 instead of xark's.
//!
//! xark still compiles the circuit and solves the witness; gnark does the setup,
//! the proof and the verification. The two meet in iden3's files, the formats
//! circom writes and snarkjs reads: the keyed rows as `circuit.r1cs`
//! (<https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md>) and
//! the solved witness as `witness.wtns`. `xark-gnark`, a small Go program whose
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
//!   witness.wtns                # the solved witness, iden3 format
//!   proof.bin                   # gnark's proof
//!   public_witness.bin          # gnark's public witness
//! ```
//!
//! The keys come from gnark's single-party setup: this machine's randomness, as
//! `xark setup` without a `.ptau`. Neither the keys nor the proofs are
//! interchangeable with xark's own, and the Solana verifier takes xark's.

use std::collections::BTreeMap;
use std::fs;
use std::io::{BufWriter, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, bail};
use ark_bn254::Fr;
use ark_serialize::CanonicalSerialize;
use xark_groth16::ConstraintSource;
use xark_groth16::r1cs::RowChunk;
use xark_prover::fr_from_decimal;

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

/// The BN254 scalar field's modulus, little-endian: the prime both iden3 headers
/// carry.
fn modulus_le() -> Vec<u8> {
    use num_bigint::BigUint;
    let p: BigUint = xark_ir::FieldSpec::bn254()
        .modulus_decimal
        .expect("bn254 has a modulus")
        .parse()
        .expect("a decimal modulus");
    let mut le = p.to_bytes_le();
    le.resize(32, 0);
    le
}

fn fr_le(v: &Fr, out: &mut impl Write) -> Result<()> {
    // arkworks' canonical encoding of a field element is its 32 little-endian
    // bytes, which is iden3's too.
    v.serialize_uncompressed(out)
        .map_err(|e| anyhow::anyhow!("encoding a field element: {e}"))
}

/// Write `src`'s rows as an iden3 `.r1cs` file. Wire `i` is assignment position
/// `i`: the constant one, the public inputs, then every other variable. The
/// header's private-input count is left at zero: the layout doesn't tell a private
/// input from a derived variable, and no Groth16 setup reads it.
fn write_r1cs(path: &Path, src: &dyn ConstraintSource) -> Result<()> {
    let layout = src.layout();
    let wires = u32::try_from(layout.num_vars()).context("more than 2^32 variables")?;
    let rows = u32::try_from(src.num_constraints()).context("more than 2^32 constraints")?;
    let f = fs::File::create(path).with_context(|| format!("creating {}", path.display()))?;
    let mut w = BufWriter::with_capacity(1 << 20, f);
    w.write_all(b"r1cs")?;
    w.write_all(&1u32.to_le_bytes())?; // version
    w.write_all(&3u32.to_le_bytes())?; // sections

    // Section 1: the header.
    w.write_all(&1u32.to_le_bytes())?;
    w.write_all(&(4 + 32 + 4 * 4 + 8 + 4u64).to_le_bytes())?;
    w.write_all(&32u32.to_le_bytes())?;
    w.write_all(&modulus_le())?;
    w.write_all(&wires.to_le_bytes())?;
    w.write_all(&0u32.to_le_bytes())?; // public outputs
    w.write_all(&(layout.num_instance() as u32 - 1).to_le_bytes())?; // public inputs
    w.write_all(&0u32.to_le_bytes())?; // private inputs
    w.write_all(&u64::from(wires).to_le_bytes())?; // labels
    w.write_all(&rows.to_le_bytes())?;

    // Section 2: the constraints. Its size is known only once they are written.
    w.write_all(&2u32.to_le_bytes())?;
    let size_at = w.stream_position()?;
    w.write_all(&0u64.to_le_bytes())?;
    let mut chunk = RowChunk::default();
    // A window's worth of rows in memory at a time, as the prover streams them.
    for window in src.windows(1 << 16) {
        src.expand(&window, &mut chunk);
        for row in 0..chunk.rows() {
            for m in 0..3 {
                let (cols, coeffs) = chunk.terms(row, m);
                w.write_all(&(cols.len() as u32).to_le_bytes())?;
                for (col, coeff) in cols.iter().zip(coeffs) {
                    w.write_all(&col.to_le_bytes())?;
                    fr_le(coeff, &mut w)?;
                }
            }
        }
    }
    let end = w.stream_position()?;
    w.seek(SeekFrom::Start(size_at))?;
    w.write_all(&(end - size_at - 8).to_le_bytes())?;
    w.seek(SeekFrom::Start(end))?;

    // Section 3: wire → label, the identity.
    w.write_all(&3u32.to_le_bytes())?;
    w.write_all(&(8 * u64::from(wires)).to_le_bytes())?;
    for i in 0..u64::from(wires) {
        w.write_all(&i.to_le_bytes())?;
    }
    w.flush()?;
    Ok(())
}

/// Write the assignment `z` (the constant one first) as an iden3 `.wtns` file.
fn write_wtns(path: &Path, z: &[Fr]) -> Result<()> {
    let f = fs::File::create(path).with_context(|| format!("creating {}", path.display()))?;
    // The witness: readable by its owner only, where the system has such a thing.
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        f.set_permissions(fs::Permissions::from_mode(0o600))?;
    }
    let mut w = BufWriter::with_capacity(1 << 20, f);
    w.write_all(b"wtns")?;
    w.write_all(&2u32.to_le_bytes())?; // version
    w.write_all(&2u32.to_le_bytes())?; // sections
    w.write_all(&1u32.to_le_bytes())?;
    w.write_all(&(4 + 32 + 4u64).to_le_bytes())?;
    w.write_all(&32u32.to_le_bytes())?;
    w.write_all(&modulus_le())?;
    w.write_all(&(z.len() as u32).to_le_bytes())?;
    w.write_all(&2u32.to_le_bytes())?;
    w.write_all(&(32 * z.len() as u64).to_le_bytes())?;
    for v in z {
        fr_le(v, &mut w)?;
    }
    w.flush()?;
    Ok(())
}

/// The number of wires an iden3 `.r1cs` file declares (the header is its first
/// section here, as [`write_r1cs`] writes it).
fn r1cs_wires(path: &Path) -> Result<usize> {
    use std::io::Read;
    let mut head = [0u8; 12 + 12 + 4 + 32 + 4];
    fs::File::open(path)
        .and_then(|mut f| f.read_exact(&mut head))
        .with_context(|| format!("reading {}", path.display()))?;
    if &head[..4] != b"r1cs" || head[12..16] != 1u32.to_le_bytes() {
        bail!("{} is not a circuit.r1cs xark wrote", path.display());
    }
    Ok(u32::from_le_bytes(head[60..64].try_into().expect("4 bytes")) as usize)
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
    let cache = std::env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache")))
        .unwrap_or_else(std::env::temp_dir);
    let dir = cache.join("xark").join(format!("gnark-{tag}"));
    let bin = dir.join(format!("xark-gnark{}", std::env::consts::EXE_SUFFIX));
    if bin.is_file() {
        return Ok(bin);
    }
    eprintln!(
        "{} building the gnark helper in {} (once; needs `go`, and the network for \
         gnark's modules)…",
        crate::style::tag(),
        dir.display()
    );
    fs::create_dir_all(&dir).with_context(|| format!("creating {}", dir.display()))?;
    for (name, text) in TOOL_SOURCES {
        fs::write(dir.join(name), text)?;
    }
    // Built under another name and renamed, so an interrupted build is never
    // taken for the helper.
    let tmp = dir.join(format!("xark-gnark.{}.tmp", std::process::id()));
    let status = Command::new("go")
        .args(["build", "-o"])
        .arg(&tmp)
        .arg(".")
        .current_dir(&dir)
        .status()
        .context(
            "running `go build` for the gnark backend: install Go (https://go.dev/dl), or \
             point XARK_GNARK at a built `xark-gnark`",
        )?;
    if !status.success() {
        bail!("`go build` of the gnark helper failed in {}", dir.display());
    }
    fs::rename(&tmp, &bin)?;
    Ok(bin)
}

/// Run the helper and return what it reported: its `name=value` output lines.
fn run_tool(args: &[&std::ffi::OsStr]) -> Result<BTreeMap<String, String>> {
    let out = Command::new(tool()?)
        .args(args)
        .stderr(std::process::Stdio::inherit())
        .output()
        .context("running xark-gnark")?;
    if !out.status.success() {
        bail!("gnark failed (see above)");
    }
    Ok(String::from_utf8_lossy(&out.stdout)
        .lines()
        .filter_map(|l| l.split_once('='))
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect())
}

fn key_dir(project: &XarkProject, out: &Option<PathBuf>) -> PathBuf {
    out.clone()
        .unwrap_or_else(|| project.key_dir())
        .join("gnark")
}

fn ms(report: &BTreeMap<String, String>, key: &str) -> String {
    report
        .get(key)
        .and_then(|v| v.parse::<f64>().ok())
        .map_or_else(|| "?".into(), |v| format!("{:.2}s", v / 1000.0))
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

    let report = run_tool(&["setup".as_ref(), r1cs.as_os_str(), dir.as_os_str()])?;
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
    println!(
        "\n{}",
        crate::style::next_steps(&[(
            format!("xark prove {p} --backend gnark --inputs '{{…}}'"),
            "prove with gnark",
        )])
    );
    Ok(())
}

/// `xark prove --backend gnark`: solve the witness with xark, prove with gnark.
pub fn prove(args: &ProveArgs) -> Result<()> {
    if args.proving_key.is_some() || args.deterministic_rng.is_some() || args.low_memory {
        bail!(
            "--backend gnark proves with the key in the circuit's `gnark/` directory, \
             from OS randomness and in memory: --proving-key, --deterministic-rng and \
             --low-memory are xark's"
        );
    }
    let project = XarkProject::resolve(args.path.clone())?;
    crate::cli::build_if_needed(&project.xark_dir, true)?;
    let keys = key_dir(&project, &None);
    if !keys.join("pk.bin").exists() {
        eprintln!(
            "{} no gnark key found — making one with gnark's setup…",
            crate::style::tag()
        );
        setup(&SetupArgs {
            path: args.path.clone(),
            out: None,
            without_ptau: true,
            deterministic_rng: None,
            ptau_file: None,
            phase2_seed: None,
            uncompressed: false,
            r1cs_form: setup::R1csForm::Auto,
            domain: setup::QapDomain::Auto,
            backend: Backend::Gnark,
        })?;
    }
    let xbc = project.circuit_xbc();
    let bytes = fs::read(&xbc).with_context(|| format!("reading {}", xbc.display()))?;
    ensure_key_fits(&keys, &bytes)?;

    let t = std::time::Instant::now();
    let inputs = match &args.inputs {
        Some(arg) => super::read_inputs(&project.xark_dir, arg)?,
        None => Default::default(),
    };
    let sources = super::load_sources(&project.xark_dir);
    let vars =
        xark_ir::function_decode::decode_input_vars(&bytes).map_err(|e| anyhow::anyhow!(e))?;
    let id_inputs = super::resolve_input_ids(&vars, &inputs)?;
    drop(vars);
    let assign = super::stream_witness(&bytes, sources.as_ref(), &id_inputs)?;
    // The rows the key was made for, told by their variable count as for a xark
    // key: the layout of the witness follows them.
    let wires = r1cs_wires(&keys.join("circuit.r1cs"))?;
    let src = xark_prover::rows_for_key(&bytes, wires, None).map_err(|e| anyhow::anyhow!(e))?;
    let z = src.layout().assignment(|id| {
        assign.get(id as usize).and_then(Option::as_ref).map(|v| {
            v.as_bn254_fr()
                .unwrap_or_else(|| fr_from_decimal(&v.to_decimal()))
        })
    });
    drop(assign);
    if z.len() != wires {
        bail!(
            "the gnark key in {} was made for another form of this circuit: run `xark \
             setup --backend gnark` again",
            keys.display()
        );
    }
    drop(src);
    let solve = t.elapsed();

    let out = args
        .out
        .clone()
        .unwrap_or_else(|| project.xark_dir.clone())
        .join("gnark");
    fs::create_dir_all(&out).with_context(|| format!("creating {}", out.display()))?;
    let wtns = out.join("witness.wtns");
    write_wtns(&wtns, &z)?;
    drop(z);
    let report = match run_tool(&[
        "prove".as_ref(),
        keys.as_os_str(),
        wtns.as_os_str(),
        out.as_os_str(),
    ]) {
        Ok(report) => report,
        Err(e) => {
            // gnark names the row it found unsatisfied; say which constraint of
            // the source that is, as `xark prove` does.
            super::explain_unsatisfied(&bytes, sources.as_ref(), &id_inputs)?;
            return Err(e);
        }
    };
    println!("Wrote {}", out.join("proof.bin").display());
    println!("Wrote {}", out.join("public_witness.bin").display());
    println!(
        "gnark proof: solve {:.2}s, prove {} (verified in {})",
        solve.as_secs_f64(),
        ms(&report, "prove_ms"),
        ms(&report, "verify_ms")
    );
    // The benchmark reads these; `PROVE_TIME=1` prints xark's own the same way.
    if super::dbg_flag("PROVE_TIME") {
        eprintln!(
            "PROVE_TIME: solve = {:.3}s, gnark prove = {}ms",
            solve.as_secs_f64(),
            report.get("prove_ms").map_or("?", String::as_str)
        );
    }
    let p = super::path_arg(&args.path);
    println!(
        "\n{}",
        crate::style::next_steps(&[(
            format!("xark verify {p} --backend gnark"),
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
    match run_tool(&[
        "verify".as_ref(),
        vk.as_os_str(),
        proof.as_os_str(),
        public.as_os_str(),
    ]) {
        Ok(_) => {
            println!("{}", crate::style::brand("✅ Proof verified (gnark)"));
            Ok(())
        }
        Err(_) => {
            println!("{}", crate::style::err("❌ Proof verification failed"));
            std::process::exit(2);
        }
    }
}
