//! iden3's two files, the formats circom writes and snarkjs reads: a circuit's
//! keyed rows as `circuit.r1cs`
//! (<https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md>) and a
//! solved witness as `witness.wtns`. `xark export --format iden3` writes them for
//! any prover that takes them; `--backend gnark` (`gnark.rs`) hands them to gnark.

use std::collections::BTreeMap;
use std::fs;
use std::io::{BufWriter, Seek, SeekFrom, Write};
use std::path::Path;

use anyhow::{Context, Result, bail};
use ark_bn254::Fr;
use ark_serialize::CanonicalSerialize;
use xark_groth16::ConstraintSource;
use xark_groth16::r1cs::RowChunk;
use xark_ir::VarId;
use xark_ir::solver::Fp;
use xark_prover::fr_from_decimal;

use super::{export::ExportArgs, setup, setup::SetupArgs};
use crate::xark_project::XarkProject;

/// The BN254 scalar field's modulus, little-endian: the prime both headers carry.
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
pub(super) fn write_r1cs(path: &Path, src: &dyn ConstraintSource) -> Result<()> {
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

/// Write the assignment `z` (the constant one first) as an iden3 `.wtns` file,
/// readable by its owner only where the system has such a thing: it holds the
/// private inputs.
pub(super) fn write_wtns(path: &Path, z: &[Fr]) -> Result<()> {
    // A file of this name from an earlier run keeps its own permissions, so it
    // goes first and the new one is made private from its first byte.
    match fs::remove_file(path) {
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => {
            return Err(e).with_context(|| format!("replacing {}", path.display()));
        }
        _ => {}
    }
    let mut open = fs::OpenOptions::new();
    open.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        open.mode(0o600);
    }
    let f = open
        .open(path)
        .with_context(|| format!("creating {}", path.display()))?;
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
pub(super) fn r1cs_wires(path: &Path) -> Result<usize> {
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

/// The value of every wire of `src`, in wire order, from a solved witness.
pub(super) fn assignment(src: &dyn ConstraintSource, assign: &[Option<Fp>]) -> Vec<Fr> {
    src.layout().assignment(|id| {
        assign.get(id as usize).and_then(Option::as_ref).map(|v| {
            v.as_bn254_fr()
                .unwrap_or_else(|| fr_from_decimal(&v.to_decimal()))
        })
    })
}

/// The inputs `--inputs` names, by variable, and the witness they solve to.
pub(super) struct Solved {
    pub inputs: BTreeMap<VarId, String>,
    pub assign: Vec<Option<Fp>>,
}

pub(super) fn solve(project: &XarkProject, xbc: &[u8], arg: Option<&str>) -> Result<Solved> {
    let inputs = match arg {
        Some(arg) => super::read_inputs(&project.xark_dir, arg)?,
        None => Default::default(),
    };
    let sources = super::load_sources(&project.xark_dir);
    let vars = xark_ir::function_decode::decode_input_vars(xbc).map_err(|e| anyhow::anyhow!(e))?;
    let inputs = super::resolve_input_ids(&vars, &inputs)?;
    let assign = super::stream_witness(xbc, sources.as_ref(), &inputs)?;
    Ok(Solved { inputs, assign })
}

/// `xark export --format iden3`: the keyed rows as `circuit.r1cs` and, with
/// `--inputs`, the witness they solve to as `witness.wtns`.
pub fn export(args: &ExportArgs) -> Result<()> {
    if args.verifying_key.is_some()
        || args.proof.is_some()
        || args.public_inputs.is_some()
        || args.crate_name.is_some()
    {
        bail!(
            "--format iden3 writes the circuit's rows (and with --inputs its witness): \
             --verifying-key, --proof, --public-inputs and --crate-name are the Solana \
             verifier's"
        );
    }
    let project = XarkProject::resolve(args.path.clone())?;
    crate::cli::build_if_needed(&project.xark_dir, true)?;
    let dir = args
        .out
        .clone()
        .unwrap_or_else(|| project.xark_dir.join("iden3"));
    fs::create_dir_all(&dir).with_context(|| format!("creating {}", dir.display()))?;

    // The rows a key over a 2^k domain is made for: the domain snarkjs, rapidsnark
    // and gnark all take.
    let setup_args = SetupArgs::defaults(args.path.clone());
    let (keyed, form, why, ..) = setup::plan_keyed(&setup_args, &project, args.r1cs_form, true)?;
    println!("R1CS form: {form} ({why})");
    let r1cs = dir.join("circuit.r1cs");
    keyed.with_source(|src| write_r1cs(&r1cs, src))?;
    println!("Wrote {}", r1cs.display());

    if let Some(inputs) = &args.inputs {
        let xbc = project.circuit_xbc();
        let bytes = fs::read(&xbc).with_context(|| format!("reading {}", xbc.display()))?;
        let solved = solve(&project, &bytes, Some(inputs))?;
        let z = keyed.with_source(|src| assignment(src, &solved.assign));
        let wtns = dir.join("witness.wtns");
        write_wtns(&wtns, &z)?;
        println!(
            "Wrote {} (it holds the private inputs: keep it as you keep them)",
            wtns.display()
        );
    }
    Ok(())
}
