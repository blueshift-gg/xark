//! `cargo xtask lean-export`: a `#[gadget]`'s exact R1CS as a Lean definition, for
//! the proofs in `formal/`.
//!
//! Each proven gadget has a harness, `formal/templates/<gadget>/`: a circuit that
//! calls it once on fresh inputs. The task builds the harness, records that call
//! (`xark_frontend::lower_recording_gadgets`) and writes its template, the rows
//! `a · b = c` over BN254's scalar field, its hints and its variables' roles, to
//! `formal/Formal/Templates/<Gadget>.lean`, with a hash of that data. The Lean
//! proofs are checked against that file; `--check` re-exports every harness and
//! fails, naming the gadget and both hashes, when the code no longer emits it.

use std::fmt::Write as _;
use std::path::PathBuf;

use anyhow::{Context, Result, bail};
use sha2::{Digest, Sha256};
use xark_frontend::GadgetTemplate;
use xark_ir::primitive::WitnessGen;
use xark_ir::{FieldConst, LinearCombination};

#[derive(clap::Args)]
pub struct Args {
    /// The gadget to export: a harness under formal/templates/.
    #[arg(required_unless_present_any = ["check", "coverage", "example"])]
    gadget: Option<String>,
    /// Re-export every harness and every exported example circuit; fail if one differs
    /// from its committed Lean file.
    #[arg(long, conflicts_with = "gadget")]
    check: bool,
    /// Export an example's whole circuit as its gadget calls and glue rows, to
    /// `formal/Formal/Circuits/<Example>.lean` (see `Formal/Circuit.lean`).
    #[arg(long, conflicts_with_all = ["gadget", "check", "coverage"])]
    example: Option<String>,
    /// Build every example and classify each call of a proven gadget: its proven
    /// template's rows, refused, or different rows; fail on any of the last two
    /// not in formal/coverage-allowlist.txt.
    #[arg(long, conflicts_with_all = ["gadget", "check"])]
    coverage: bool,
    /// With --coverage: check these circuit crates instead of the examples.
    #[arg(long, requires = "coverage")]
    circuit: Vec<PathBuf>,
    /// With --coverage: rewrite formal/Formal/Templates/Consts/, the Lean
    /// obligations for the constant plugs the examples pass.
    #[arg(long, requires = "coverage", conflicts_with = "circuit")]
    update: bool,
    /// With --coverage: only every n-th example, starting at k (`k/n`), for a check
    /// spread over machines. Every call is classified as in a full run; what needs
    /// every example at once (an allowlist entry or a committed obligation no example
    /// uses any more) is checked only by a full run.
    #[arg(long, requires = "coverage", conflicts_with_all = ["circuit", "update"], value_parser = crate::difftest::parse_shard)]
    shard: Option<(usize, usize)>,
}

pub fn run(args: Args) -> Result<()> {
    if args.coverage {
        return crate::coverage::run(&args.circuit, args.update, args.shard);
    }
    if let Some(gadget) = args.gadget {
        let (_, path, text, hash) = export(&gadget)?;
        std::fs::write(&path, text)?;
        println!("wrote {} ({hash})", path.display());
        return Ok(());
    }
    if let Some(example) = args.example {
        let (hash, files) = export_circuit(&example)?;
        for (path, text) in &files {
            std::fs::create_dir_all(path.parent().unwrap())?;
            std::fs::write(path, text)?;
        }
        println!(
            "wrote {} ({hash}, {} files)",
            files[0].0.display(),
            files.len()
        );
        return Ok(());
    }
    let mut drift = Vec::new();
    for example in exported_circuits()? {
        let (_, files) = export_circuit(&example)?;
        for (path, text) in &files {
            if std::fs::read_to_string(path).unwrap_or_default() != *text {
                drift.push(format!(
                    "{example}: {} isn't what the exporter writes; re-export it \
                     (`cargo xtask lean-export --example {example}`)",
                    path.display()
                ));
            }
        }
    }
    let harnesses = harnesses()?;
    for gadget in &harnesses {
        let (name, path, text, hash) = export(gadget)?;
        let committed = std::fs::read_to_string(&path).unwrap_or_default();
        match committed_hash(&committed) {
            None => drift.push(format!(
                "{gadget}: no template at {} (run `cargo xtask lean-export {gadget}`)",
                path.display()
            )),
            Some(proven) if proven != hash => drift.push(format!(
                "{gadget} (`{name}`): the code emits template {hash}, the proof was checked \
                 against {proven}; re-export it (`cargo xtask lean-export {gadget}`) and fix the proof"
            )),
            Some(_) if committed != text => drift.push(format!(
                "{gadget}: {} isn't what the exporter writes; re-export it",
                path.display()
            )),
            Some(_) => {}
        }
    }
    for entry in std::fs::read_dir(crate::root().join("formal/Formal/Templates"))? {
        let file = entry?.file_name().to_string_lossy().into_owned();
        if !file.ends_with(".lean") {
            continue;
        }
        if !harnesses
            .iter()
            .any(|g| format!("{}.lean", camel(g)) == file)
        {
            drift.push(format!(
                "formal/Formal/Templates/{file} has no harness under formal/templates/"
            ));
        }
    }
    if !drift.is_empty() {
        bail!("Lean templates differ from the code:\n{}", drift.join("\n"));
    }
    println!("all {} templates match their proofs", harnesses.len());
    Ok(())
}

/// Every harness under formal/templates/, sorted.
pub(crate) fn harnesses() -> Result<Vec<String>> {
    let mut names = Vec::new();
    for entry in std::fs::read_dir(templates_dir())? {
        let entry = entry?;
        if entry.file_type()?.is_dir() {
            names.push(entry.file_name().to_string_lossy().into_owned());
        }
    }
    names.sort();
    Ok(names)
}

fn templates_dir() -> PathBuf {
    crate::root().join("formal/templates")
}

/// Build `gadget`'s harness and record its one call of `…::<gadget>`.
pub(crate) fn harness(gadget: &str) -> Result<GadgetTemplate> {
    let dir = templates_dir().join(gadget);
    if !dir.join("Cargo.toml").exists() {
        bail!(
            "no harness for `{gadget}`: expected a circuit crate at {}",
            dir.display()
        );
    }
    let target = crate::build_dir(true, 0);
    let opts = xark_frontend::BuildOptions {
        gadget_markers: true,
        ..Default::default()
    };
    let wasm = xark_frontend::build_crate_with(&dir, &target, &opts)
        .map_err(|e| anyhow::anyhow!("{e}"))?
        .wasm;
    let out = xark_frontend::lower_recording_gadgets(&wasm, xark_ir::FieldSpec::bn254())
        .map_err(|e| anyhow::anyhow!("{e}"))?
        .output;
    // `<function>__<instance>` names one instantiation of a generic gadget
    // (`reduce__33`); its template is `Formal/Templates/<Function><Instance>.lean`.
    let function = gadget.split_once("__").map_or(gadget, |(f, _)| f);
    let suffix = format!("::{function}");
    let calls: Vec<_> = out
        .gadgets
        .into_iter()
        .filter(|c| c.name.ends_with(&suffix))
        .collect();
    match <[_; 1]>::try_from(calls) {
        Ok([call]) => call.template.map_err(|e| anyhow::anyhow!("{e}")),
        Err(calls) => bail!(
            "{}: the harness must call `#[gadget]` `…{suffix}` exactly once (it calls it {} times)",
            dir.display(),
            calls.len()
        ),
    }
}

/// Build `gadget`'s harness and render its one recorded call: the gadget's name, the
/// Lean file's path, its text and the template's hash.
fn export(gadget: &str) -> Result<(String, PathBuf, String, String)> {
    let template = harness(gadget)?;
    let module = camel(gadget);
    let data = render(&template).with_context(|| format!("exporting {}", template.name))?;
    let hash = hash(&data);
    let text = format!(
        "-- Generated by `cargo xtask lean-export {gadget}` from `{name}` (harness\n\
         -- formal/templates/{gadget}). Don't edit: `cargo xtask lean-export --check` fails\n\
         -- when the code stops emitting exactly this.\n\
         import Formal.Template\n\n\
         set_option linter.style.header false\n\
         set_option linter.style.longLine false\n\n\
         namespace Xark.Templates.{module}\n\
         open Xark.Template\n\n\
         -- A long list literal nests deeply (and so does its compiled code), and a\n\
         -- template of a few thousand rows takes more than the default heartbeats.\n\
         set_option maxRecDepth 100000 in\n\
         set_option maxHeartbeats 0 in\n\
         /-- `{name}`'s rows, hints and variables, as the frontend emits them. -/\n\
         def template : Template where\n  \
           hash := \"{hash}\"\n\
         {data}\n\
         end Xark.Templates.{module}\n",
        name = template.name,
    );
    let path = crate::root()
        .join("formal/Formal/Templates")
        .join(format!("{module}.lean"));
    Ok((template.name, path, text, hash))
}

/// The examples with a committed `formal/Formal/Circuits/<Example>.lean`, by their
/// example name (the file's first line names it).
fn exported_circuits() -> Result<Vec<String>> {
    let dir = crate::root().join("formal/Formal/Circuits");
    let mut names = Vec::new();
    for entry in std::fs::read_dir(&dir)? {
        let path = entry?.path();
        if path.extension().is_some_and(|e| e == "lean") {
            let text = std::fs::read_to_string(&path)?;
            let name = text
                .lines()
                .next()
                .and_then(|l| l.split_once("--example ")?.1.split_whitespace().next())
                .map(|n| n.trim_matches('`'))
                .with_context(|| format!("{}: no `--example <name>` header", path.display()))?;
            names.push(name.to_owned());
        }
    }
    names.sort();
    Ok(names)
}

/// BN254's scalar field modulus.
fn modulus() -> num_bigint::BigInt {
    num_bigint::BigInt::parse_bytes(
        xark_ir::FieldSpec::bn254()
            .modulus_decimal
            .unwrap()
            .as_bytes(),
        10,
    )
    .unwrap()
}

/// A combination in the normal form `Formal/Circuit.lean`'s `renderLC` prints: canonical
/// coefficients, terms by variable, merged, zeros dropped.
fn canonical(l: &LinearCombination, r: &num_bigint::BigInt) -> String {
    let canon = |c: &FieldConst| ((c.big() % r) + r) % r;
    let mut terms = std::collections::BTreeMap::<u32, num_bigint::BigInt>::new();
    for t in &l.terms {
        let e = terms.entry(t.var).or_default();
        *e = (&*e + canon(&t.coeff)) % r;
    }
    let terms: Vec<String> = terms
        .iter()
        .filter(|(_, c)| **c != num_bigint::BigInt::ZERO)
        .map(|(v, c)| format!("({c}, {v})"))
        .collect();
    format!("⟨{}, [{}]⟩", canon(&l.constant), terms.join(", "))
}

/// FNV-1a 64 of the rendered rows, one per line: what `Xark.Circuit.hash` computes.
fn circuit_hash(rows: &[[LinearCombination; 3]]) -> String {
    let r = modulus();
    let text: Vec<String> = rows
        .iter()
        .map(|[a, b, c]| {
            format!(
                "⟨{}, {}, {}⟩",
                canonical(a, &r),
                canonical(b, &r),
                canonical(c, &r)
            )
        })
        .collect();
    let mut h: u64 = 0xcbf29ce484222325;
    for byte in text.join("\n").bytes() {
        h = (h ^ u64::from(byte)).wrapping_mul(0x100000001b3);
    }
    format!("fnv1a64:{h:016x}")
}

/// Build `example` with the gadget markers and render its circuit as segments: runs of
/// glue rows and top-level calls of proven templates (`Xark.Circuit.Circuit`). Every
/// row is in exactly one segment, in order. The segments go to `Part<k>.lean` files of
/// about `PART_BYTES` each (one 4 MB file took 16 GB to elaborate), the main file lists
/// them and carries the compiler's hash of the rows, which `CircuitHash.lean` compares
/// with the hash of the Lean composition.
fn export_circuit(example: &str) -> Result<(String, Vec<(PathBuf, String)>)> {
    let proven = crate::coverage::proven()?;
    let digests = std::fs::read_to_string(crate::root().join("tests/stable-digests.txt"))?;
    // `<example> <keyed> <flat>`: the flat digest, as `coverage::calls` compares.
    let want = digests
        .lines()
        .find_map(|l| l.strip_prefix(&format!("{example} ")))
        .map(|d| d.rsplit(' ').next().unwrap_or(d).to_owned());
    let dir = crate::root().join("examples").join(example);
    let rec = crate::coverage::calls(&dir, Some(want), &proven, 0)?;
    let mut calls: Vec<&crate::coverage::Call> = rec
        .calls
        .iter()
        .filter(|c| c.parent.is_none() && c.rows > 0)
        .collect();
    calls.sort_by_key(|c| c.first_row);
    // Integer coefficients as constructors: a numeral at type `ℤ` costs the elaborator an
    // instance search each (90 s on one 300-term combination), `Int.ofNat n` none.
    let z = |c: &FieldConst| {
        let d = c.decimal();
        match d.strip_prefix('-') {
            Some(m) => format!(
                "(Int.negSucc {})",
                num_bigint::BigInt::parse_bytes(m.as_bytes(), 10).unwrap() - 1
            ),
            None => format!("(Int.ofNat {d})"),
        }
    };
    let lc = |l: &LinearCombination| {
        let terms: Vec<String> = l
            .terms
            .iter()
            .map(|t| format!("({}, {})", z(&t.coeff), t.var))
            .collect();
        format!("⟨{}, [{}]⟩", z(&l.constant), terms.join(", "))
    };
    let mut segs: Vec<String> = Vec::new();
    let mut ranges: Vec<(usize, usize)> = Vec::new();
    let count = std::cell::Cell::new(0usize);
    let segs_len = || {
        let n = count.get();
        count.set(n + 1);
        n
    };
    let mut modules = std::collections::BTreeSet::new();
    let mut row = 0usize;
    // One `def` per segment: a single list literal of every row and plug times out the
    // elaborator, and each definition then stays small enough to read.
    let glue = |from: usize, to: usize| {
        let rows: Vec<String> = rec.rows[from..to]
            .iter()
            .map(|[a, b, c]| format!("    ⟨{}, {}, {}⟩", lc(a), lc(b), lc(c)))
            .collect();
        format!(
            "-- rows {from}..{to}\nset_option maxHeartbeats 0 in\ndef s{} : Seg := .glue [\n{}]",
            segs_len(),
            rows.join(",\n")
        )
    };
    for c in calls {
        // Covered (plain, constant or combination plugs) and allowlisted LC-plug calls
        // emit the template's rows with their plugs substituted, which `Call.rows` is; a
        // fold drops rows, so a folded call fails the hash in `CircuitHash.lean`.
        if !(c.class.starts_with("covered") || c.class.starts_with("LC plugs")) {
            bail!(
                "{example}: the `{}` call at {} is `{}`: its rows aren't the template's with \
                 its plugs substituted, so the circuit can't be composed from templates yet",
                c.gadget,
                c.site,
                c.class
            );
        }
        if c.first_row < row {
            bail!("{example}: calls overlap at row {}", c.first_row);
        }
        let p = proven[&c.gadget]
            .iter()
            .find(|p| p.harness == c.harness)
            .expect("classified against a harness");
        let plain = p.template.inputs.iter().enumerate().all(|(i, l)| {
            l.constant.is_zero()
                && matches!(&l.terms[..], [t] if t.coeff.is_one() && t.var == i as u32)
        });
        if c.class.starts_with("covered with folded constants") {
            // The frontend dropped rows a constant made trivial: the call's rows as
            // emitted, which no template proof covers yet.
            if c.first_row > row {
                segs.push(glue(row, c.first_row));
                ranges.push((row, c.first_row));
            }
            let rows: Vec<String> = rec.rows[c.first_row..c.first_row + c.rows]
                .iter()
                .map(|[a, b, c]| format!("    ⟨{}, {}, {}⟩", lc(a), lc(b), lc(c)))
                .collect();
            segs.push(format!(
                "-- `{}` at {}: rows {}..{}, {}\nset_option maxHeartbeats 0 in\n\
                 def s{} : Seg := .folded \"{}\" [\n{}]",
                c.gadget,
                c.site,
                c.first_row,
                c.first_row + c.rows,
                c.class,
                segs_len(),
                c.gadget,
                rows.join(",\n")
            ));
            ranges.push((c.first_row, c.first_row + c.rows));
            row = c.first_row + c.rows;
            continue;
        }
        if c.rows != p.template.rows.len() {
            bail!(
                "{example}: the `{}` call at {} emitted {} rows, its template {} has {}",
                c.gadget,
                c.site,
                c.rows,
                c.harness,
                p.template.rows.len()
            );
        }
        if !plain || c.inputs.len() != p.template.inputs.len() {
            bail!(
                "{example}: harness {} doesn't call `{}` on one fresh variable per input, so \
                 `plug i` isn't input `i`",
                c.harness,
                c.gadget
            );
        }
        if c.first_row > row {
            segs.push(glue(row, c.first_row));
            ranges.push((row, c.first_row));
        }
        ranges.push((c.first_row, c.first_row + c.rows));
        let module = camel(&c.harness);
        modules.insert(module.clone());
        let plugs: Vec<String> = c.inputs.iter().map(lc).collect();
        segs.push(format!(
            "-- `{}` at {}: rows {}..{}\nset_option maxHeartbeats 0 in\n\
             def s{} : Seg := .call ⟨Xark.Templates.{module}.template, [{}], {}⟩",
            c.gadget,
            c.site,
            c.first_row,
            c.first_row + c.rows,
            segs_len(),
            plugs.join(", "),
            c.first_var
        ));
        row = c.first_row + c.rows;
    }
    if row < rec.rows.len() {
        segs.push(glue(row, rec.rows.len()));
        ranges.push((row, rec.rows.len()));
    }
    let hash = circuit_hash(&rec.rows);
    let seg_hashes: Vec<String> = ranges
        .iter()
        .map(|&(from, to)| format!("\"{}\"", circuit_hash(&rec.rows[from..to])))
        .collect();
    let module = camel(example);
    let imports: Vec<String> = modules
        .iter()
        .map(|m| format!("import Formal.Templates.{m}"))
        .collect();
    let publics: Vec<String> = rec.publics.iter().map(u32::to_string).collect();
    const PART_BYTES: usize = 400_000;
    let header = |extra: &str| {
        format!(
            "-- Generated by `cargo xtask lean-export --example {example}` from examples/{example}.\n\
             -- Don't edit: `cargo xtask lean-export --check` fails when the code stops emitting\n\
             -- exactly this, and `CircuitHash.lean` fails unless `circuit`'s rows hash to `expected`.\n\
             {extra}\n\n\
             set_option linter.style.header false\n\
             set_option linter.style.longLine false\n\n\
             namespace Xark.Circuits.{module}\n\
             open Xark.Circuit Xark.R1cs\n\n"
        )
    };
    let dir = crate::root().join("formal/Formal/Circuits");
    let mut files = Vec::new();
    let mut part = String::new();
    let flush = |part: &mut String, files: &mut Vec<(PathBuf, String)>| {
        if part.is_empty() {
            return;
        }
        let k = files.len();
        let text = format!(
            "{}set_option maxRecDepth 100000\n\n{}\nend Xark.Circuits.{module}\n",
            header(&format!("import Formal.Circuit\n{}", imports.join("\n"))),
            part
        );
        files.push((dir.join(&module).join(format!("Part{k}.lean")), text));
        part.clear();
    };
    for seg in &segs {
        if !part.is_empty() && part.len() + seg.len() > PART_BYTES {
            flush(&mut part, &mut files);
        }
        part.push_str(seg);
        part.push_str("\n\n");
    }
    flush(&mut part, &mut files);
    let parts: Vec<String> = (0..files.len())
        .map(|k| format!("import Formal.Circuits.{module}.Part{k}"))
        .collect();
    let main = format!(
        "{}/-- The compiler's hash of the {n} rows (`lean-export`'s `circuit_hash`). -/\n\
         def expected : String := \"{hash}\"\n\n\
         /-- The compiler's hash of each segment's rows. -/\n\
         def expectedSegs : List String := [{seg_hashes}]\n\n\
         /-- The public inputs' variables. -/\n\
         def publics : List ℕ := [{publics}]\n\n\
         /-- The circuit: glue rows and calls of proven templates, in row order. -/\n\
         def circuit : Circuit := [{list}]\n\n\
         end Xark.Circuits.{module}\n",
        header(&parts.join("\n")),
        n = rec.rows.len(),
        publics = publics.join(", "),
        seg_hashes = seg_hashes.join(", "),
        list = (0..segs.len())
            .map(|i| format!("s{i}"))
            .collect::<Vec<_>>()
            .join(", "),
    );
    files.insert(0, (dir.join(format!("{module}.lean")), main));
    Ok((hash, files))
}

/// A template's hash: the sha256 of its rendered data.
pub(crate) fn hash(data: &str) -> String {
    let digest = Sha256::digest(data.as_bytes());
    let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
    format!("sha256:{hex}")
}

/// The hash a committed template file records.
pub(crate) fn committed_hash(text: &str) -> Option<&str> {
    text.lines()
        .find_map(|l| l.trim().strip_prefix("hash := \""))
        .and_then(|l| l.strip_suffix('"'))
}

/// `add_mod` → `AddMod`.
pub(crate) fn camel(s: &str) -> String {
    s.split('_')
        .map(|w| {
            let mut c = w.chars();
            c.next()
                .map(|f| f.to_uppercase().chain(c).collect::<String>())
                .unwrap_or_default()
        })
        .collect()
}

/// The template's fields after `hash`, one per line (what the hash covers).
pub(crate) fn render(t: &GadgetTemplate) -> Result<String> {
    let plugs = t.plugs;
    let var = |v: u32| {
        if v < plugs {
            format!(".plug {v}")
        } else {
            format!(".wit {}", v - plugs)
        }
    };
    let lc = |l: &LinearCombination| {
        let terms: Vec<String> = l
            .terms
            .iter()
            .map(|t| format!("({}, {})", coeff(&t.coeff), var(t.var)))
            .collect();
        format!("⟨{}, [{}]⟩", coeff(&l.constant), terms.join(", "))
    };
    let lcs = |ls: &[LinearCombination]| ls.iter().map(lc).collect::<Vec<_>>().join(", ");
    let wit = |v: u32| -> Result<u32> {
        v.checked_sub(plugs)
            .context("a hint writes a variable from outside the call")
    };
    let mut hints = Vec::new();
    for h in &t.hints {
        hints.push(match h {
            WitnessGen::Product { out, left, right } => {
                format!(".product {} {} {}", wit(*out)?, lc(left), lc(right))
            }
            WitnessGen::Linear { out, lc: l } => format!(".linear {} {}", wit(*out)?, lc(l)),
            WitnessGen::Xor { out, a, b } => format!(".xor {} {} {}", wit(*out)?, lc(a), lc(b)),
            WitnessGen::Or { out, a, b } => format!(".or {} {} {}", wit(*out)?, lc(a), lc(b)),
            WitnessGen::Inverse { out, input } => format!(".inverse {} {}", wit(*out)?, lc(input)),
            WitnessGen::InverseOrZero { out, input } => {
                format!(".inverseOrZero {} {}", wit(*out)?, lc(input))
            }
            WitnessGen::Bit { out, input, index } => {
                format!(".bit {} {} {index}", wit(*out)?, lc(input))
            }
            WitnessGen::Bits { outs, input } => {
                let outs = outs.iter().map(|&o| wit(o)).collect::<Result<Vec<_>>>()?;
                format!(".bits {outs:?} {}", lc(input))
            }
            WitnessGen::DivRem { q, r, num, den } => {
                format!(".divRem {} {} {} {}", wit(*q)?, wit(*r)?, lc(num), lc(den))
            }
            WitnessGen::MulModDivMod { .. }
            | WitnessGen::ModInverse { .. }
            | WitnessGen::FakeGlv { .. }
            | WitnessGen::Sub2 { .. } => {
                bail!("its big-integer hints have no Lean meaning yet: add them to Formal/Template.lean's `Hint`")
            }
        });
    }
    let rows: Vec<String> = t
        .rows
        .iter()
        .map(|[a, b, c]| format!("⟨{}, {}, {}⟩", lc(a), lc(b), lc(c)))
        .collect();
    let mut s = String::new();
    writeln!(s, "  name := \"{}\"", t.name)?;
    writeln!(s, "  plugs := {plugs}")?;
    writeln!(s, "  wits := {}", t.witnesses)?;
    writeln!(s, "  inputs := [{}]", lcs(&t.inputs))?;
    writeln!(s, "  outputs := [{}]", lcs(&t.outputs))?;
    writeln!(s, "  hints := [\n    {}]", hints.join(",\n    "))?;
    writeln!(s, "  rows := [\n    {}]", rows.join(",\n    "))?;
    Ok(s)
}

/// A coefficient as the integer the frontend holds (any sign; it means its value
/// mod r).
fn coeff(c: &FieldConst) -> String {
    let d = c.decimal();
    if d.starts_with('-') {
        format!("({d})")
    } else {
        d
    }
}

#[cfg(test)]
mod tests {
    /// The alarm rings: a circuit whose composition differs from the compiler's rows by
    /// one coefficient is refused by `Xark.Circuit.check` (what `CircuitHash.lean` runs),
    /// naming the segment. Guards the CI wiring, not the hash function.
    #[test]
    #[ignore = "needs lake and the built Formal.Circuits modules; lean.yml runs it"]
    fn the_hash_check_refuses_a_mutated_circuit() {
        let formal = crate::root().join("formal");
        let probe = crate::target_dir().join("circuit-check-test");
        std::fs::create_dir_all(&probe).unwrap();
        let file = probe.join("Mutant.lean");
        std::fs::write(
            &file,
            "import Formal.Circuits.Secp256k1Ecdsa\n\
             open Xark.Circuit\n\
             /-- The first glue segment's first row, with its `a` constant bumped. -/\n\
             def mutant : Circuit → Circuit\n\
               | .glue (r :: rs) :: rest => .glue ({ r with a := ⟨r.a.const + 1, r.a.terms⟩ } :: rs) :: rest\n\
               | s :: rest => s :: mutant rest\n\
               | [] => []\n\
             #eval check \"Mutant\" (mutant Xark.Circuits.Secp256k1Ecdsa.circuit) \
             Xark.Circuits.Secp256k1Ecdsa.expected Xark.Circuits.Secp256k1Ecdsa.expectedSegs\n",
        )
        .unwrap();
        let out = std::process::Command::new("lake")
            .args(["env", "lean", file.to_str().unwrap()])
            .current_dir(&formal)
            .output()
            .unwrap();
        let text = String::from_utf8_lossy(&out.stdout).to_string()
            + &String::from_utf8_lossy(&out.stderr);
        assert!(!out.status.success(), "the mutant passed: {text}");
        assert!(
            text.contains("first differing segment: s"),
            "refused for another reason: {text}"
        );
    }
}
