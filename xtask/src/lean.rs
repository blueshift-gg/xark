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
    #[arg(required_unless_present_any = ["check", "coverage"])]
    gadget: Option<String>,
    /// Re-export every harness; fail if one differs from its committed Lean file.
    #[arg(long, conflicts_with = "gadget")]
    check: bool,
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
}

pub fn run(args: Args) -> Result<()> {
    if args.coverage {
        return crate::coverage::run(&args.circuit, args.update);
    }
    if let Some(gadget) = args.gadget {
        let (_, path, text, hash) = export(&gadget)?;
        std::fs::write(&path, text)?;
        println!("wrote {} ({hash})", path.display());
        return Ok(());
    }
    let mut drift = Vec::new();
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
    let target = crate::target_dir().join("lean-export").join(gadget);
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
