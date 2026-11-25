//! `cargo xtask lean-export --witnesses`: a witness of every harness's soundness
//! hypotheses, so no soundness theorem holds vacuously.
//!
//! A soundness theorem `∀ σ, Assumptions (ins σ) → Sat σ → Spec …` says nothing when
//! no `σ` meets its hypotheses. For each harness this writes
//! `formal/Formal/Templates/Witness/<Gadget>.lean`, whose `satisfiable` proves
//! `obligation% soundness` (`Formal/TemplateSolve.lean`) at one assignment: the plug
//! values a production call of the gadget received while an example's `xark test`
//! ran, and the witness `xark_ir::solver` computes from them on the proven template.
//! `decide +kernel` checks that assignment, so nothing here is trusted: a wrong value
//! fails the Lean build. Rerun after a template changes; its build fails when the
//! old witness no longer fits.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;
use std::sync::{LazyLock, Mutex};

use anyhow::{Context, Result, bail};
use num_bigint::BigInt;
use xark_frontend::GadgetTemplate;
use xark_ir::primitive::{FieldSpec, PrimitiveProgram, Var, VarRole};
use xark_ir::{LinearCombination, VarId, solver};

use crate::coverage::Proven;

/// Witness values per chunk of `assign`'s list (`Formal/TemplateSolve.lean` says why).
const CHUNK: usize = 64;

/// A satisfying assignment of one harness's template, and where its plug values came
/// from (an example, or none: zeros).
struct Witness {
    example: String,
    source: String,
    plugs: Vec<BigInt>,
    wits: Vec<BigInt>,
}

/// What one example gives: the gadgets it calls, and a witness per harness its first
/// accepted test input satisfies.
struct Found {
    gadgets: Vec<String>,
    witnesses: BTreeMap<String, Witness>,
}

pub fn run() -> Result<()> {
    crate::cargo_build(&["-p", "xark-cli", "--bin", "xark"])?;
    let xark = crate::target_dir().join("release/xark");
    let work = crate::target_dir().join("witnesses");
    let proven = crate::coverage::proven()?;
    let digests = crate::coverage::flat_digests()?;
    let found = Mutex::new(BTreeMap::<String, Witness>::new());
    let reached = Mutex::new(BTreeSet::<String>::new());
    let failures = Mutex::new(Vec::new());
    crate::parallel(crate::circuits()?, crate::default_jobs(), |worker, name| {
        let Some(digest) = digests.get(&name) else {
            let e = format!("{name}: not in tests/stable-digests.txt");
            failures.lock().unwrap().push(e);
            return;
        };
        match from_example(&name, digest, &xark, &work, &proven, worker) {
            Ok(Found { gadgets, witnesses }) => {
                reached.lock().unwrap().extend(gadgets);
                // The first example by name wins, so a rerun writes the same files.
                let mut found = found.lock().unwrap();
                for (harness, w) in witnesses {
                    if found.get(&harness).is_none_or(|k| w.example < k.example) {
                        found.insert(harness, w);
                    }
                }
            }
            Err(e) => failures.lock().unwrap().push(format!("{name}: {e:#}")),
        }
    });
    let (mut found, reached) = (found.into_inner().unwrap(), reached.into_inner().unwrap());
    let mut failures = failures.into_inner().unwrap();
    let mut files = Vec::new();
    for p in proven.values().flatten() {
        let w = match found.remove(&p.harness) {
            Some(w) => w,
            // No example calls the gadget (`xark::lang::or`): zeros, when its rows accept
            // them. A gadget the examples do call must get its witness from one of them.
            None if !reached.contains(&p.template.name) => match zeros(&p.template)? {
                Some(w) => w,
                None => {
                    failures.push(format!(
                        "{}: no example calls it, and its rows refuse zeros",
                        p.harness
                    ));
                    continue;
                }
            },
            None => {
                failures.push(format!(
                    "{}: called, but no call's values satisfy its template",
                    p.harness
                ));
                continue;
            }
        };
        let module = crate::lean::camel(&p.harness);
        files.push((format!("{module}.lean"), render(p, &module, &w)));
    }
    // Nothing is written unless every harness has its witness: a half-run would replace
    // good witnesses with whatever the examples that did run gave.
    if !failures.is_empty() {
        bail!("witnesses missing:\n{}", failures.join("\n"));
    }
    let dir = crate::root().join("formal/Formal/Templates/Witness");
    std::fs::create_dir_all(&dir)?;
    for (name, text) in &files {
        std::fs::write(dir.join(name), text)?;
    }
    println!("wrote {} witnesses to {}", files.len(), dir.display());
    Ok(())
}

/// A witness on zero plugs, when `t`'s rows accept them: for a gadget no example calls,
/// which still has a soundness theorem.
fn zeros(t: &GadgetTemplate) -> Result<Option<Witness>> {
    let plugs = vec![BigInt::ZERO; t.plugs as usize];
    Ok(solve_template(t, &plugs)?.map(|wits| Witness {
        example: String::new(),
        source: "zero plug values: no example calls the gadget".into(),
        plugs,
        wits,
    }))
}

fn from_example(
    name: &str,
    digest: &str,
    xark: &Path,
    work: &Path,
    proven: &BTreeMap<String, Vec<Proven>>,
    worker: usize,
) -> Result<Found> {
    let example = crate::root().join("examples").join(name);
    let dump = work.join("dumps").join(name);
    let _ = std::fs::remove_dir_all(&dump);
    crate::run(
        Command::new(xark)
            .arg("test")
            .arg(&example)
            .env("XARK_DUMP_INPUTS", &dump)
            .env("CARGO_TARGET_DIR", work.join("target")),
    )?;
    let rec = crate::coverage::calls(&example, Some(Some(digest.to_string())), proven, worker)?;
    let gadgets = rec.calls.iter().map(|c| c.gadget.clone()).collect();
    let Some(assign) = first_accepted(&dump, &rec.program)? else {
        let witnesses = BTreeMap::new();
        return Ok(Found { gadgets, witnesses });
    };
    let value = |v: VarId| assign.get(&rec.var_map[v as usize]).cloned();
    let mut witnesses = BTreeMap::new();
    // Against every instantiation of the gadget: coverage classifies a call against the
    // closest one, but any whose rows its values satisfy is a witness for that one.
    for call in &rec.calls {
        for p in &proven[&call.gadget] {
            if witnesses.contains_key(&p.harness) {
                continue;
            }
            let Some(plugs) = plug_values(&p.template, &call.inputs, &value) else {
                continue;
            };
            if let Some(wits) = solve_template(&p.template, &plugs)? {
                let source = format!(
                    "the inputs `xark test` gave examples/{name} (the call at {})",
                    call.at
                );
                let w = Witness {
                    example: name.into(),
                    source,
                    plugs,
                    wits,
                };
                witnesses.insert(p.harness.clone(), w);
            }
        }
    }
    Ok(Found { gadgets, witnesses })
}

/// The assignment of `program` on the first recorded input it accepts.
fn first_accepted(
    dump: &Path,
    program: &PrimitiveProgram,
) -> Result<Option<BTreeMap<VarId, BigInt>>> {
    let Ok(entries) = std::fs::read_dir(dump) else {
        return Ok(None);
    };
    let mut files: Vec<_> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
    files.sort();
    let ids: BTreeMap<&str, VarId> = program
        .vars
        .iter()
        .filter(|v| matches!(v.role, VarRole::PublicInput | VarRole::PrivateInput))
        .map(|v| (v.name.as_str(), v.id))
        .collect();
    for f in files {
        let doc: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&f)?)
            .with_context(|| f.display().to_string())?;
        // `{"circuit", "inputs": [[leaf, decimal]…], "ok"}`: `solve_and_check_recorded`.
        let leaves = doc["inputs"].as_array().into_iter().flatten();
        let inputs: Option<BTreeMap<VarId, String>> = leaves
            .map(|l| Some((*ids.get(l[0].as_str()?)?, l[1].as_str()?.to_string())))
            .collect();
        let Some(inputs) = inputs.filter(|i| doc["ok"] == true && i.len() == ids.len()) else {
            continue;
        };
        if let Ok(assign) = solver::solve_and_check(program, &inputs) {
            return Ok(Some(assign.iter().map(|(&v, x)| (v, big(x))).collect()));
        }
    }
    Ok(None)
}

/// The value of each of `t`'s plugs in a call passing `inputs`, when each input of the
/// template is one plug (as `GadgetTemplate::substitution_of` asks): it carries the
/// value of the call's input in the same position, the same one wherever it is read.
fn plug_values(
    t: &GadgetTemplate,
    inputs: &[LinearCombination],
    value: &dyn Fn(VarId) -> Option<BigInt>,
) -> Option<Vec<BigInt>> {
    if inputs.len() != t.inputs.len() {
        return None;
    }
    let mut plugs = vec![None; t.plugs as usize];
    for (mine, theirs) in t.inputs.iter().zip(inputs) {
        let [term] = &mine.terms[..] else { return None };
        if !mine.constant.is_zero() || !term.coeff.is_one() {
            return None;
        }
        let v = eval(theirs, value)?;
        let slot = plugs.get_mut(term.var as usize)?;
        if slot.as_ref().is_some_and(|w| *w != v) {
            return None;
        }
        *slot = Some(v);
    }
    plugs.into_iter().collect()
}

/// The witness `xark_ir::solver` computes on `t` from plug values `plugs`, when every
/// row then holds.
fn solve_template(t: &GadgetTemplate, plugs: &[BigInt]) -> Result<Option<Vec<BigInt>>> {
    let var = |id, role| Var {
        id,
        name: format!("v{id}"),
        role,
    };
    let vars = (0..t.plugs)
        .map(|v| var(v, VarRole::PrivateInput))
        .chain((t.plugs..t.plugs + t.witnesses).map(|v| var(v, VarRole::Derived)))
        .collect();
    let program = PrimitiveProgram {
        field: FieldSpec::bn254(),
        vars,
        constraints: Vec::new(),
        witness_gen: t.hints.clone(),
    };
    let inputs = (0..t.plugs)
        .map(|v| (v, plugs[v as usize].to_string()))
        .collect();
    let Ok(assign) = solver::solve(&program, &inputs) else {
        return Ok(None);
    };
    let value = |v: VarId| Some(assign.get(&v).map_or(BigInt::ZERO, big));
    let holds = t.rows.iter().all(|[a, b, c]| {
        let (a, b, c) = (eval(a, &value), eval(b, &value), eval(c, &value));
        a.zip(b)
            .zip(c)
            .is_some_and(|((a, b), c)| (a * b - c) % &*R == BigInt::ZERO)
    });
    let wits = (t.plugs..t.plugs + t.witnesses)
        .map(|v| value(v).unwrap())
        .collect();
    Ok(holds.then_some(wits))
}

/// A solver value as an integer in `0..r`.
fn big(x: &solver::Fp) -> BigInt {
    x.to_decimal().parse().expect("a decimal field element")
}

/// BN254's scalar field order, `ark_bn254::Fr`'s modulus.
static R: LazyLock<BigInt> = LazyLock::new(|| {
    let decimal = FieldSpec::bn254().modulus_decimal;
    decimal.parse().expect("a decimal modulus")
});

/// `l` under `value`, reduced to `0..r`.
fn eval(l: &LinearCombination, value: &dyn Fn(VarId) -> Option<BigInt>) -> Option<BigInt> {
    let mut acc = l.constant.big();
    for t in &l.terms {
        acc += t.coeff.big() * value(t.var)?;
    }
    Some(((acc % &*R) + &*R) % &*R)
}

fn render(p: &Proven, module: &str, w: &Witness) -> String {
    let list = |xs: &[BigInt]| {
        let xs: Vec<String> = xs.iter().map(BigInt::to_string).collect();
        format!("[{}]", xs.join(", "))
    };
    format!(
        "-- Generated by `cargo xtask lean-export --witnesses` from {source}.\n\
         -- Don't edit: rerun it after the template changes.\n\
         import {proof}\n\
         import Formal.TemplateSolve\n\n\
         set_option linter.style.header false\n\
         set_option linter.style.longLine false\n\n\
         namespace Xark.Templates.{module}\n\
         open Xark.Template\n\n\
         set_option maxRecDepth 100000 in\n\
         /-- `soundness` doesn't hold vacuously: these plug values, and the witness the\n\
         solver computes from them, meet its hypotheses. -/\n\
         theorem satisfiable : obligation% soundness :=\n  \
         ⟨assign {plugs} {CHUNK}\n    [{wits}], by decide +kernel⟩\n\n\
         end Xark.Templates.{module}\n",
        source = w.source,
        proof = p.proof,
        plugs = list(&w.plugs),
        // In chunks: `assign` (`Formal/TemplateSolve.lean`) says why.
        wits = w
            .wits
            .chunks(CHUNK)
            .map(list)
            .collect::<Vec<_>>()
            .join(",\n    "),
    )
}
