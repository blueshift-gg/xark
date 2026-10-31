//! `cargo xtask lean-export --coverage`: does every production call of a proven
//! `#[gadget]` emit the rows its proof is about?
//!
//! A template is proven over one harness call on fresh inputs. In a real circuit
//! the same call can emit other rows: a constant input folds, a decomposition memo
//! hit reuses bits from outside the call, a caller's `require_eq` merges into it, a
//! witness branch guards it. This builds every example with the gadget markers,
//! checks that build keys the production rows (its keyed-rows digest is the one in
//! `tests/stable-digests.txt`), and classifies each call of a gadget with a
//! harness and a committed `formal/Formal/Templates/*.lean`:
//!
//! * **covered**: its template (rows, hints, inputs, outputs, variables renamed as
//!   the export renames them) hashes to the proven template's hash;
//! * **covered with constant plugs**: it is the proven template with some input
//!   plugs replaced by the constants the call passes (every linear combination
//!   reduced mod `r`); `Template.soundness_inst` carries the
//!   proof over, given `Assumptions` of those constants, which
//!   `formal/Formal/Templates/Consts/<Gadget>.lean` proves per constant vector;
//! * **refused**: the recorder can't attribute its rows exactly to the call (the
//!   reason says why);
//! * **different rows**: neither.
//!
//! Calls are grouped by (gadget, circuit, call site, classification). A refused or
//! different group fails the check unless `formal/coverage-allowlist.txt` lists it
//! with a reason; an entry no group matches fails too, so the list stays current.
//! A missing or stale `Consts/<Gadget>.lean` fails (`--update` rewrites them).

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use anyhow::{Context, Result, bail};
use sha2::{Digest, Sha256};
use xark_frontend::GadgetTemplate;

const ALLOWLIST: &str = "formal/coverage-allowlist.txt";

/// (gadget, circuit, site, classification).
type Group = (String, String, String, String);

/// A gadget's constant plug vectors `(plug, value mod r)`, and the circuits using
/// each; the empty vector stands for its calls with LC plugs (no assumptions).
type Vectors = BTreeMap<Vec<(u32, String)>, BTreeSet<String>>;

/// A gadget with a proof: its harness and the template its proof is about.
struct Proven {
    harness: String,
    hash: String,
    template: GadgetTemplate,
    /// Its soundness theorem assumes nothing of the inputs.
    trivial: bool,
}

/// One recorded call of a proven gadget.
struct Call {
    gadget: String,
    site: String,
    class: String,
    consts: Option<Vec<(u32, String)>>,
}

pub fn run(circuits: &[PathBuf], update: bool) -> Result<()> {
    let t = std::time::Instant::now();
    let proven = proven()?;
    let examples = circuits.is_empty();
    let targets: Vec<PathBuf> = if examples {
        crate::circuits()?
            .into_iter()
            .map(|n| crate::root().join("examples").join(n))
            .collect()
    } else {
        let full = circuits
            .iter()
            .map(|c| c.canonicalize().with_context(|| c.display().to_string()));
        full.collect::<Result<_>>()?
    };
    let digests = std::fs::read_to_string(crate::root().join("tests/stable-digests.txt"))?;
    // `<example> <keyed> <flat>`: the keyed digest.
    let digests: BTreeMap<&str, &str> = digests
        .lines()
        .filter_map(|l| l.split_once(' '))
        .map(|(n, d)| (n, d.split(' ').next().unwrap_or(d)))
        .collect();

    let groups = Mutex::new(BTreeMap::<Group, usize>::new());
    let vectors = Mutex::new(BTreeMap::<String, Vectors>::new());
    let failures = Mutex::new(Vec::new());
    crate::parallel(targets, crate::default_jobs(), |dir| {
        let name = dir.file_name().unwrap().to_string_lossy().into_owned();
        let want = examples.then(|| digests.get(name.as_str()).map(|d| d.to_string()));
        match calls(&dir, &name, want, &proven) {
            Ok(calls) => {
                let (mut g, mut v) = (groups.lock().unwrap(), vectors.lock().unwrap());
                for c in calls {
                    if let Some(k) = c.consts {
                        let users = v.entry(c.gadget.clone()).or_default().entry(k);
                        users.or_default().insert(name.clone());
                    }
                    *g.entry((c.gadget, name.clone(), c.site, c.class))
                        .or_default() += 1;
                }
            }
            Err(e) => failures.lock().unwrap().push(format!("{name}: {e:#}")),
        }
    });
    let groups = groups.into_inner().unwrap();
    let vectors = vectors.into_inner().unwrap();
    let mut failures = failures.into_inner().unwrap();

    let (problems, missing) = obligations(&proven, &vectors, update, examples)?;
    failures.extend(problems);
    // A call whose obligation isn't committed isn't covered.
    let groups: BTreeMap<Group, usize> = groups
        .into_iter()
        .map(
            |((g, c, s, class), n)| match missing.iter().find(|m| class.contains(*m)) {
                Some(_) => (
                    (
                        g,
                        c,
                        s,
                        format!("not covered: {class} has no committed obligation"),
                    ),
                    n,
                ),
                None => ((g, c, s, class), n),
            },
        )
        .collect();
    let mut allow = allowlist()?;
    for ((gadget, circuit, site, class), n) in &groups {
        let calls = if *n == 1 { "call" } else { "calls" };
        // A refused call's rows are unknown: its entry also pins how many there are.
        let class = &match class.strip_prefix("refused: ") {
            Some(why) => format!("refused ({n} {calls}): {why}"),
            None => class.clone(),
        };
        let verdict = if class.starts_with("covered") {
            String::new()
        } else if let Some((reason, used)) = allow.get_mut(&key(gadget, circuit, site, class)) {
            *used = true;
            format!(" — allowlisted: {reason}")
        } else {
            failures.push(format!("{gadget} in {circuit} at {site}: {class}"));
            " — not allowlisted".into()
        };
        println!("{gadget}  {circuit}  {site}: {n} {calls} {class}{verdict}");
    }
    if examples {
        for (k, (_, used)) in &allow {
            if !used {
                failures.push(format!("{ALLOWLIST}: no call matches `{k}`; remove it"));
            }
        }
    }
    for gadget in proven.keys() {
        let mut n = BTreeMap::<&str, usize>::new();
        for ((g, _, _, class), m) in &groups {
            if g == gadget {
                *n.entry(class.split(" (").next().unwrap_or(class))
                    .or_default() += m;
                *n.entry("total").or_default() += m;
            }
        }
        let get = |k: &str| n.get(k).copied().unwrap_or(0);
        println!(
            "{gadget}: {} of {} calls covered ({} the proven template, {} with constant \
             plugs, {} with LC plugs); {} caller-enforced, {} without a committed \
             obligation, {} refused, {} different",
            get("covered") + get("covered with constant plugs") + get("covered with LC plugs"),
            get("total"),
            get("covered"),
            get("covered with constant plugs"),
            get("covered with LC plugs"),
            get("LC plugs: the caller must enforce Assumptions"),
            get("not covered: covered with constant plugs")
                + get("not covered: covered with LC plugs"),
            n.iter()
                .filter(|(k, _)| k.starts_with("refused"))
                .map(|(_, m)| m)
                .sum::<usize>(),
            get("different rows"),
        );
    }
    println!("coverage took {:.0?}", t.elapsed());
    if !failures.is_empty() {
        bail!("coverage of proven gadgets fails:\n{}", failures.join("\n"));
    }
    Ok(())
}

/// Every gadget with a harness: its template, which must be the one its committed
/// Lean file (and so its proof) is about.
fn proven() -> Result<BTreeMap<String, Proven>> {
    let mut out = BTreeMap::new();
    for harness in crate::lean::harnesses()? {
        let template = crate::lean::harness(&harness)?;
        let hash = crate::lean::hash(&crate::lean::render(&template)?);
        let path = crate::root()
            .join("formal/Formal/Templates")
            .join(format!("{}.lean", crate::lean::camel(&harness)));
        let committed = std::fs::read_to_string(&path).unwrap_or_default();
        if crate::lean::committed_hash(&committed) != Some(hash.as_str()) {
            bail!(
                "{harness}: its harness no longer emits the proven template (run `cargo xtask lean-export --check`)"
            );
        }
        // A soundness theorem with no hypothesis but the rows needs nothing of the
        // inputs, whatever combinations a caller passes.
        let proof = crate::root()
            .join("formal/Formal")
            .join(format!("{}.lean", crate::lean::camel(&harness)));
        let proof = std::fs::read_to_string(&proof).unwrap_or_default();
        let trivial = proof
            .lines()
            .any(|l| l.trim_end() == "theorem soundness (σ : TVar → F) (h : template.Sat σ) :");
        let p = Proven {
            harness,
            hash,
            template,
            trivial,
        };
        out.insert(p.template.name.clone(), p);
    }
    Ok(out)
}

/// Build `dir` with the gadget markers and classify its calls of proven gadgets.
/// First, the build must be the production circuit: its digest is `want` (an
/// example's committed digest), or with no `want` the digest of the same crate
/// built without markers.
fn calls(
    dir: &Path,
    name: &str,
    want: Option<Option<String>>,
    proven: &BTreeMap<String, Proven>,
) -> Result<Vec<Call>> {
    let target = crate::target_dir().join("coverage").join(name);
    let lower = |markers: bool| -> Result<xark_frontend::LowerOutput> {
        let opts = xark_frontend::BuildOptions {
            gadget_markers: markers,
            ..Default::default()
        };
        let sub = if markers { "marked" } else { "plain" };
        let wasm = xark_frontend::build_crate_with(dir, &target.join(sub), &opts)
            .map_err(|e| anyhow::anyhow!("{e}"))?;
        let field = xark_ir::FieldSpec::bn254();
        let out = if markers {
            xark_frontend::lower_recording_gadgets(&wasm, field)
        } else {
            xark_frontend::lower_module(&wasm, field, false, false)
        };
        Ok(out.map_err(|e| anyhow::anyhow!("{e}"))?.output)
    };
    let digest = |out: &xark_frontend::LowerOutput| crate::digests::keyed_digest(&out.xbc);
    let out = lower(true)?;
    // The templates are cut from the flat rows; the digest is the artifact's.
    xark_ir::function_decode::verify_blob_matches(&out.xbc, &out.r1cs, &out.primitive)
        .map_err(|e| anyhow::anyhow!("circuit.xbc doesn't match the flat lowering: {e}"))?;
    let want = match want {
        Some(Some(d)) => d,
        Some(None) => bail!("not in tests/stable-digests.txt"),
        None => digest(&lower(false)?)?,
    };
    let got = digest(&out)?;
    if got != want {
        bail!("built with the gadget markers it keys rows {got}, not the production {want}");
    }
    let root = format!("{}/", crate::root().display());
    Ok(out
        .gadgets
        .into_iter()
        .filter_map(|c| {
            let p = proven.get(&c.name)?;
            let (class, consts) = classify(c.template, p);
            let site = c.site.replace(&root, "");
            Some(Call {
                gadget: c.name,
                site,
                class,
                consts,
            })
        })
        .collect())
}

/// A call's classification, and its constant plugs when it is the proven
/// template with constants substituted for some plugs (and the others plain,
/// distinct variables, as in the template).
fn classify(
    call: Result<GadgetTemplate, String>,
    p: &Proven,
) -> (String, Option<Vec<(u32, String)>>) {
    let call = call.and_then(|t| {
        let hash = crate::lean::render(&t).map_err(|e| format!("{e:#}"))?;
        Ok((crate::lean::hash(&hash), t))
    });
    match call {
        Ok((h, _)) if h == p.hash => ("covered".into(), None),
        Ok((h, t)) => match p.template.substitution_of(&t) {
            None => (format!("different rows (template {})", &h[..23]), None),
            Some(sub) => {
                let var = |e: &xark_ir::LinearCombination| match &e.terms[..] {
                    [u] if e.constant.is_zero() && u.coeff.is_one() => Some(u.var),
                    _ => None,
                };
                let vars: Vec<u32> = sub.iter().filter_map(|(_, e)| var(e)).collect();
                let k: Vec<(u32, String)> = sub
                    .iter()
                    .filter(|(_, e)| e.is_constant())
                    .map(|(p, e)| (*p, e.constant.decimal()))
                    .collect();
                let distinct = vars.iter().collect::<BTreeSet<_>>().len() == vars.len();
                if !k.is_empty() && distinct && vars.len() + k.len() == sub.len() {
                    let class = format!("covered with constant plugs ({})", vector_name(&k));
                    (class, Some(k))
                } else if p.trivial {
                    // The empty vector: the obligation that soundness assumes nothing.
                    (
                        "covered with LC plugs (no assumptions)".into(),
                        Some(Vec::new()),
                    )
                } else {
                    ("LC plugs: the caller must enforce Assumptions".into(), None)
                }
            }
        },
        Err(why) => (refusal(&why), None),
    }
}

/// `k_<16 hex>`: a constant vector's Lean name, from its plugs and values.
fn vector_name(k: &[(u32, String)]) -> String {
    let text: Vec<String> = k.iter().map(|(p, v)| format!("{p}={v}")).collect();
    let d = Sha256::digest(text.join(",").as_bytes());
    format!(
        "k_{}",
        d.iter()
            .take(8)
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    )
}

/// Check (or with `update`, write) `formal/Formal/Templates/Consts/<Gadget>.lean`:
/// for each gadget with constant-plug calls, one `Assumptions` obligation per
/// constant vector, and for one with LC-plug calls, that its soundness assumes
/// nothing. Over the examples the file must be exactly that; over other circuits
/// it must already hold each obligation they need. The problems, if any, and the
/// names of the vectors with no committed obligation.
fn obligations(
    proven: &BTreeMap<String, Proven>,
    vectors: &BTreeMap<String, Vectors>,
    update: bool,
    examples: bool,
) -> Result<(Vec<String>, BTreeSet<String>)> {
    let mut missing = BTreeSet::new();
    let dir = crate::root().join("formal/Formal/Templates/Consts");
    let fix = "run `cargo xtask lean-export --coverage --update`";
    let mut out = Vec::new();
    let imports = std::fs::read_to_string(crate::root().join("formal/Formal.lean"))?;
    let mut want = BTreeSet::new();
    for (gadget, vs) in vectors {
        let module = crate::lean::camel(&proven[gadget].harness);
        let file = format!("{module}.lean");
        let path = dir.join(&file);
        let have = std::fs::read_to_string(&path).ok();
        if examples {
            let text = consts_file(gadget, &module, vs);
            if update {
                std::fs::create_dir_all(&dir)?;
                std::fs::write(&path, &text)?;
            } else if have.as_ref() != Some(&text) {
                out.push(format!(
                    "formal/Formal/Templates/Consts/{file} is missing or stale; {fix}"
                ));
            }
        } else {
            for k in vs.keys() {
                if !have.as_ref().is_some_and(|h| h.contains(&obligation(k))) {
                    missing.insert(if k.is_empty() {
                        "covered with LC plugs".into()
                    } else {
                        vector_name(k)
                    });
                    out.push(format!(
                        "{gadget}: formal/Formal/Templates/Consts/{file} has no obligation {}; \
                         add the circuit to the examples and {fix}",
                        if k.is_empty() {
                            "soundness_free".into()
                        } else {
                            vector_name(k)
                        }
                    ));
                }
            }
        }
        if !imports
            .lines()
            .any(|l| l.trim() == format!("import Formal.Templates.Consts.{module}"))
        {
            out.push(format!(
                "formal/Formal.lean doesn't import Formal.Templates.Consts.{module}"
            ));
        }
        want.insert(file);
    }
    if examples && let Ok(entries) = std::fs::read_dir(&dir) {
        for e in entries {
            let file = e?.file_name().to_string_lossy().into_owned();
            if !file.ends_with(".lean") || want.contains(&file) {
                continue;
            }
            if update {
                std::fs::remove_file(dir.join(&file))?;
            } else {
                out.push(format!(
                    "formal/Formal/Templates/Consts/{file}: no call needs it; {fix}"
                ));
            }
        }
    }
    Ok((out, missing))
}

/// One obligation's Lean: vector `k`'s values meet the gadget's `Assumptions`, or
/// for the empty vector, its soundness needs none (so any LC plugs keep it).
fn obligation(k: &[(u32, String)]) -> String {
    if k.is_empty() {
        return "theorem soundness_free (σ : TVar → F) (h : template.Sat σ) :\n    \
                Spec (template.ins σ) (template.outs σ) :=\n  soundness σ h\n"
            .into();
    }
    let name = vector_name(k);
    let pairs: Vec<String> = k.iter().map(|(p, v)| format!("({p}, {v})")).collect();
    format!(
        "def {name} : List (ℕ × F) := [{}]\n\n\
         theorem {name}_assumptions : Assumptions ({name}.map Prod.snd) := by\n  \
         simp [{name}, Assumptions, IsBit]\n",
        pairs.join(", ")
    )
}

/// The Lean obligations for `gadget`'s calls with constant or LC plugs.
fn consts_file(gadget: &str, module: &str, vectors: &Vectors) -> String {
    let mut s = format!(
        "-- Generated by `cargo xtask lean-export --coverage --update`: what `{gadget}`'s\n\
         -- production calls with constant or LC plugs need (formal/README.md, \"Coverage\").\n\
         -- Don't edit: `cargo xtask lean-export --coverage` fails when the examples stop\n\
         -- needing exactly these.\n\
         import Formal.{module}\n\n\
         set_option linter.style.header false\n\
         set_option linter.style.longLine false\n\n\
         namespace Xark.Templates.{module}.Consts\n\
         open Xark.Template\n"
    );
    for (k, users) in vectors {
        let users: Vec<&str> = users.iter().map(String::as_str).collect();
        let what = if k.is_empty() { "LC" } else { "Constant" };
        s += &format!(
            "\n/-- {what} plugs of calls in {}. -/\n{}",
            users.join(", "),
            obligation(k)
        );
    }
    s + &format!("\nend Xark.Templates.{module}.Consts\n")
}

/// A refused call's classification: the reason with its numbers (variable ids,
/// which move whenever the circuit before the call changes) elided.
fn refusal(why: &str) -> String {
    let why = why.split_once("can't be exported: ").map_or(why, |w| w.1);
    let mut out = String::from("refused: ");
    // A digit run starting a word becomes `#`; one inside a name stays.
    let (mut prev, mut keep) = (' ', false);
    for c in why.chars() {
        if c.is_ascii_digit() && !prev.is_ascii_digit() {
            keep = prev.is_alphanumeric() || prev == '_';
            if !keep {
                out.push('#');
            }
        }
        if !c.is_ascii_digit() || keep {
            out.push(c);
        }
        prev = c;
    }
    out
}

fn key(gadget: &str, circuit: &str, site: &str, class: &str) -> String {
    format!("{gadget} | {circuit} | {site} | {class}")
}

/// `formal/coverage-allowlist.txt`: `gadget | circuit | site | classification |
/// reason` per line, `#` comments. Each entry, keyed by its first four fields,
/// with its reason and whether a call matched it.
fn allowlist() -> Result<BTreeMap<String, (String, bool)>> {
    let path = crate::root().join(ALLOWLIST);
    let text = std::fs::read_to_string(&path).with_context(|| format!("reading {ALLOWLIST}"))?;
    let mut out = BTreeMap::new();
    for (i, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let f: Vec<&str> = line.splitn(5, " | ").map(str::trim).collect();
        match f[..] {
            [g, c, s, class, reason] if !reason.is_empty() && class != "covered" => {
                out.insert(key(g, c, s, class), (reason.to_string(), false));
            }
            _ => bail!(
                "{ALLOWLIST}:{}: want `gadget | circuit | site | classification | reason`",
                i + 1
            ),
        }
    }
    Ok(out)
}
