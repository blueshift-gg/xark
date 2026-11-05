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
//!   reduced mod `r`); `Template.soundness_inst` / `completeness_inst` carry the
//!   proof over on inputs meeting the gadget's `Assumptions`;
//!   `formal/Formal/Templates/Consts/<Gadget>.lean` proves `Assumptions` of each constant
//!   vector (for add32, the constants' share of them; for `require_lt`, whose constants are
//!   all `m − 1`'s, completeness's bound on `m − 1`: see `Formal/RequireLt3x86.lean`);
//! * **covered with folded constants**: it is the proven template with constant
//!   plugs substituted and then folded as the frontend folds (a hint of constants or
//!   affine in the call's wires replaced by its value, the rows that leaves holding
//!   at every assignment dropped; a closed false row fails): `Template.foldAt`,
//!   `soundness_foldAt`, `sat_foldAt_of_sat`;
//! * **covered: reuses a covered decomposition** / **bits of producer bits**: a
//!   `to_bits` that emits nothing, returning a covered decomposition's bits of the
//!   same input at the same width, or the proven bits its input sums;
//! * **covered with LC plugs (assumptions discharged by producers …)**: LC plugs to a
//!   gadget assuming bit inputs, each a proven bit (see [`in_context`]);
//! * **covered: inside a covered / an allowlisted `G` call**: nested in a call of
//!   proven gadget `G` that is covered, or LC plugs listed in the allowlist (see
//!   [`inside_accepted`]);
//! * **refused**: the recorder can't attribute its rows exactly to the call (the
//!   reason says why);
//! * **different rows**: neither.
//!
//! Calls are grouped by (gadget, circuit, call site, classification). A refused or
//! different group fails the check unless `formal/coverage-allowlist.txt` lists it
//! with a reason; an entry no group matches fails too, so the list stays current.
//! A missing or stale `Consts/<Gadget>.lean` fails (`--update` rewrites them), and so
//! does a call of a `#[gadget]` with no harness.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use anyhow::{Context, Result, bail};
use sha2::{Digest, Sha256};
use xark_frontend::GadgetTemplate;
use xark_ir::LinearCombination;

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
    /// The Lean module of its proof (`Formal.BoolOps` for `xor`).
    proof: String,
}

/// The proof of template `module`: the one file under `formal/Formal/` importing
/// `Formal.Templates.<module>`, as its Lean module and text.
fn proof_of(module: &str) -> Result<(String, String)> {
    let dir = crate::root().join("formal/Formal");
    let import = format!("import Formal.Templates.{module}");
    let mut found = Vec::new();
    for e in std::fs::read_dir(&dir)? {
        let path = e?.path();
        if path.extension().is_some_and(|x| x == "lean") {
            let text = std::fs::read_to_string(&path)?;
            if text.lines().any(|l| l.trim_end() == import) {
                let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
                found.push((format!("Formal.{stem}"), text));
            }
        }
    }
    match <[_; 1]>::try_from(found) {
        Ok([p]) => Ok(p),
        Err(f) => bail!(
            "Formal.Templates.{module} must be imported by exactly one proof under formal/Formal/ (it is by {})",
            f.len()
        ),
    }
}

/// One recorded call of a proven gadget.
struct Call {
    gadget: String,
    /// The harness whose template it was classified against.
    harness: String,
    site: String,
    class: String,
    consts: Option<Vec<(u32, String)>>,
    /// The call's inputs and outputs over the circuit's variables, and how many rows
    /// and variables it emitted: what [`in_context`] reads.
    inputs: Vec<LinearCombination>,
    outputs: Vec<LinearCombination>,
    rows: usize,
    witnesses: u32,
    /// The innermost enclosing call of a proven gadget, as an index in the circuit's calls.
    parent: Option<usize>,
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
    // Keyed by harness: a generic gadget has one per instantiation.
    let vectors = Mutex::new(BTreeMap::<String, Vectors>::new());
    let failures = Mutex::new(Vec::new());
    let listed = allowlist()?;
    let allowed = |k: &str| listed.contains_key(k);
    crate::parallel(targets, crate::default_jobs(), |dir| {
        let name = dir.file_name().unwrap().to_string_lossy().into_owned();
        let want = examples.then(|| digests.get(name.as_str()).map(|d| d.to_string()));
        match calls(&dir, &name, want, &proven) {
            Ok(mut calls) => {
                inside_accepted(&mut calls, &name, &allowed);
                let (mut g, mut v) = (groups.lock().unwrap(), vectors.lock().unwrap());
                for c in calls {
                    if let Some(k) = c.consts {
                        let users = v.entry(c.harness.clone()).or_default().entry(k);
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
        // Per class, without the per-call detail in parentheses.
        let mut n = BTreeMap::<String, usize>::new();
        let (mut total, mut covered) = (0, 0);
        for ((g, _, _, class), m) in &groups {
            if g == gadget {
                let kind = match class.split_once(" (") {
                    Some((k, rest)) if rest.starts_with("k_") || rest.starts_with("template ") => k,
                    _ => class.as_str(),
                };
                let kind = if kind.starts_with("refused") {
                    "refused"
                } else {
                    kind
                };
                *n.entry(kind.to_string()).or_default() += m;
                total += m;
                if class.starts_with("covered") {
                    covered += m;
                }
            }
        }
        let parts: Vec<String> = n.iter().map(|(k, m)| format!("{m} {k}")).collect();
        println!(
            "{gadget}: {covered} of {total} calls covered; {}",
            parts.join("; ")
        );
    }
    println!("coverage took {:.0?}", t.elapsed());
    if !failures.is_empty() {
        bail!("coverage of proven gadgets fails:\n{}", failures.join("\n"));
    }
    Ok(())
}

/// Every gadget with a harness: its templates (one per instantiation of a generic
/// gadget), each of which must be the one its committed Lean file (and so its proof)
/// is about.
fn proven() -> Result<BTreeMap<String, Vec<Proven>>> {
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
        // Its proof: the file importing the template (`BoolOps.lean` proves both
        // `xor` and `or`), in the template's namespace there.
        let module = crate::lean::camel(&harness);
        let (proof, text) = proof_of(&module)?;
        let body = text
            .split_once(&format!("namespace Xark.Templates.{module}\n"))
            .and_then(|(_, b)| b.split_once(&format!("end Xark.Templates.{module}\n")))
            .map_or("", |(b, _)| b);
        // A soundness theorem with no hypothesis but the rows needs nothing of the
        // inputs, whatever combinations a caller passes.
        let trivial = body
            .lines()
            .any(|l| l.trim_end() == "theorem soundness (σ : TVar → F) (h : template.Sat σ) :");
        let p = Proven {
            harness,
            hash,
            template,
            trivial,
            proof,
        };
        out.entry(p.template.name.clone())
            .or_insert_with(Vec::new)
            .push(p);
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
    proven: &BTreeMap<String, Vec<Proven>>,
) -> Result<Vec<Call>> {
    let target = crate::target_dir().join("coverage").join(name);
    let lower = |markers: bool| -> Result<xark_frontend::LowerOutput> {
        let opts = xark_frontend::BuildOptions {
            gadget_markers: markers,
            ..Default::default()
        };
        let sub = if markers { "marked" } else { "plain" };
        let wasm = xark_frontend::build_crate_with(dir, &target.join(sub), &opts)
            .map_err(|e| anyhow::anyhow!("{e}"))?
            .wasm;
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
    // Against each instantiation's template, keeping the closest match.
    let rank = |class: &str| match class {
        "covered" => 0,
        c if c.starts_with("covered") => 1,
        c if c.starts_with("LC plugs") => 2,
        _ => 3,
    };
    let mut calls: Vec<Call> = Vec::new();
    // Each recorded call's index in `calls` (proven gadgets only), and its parent.
    let mut index: Vec<Option<usize>> = Vec::new();
    let parents: Vec<Option<usize>> = out.gadgets.iter().map(|c| c.parent).collect();
    let mut unproven = BTreeSet::new();
    for c in out.gadgets {
        let Some(ps) = proven.get(&c.name) else {
            // Every recorded call is of a `#[gadget]`; this one has no harness, so no proof.
            unproven.insert(format!("`{}` at {}", c.name, c.site.replace(&root, "")));
            index.push(None);
            continue;
        };
        index.push(Some(calls.len()));
        let (p, (class, consts)) = ps
            .iter()
            .map(|p| (p, classify(c.template.clone(), p)))
            .min_by_key(|(_, (class, _))| rank(class))
            .expect("a gadget has a harness");
        calls.push(Call {
            harness: p.harness.clone(),
            gadget: c.name,
            site: c.site.replace(&root, ""),
            class,
            consts,
            inputs: c.inputs,
            outputs: c.outputs,
            rows: c.rows,
            witnesses: c.witnesses,
            parent: None,
        });
    }
    if !unproven.is_empty() {
        let calls: Vec<String> = unproven.into_iter().collect();
        bail!(
            "a #[gadget] with no harness under formal/templates/: {}",
            calls.join(", ")
        );
    }
    in_context(&mut calls, &out.gadget_rows);
    // Each call's innermost enclosing call of a proven gadget, as an index in `calls`.
    for (i, me) in index.iter().enumerate() {
        let Some(me) = *me else { continue };
        let mut up = parents[i];
        while let Some(a) = up {
            if let Some(k) = index[a] {
                calls[me].parent = Some(k);
                break;
            }
            up = parents[a];
        }
    }
    Ok(calls)
}

/// A call nested in an accepted call of a proven gadget is covered: its rows are part of
/// that call's, which the gadget's proof is about (`soundness_inst` when the enclosing
/// call has LC plugs, whose `Assumptions` its allowlist entry names the enforcer of).
/// Accepted: covered, or allowlisted as LC plugs. Parents come first, so an ancestor's
/// class is final when its descendants are visited.
fn inside_accepted(calls: &mut [Call], circuit: &str, allowed: &dyn Fn(&str) -> bool) {
    for i in 0..calls.len() {
        let mut up = calls[i].parent;
        while let Some(k) = up {
            let (gadget, class) = (&calls[k].gadget, &calls[k].class);
            let how = if class.starts_with("covered") {
                Some("a covered")
            } else if class.starts_with("LC plugs")
                && allowed(&key(gadget, circuit, &calls[k].site, class))
            {
                Some("an allowlisted")
            } else {
                None
            };
            if let Some(how) = how {
                calls[i].class = format!("covered: inside {how} `{gadget}` call");
                // Its proof is the parent's: no obligation of its own.
                calls[i].consts = None;
                break;
            }
            up = calls[k].parent;
        }
    }
}

/// The gadgets whose `Spec` makes every output a bit (on inputs meeting their
/// `Assumptions`): `ToBits.spec_isBit`, `ToBitsCanonical.spec_isBit`,
/// `Reduce.spec_isBit`, and each bitwise `BIT_ASSUMING` gadget's `outs_isBit`.
/// Gadgets whose `Assumptions` read only the first half of their inputs (`x`), so a call
/// whose constants are all in the second half (`m₋₁`'s limbs) needs no obligation.
const UNASSUMED_TAIL: [&str; 1] = ["xark_bignum::require_lt"];

const BIT_PRODUCERS: [&str; 10] = [
    "xark::lang::to_bits",
    "xark::lang::to_bits_canonical",
    "xark_bits::reduce",
    "xark::lang::xor",
    "xark::lang::or",
    "xark_bits::add32",
    "xark_bits::xor3",
    "xark_bits::maj3",
    "xark_bits::chi",
    "xark_bits::ch",
];

/// The producers whose outputs are bits whatever their inputs (their `soundness`
/// assumes nothing): `to_bits`, `to_bits_canonical` and `reduce`.
const FREE_PRODUCERS: [&str; 3] = [
    "xark::lang::to_bits",
    "xark::lang::to_bits_canonical",
    "xark_bits::reduce",
];

/// The gadgets whose `Assumptions` are exactly that their first `n` inputs are bits
/// (`usize::MAX`: every input), so proven bit inputs discharge them (`Xor`, `Or`,
/// `Add32`'s `Assumptions`, `Xark.HashOps.Assumptions` for `xor3`, `maj3`, `chi`, `ch`,
/// `ScalarMul.Assumptions`, the 128 scalar bits before `P`, and `OneHot8.Assumptions`).
const BIT_ASSUMING: [(&str, usize); 9] = [
    ("xark::lang::xor", usize::MAX),
    ("xark::lang::or", usize::MAX),
    ("xark_bits::add32", usize::MAX),
    ("xark_bits::xor3", usize::MAX),
    ("xark_bits::maj3", usize::MAX),
    ("xark_bits::chi", usize::MAX),
    ("xark_bits::ch", usize::MAX),
    ("xark_grumpkin::scalar_mul", 128),
    ("xark_bignum::one_hot8", usize::MAX),
];

/// A linear combination's identity mod `r` (for matching wires across calls).
fn wire(l: &LinearCombination) -> String {
    let l = xark_frontend::canonical_lc(l);
    let mut s = l.constant.decimal();
    for t in &l.terms {
        let _ = write!(s, "+{}*v{}", t.coeff.decimal(), t.var);
    }
    s
}

/// The classes that need the circuit around a call, over its own variables: a
/// `to_bits` that emits nothing, reusing a covered decomposition of the same input
/// at the same width (the frontend's memo is keyed by both) or reading the bits of
/// a sum of proven bits (`ToBits.spec_of_bits`); and LC plugs whose `Assumptions`
/// (`BIT_ASSUMING`: its first `n` inputs are bits) hold because each of those inputs is
/// a proven bit. A wire is a proven bit when it is a 0/1 constant, an output of a
/// covered `BIT_PRODUCERS` call whose own inputs are proven bits (`FREE_PRODUCERS` need
/// none), one minus a proven bit, or
/// pinned by a row of the circuit (`rows`, from `LowerOutput::gadget_rows`):
/// `x · x = x`, `x · (x − 1) = 0`, or `a · b = v` with `a` and `b` proven bits.
/// Repeated until nothing changes, since a covered call's outputs can discharge
/// another's inputs.
fn in_context(calls: &mut [Call], rows: &[[LinearCombination; 3]]) {
    let covered = |c: &Call| c.class.starts_with("covered");
    let to_bits = |c: &Call| c.gadget == "xark::lang::to_bits" && c.inputs.len() == 1;
    let key = |c: &Call| format!("{}/{}", wire(&c.inputs[0]), c.outputs.len());
    // Outputs of producers, and wires the rows pin.
    let (mut bits, mut pinned) = (HashSet::<String>::new(), HashSet::<String>::new());
    let mut decomps: HashMap<String, Vec<String>> = HashMap::new();
    let mut learned = vec![false; calls.len()];
    let one = LinearCombination::one();
    // A 0/1 constant, or a wire (or one minus it) in `set`.
    let in_set = |set: &HashSet<String>, l: &LinearCombination| {
        let l = xark_frontend::canonical_lc(l);
        (l.is_constant() && (l.constant.is_zero() || l.constant.is_one()))
            || set.contains(&wire(&l))
            || set.contains(&wire(&(one.clone() - l)))
    };
    let is_bit = |bits: &HashSet<String>, pinned: &HashSet<String>, l: &LinearCombination| {
        in_set(bits, l) || in_set(pinned, l)
    };
    loop {
        let mut changed = false;
        for [a, b, c] in rows {
            let pins = if a == b && a == c {
                Some(a)
            } else if c.is_zero() {
                let less = |x: &LinearCombination| wire(&(x.clone() - one.clone()));
                if less(a) == wire(b) {
                    Some(a)
                } else if less(b) == wire(a) {
                    Some(b)
                } else {
                    None
                }
            } else if is_bit(&bits, &pinned, a) && is_bit(&bits, &pinned, b) {
                Some(c)
            } else {
                None
            };
            if let Some(x) = pins {
                changed |= pinned.insert(wire(x));
            }
        }
        for (i, c) in calls.iter_mut().enumerate() {
            if !covered(c) {
                let silent = c.rows == 0 && c.witnesses == 0 && !c.outputs.is_empty();
                let class = if to_bits(c) && silent {
                    let outs: Vec<String> = c.outputs.iter().map(wire).collect();
                    let mut sum = LinearCombination::zero();
                    let mut pow = xark_ir::FieldConst::one();
                    for o in &c.outputs {
                        sum = sum + o.clone().scale(&pow);
                        pow = pow.mul(&xark_ir::FieldConst::from_i64(2));
                    }
                    if decomps.get(&key(c)) == Some(&outs) {
                        Some("covered: reuses a covered decomposition")
                    } else if c.outputs.len() <= 253
                        && wire(&sum) == wire(&c.inputs[0])
                        && c.outputs.iter().all(|o| is_bit(&bits, &pinned, o))
                    {
                        Some("covered: bits of producer bits")
                    } else {
                        None
                    }
                } else if let Some(&(_, n)) = BIT_ASSUMING.iter().find(|(g, _)| *g == c.gadget)
                    && c.class
                        .starts_with("LC plugs: the caller must enforce Assumptions")
                    && c.inputs.iter().take(n).all(|i| is_bit(&bits, &pinned, i))
                {
                    if c.inputs.iter().take(n).all(|i| in_set(&bits, i)) {
                        Some("covered with LC plugs (assumptions discharged by producers)")
                    } else {
                        Some(
                            "covered with LC plugs (assumptions discharged by producers and \
                             booleanity rows)",
                        )
                    }
                } else {
                    None
                };
                if let Some(class) = class {
                    c.class = class.into();
                    c.consts = None;
                    changed = true;
                }
            }
            if covered(c) && !learned[i] {
                if to_bits(c) {
                    decomps
                        .entry(key(c))
                        .or_insert_with(|| c.outputs.iter().map(wire).collect());
                }
                if BIT_PRODUCERS.contains(&c.gadget.as_str())
                    && (FREE_PRODUCERS.contains(&c.gadget.as_str())
                        || c.inputs.iter().all(|i| is_bit(&bits, &pinned, i)))
                {
                    bits.extend(c.outputs.iter().map(wire));
                    learned[i] = true;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
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
            None => match p.template.folding_of(&t) {
                None => (format!("different rows (template {})", &h[..23]), None),
                Some(Err(why)) => (format!("folded constants: {why}"), None),
                Some(Ok(sub)) => {
                    let k: Vec<(u32, String)> = sub
                        .iter()
                        .filter(|(_, e)| e.is_constant())
                        .map(|(p, e)| (*p, e.constant.decimal()))
                        .collect();
                    let var = |e: &LinearCombination| match &e.terms[..] {
                        [u] if e.constant.is_zero() && u.coeff.is_one() => Some(u.var),
                        _ => None,
                    };
                    let vars: Vec<u32> = sub.iter().filter_map(|(_, e)| var(e)).collect();
                    let distinct = vars.iter().collect::<BTreeSet<_>>().len() == vars.len();
                    if p.trivial {
                        (
                            "covered with folded constants (no assumptions)".into(),
                            Some(Vec::new()),
                        )
                    } else if distinct && vars.len() + k.len() == sub.len() {
                        if k.is_empty() {
                            ("covered with folded constants".into(), None)
                        } else {
                            let class =
                                format!("covered with folded constants ({})", vector_name(&k));
                            (class, Some(k))
                        }
                    } else {
                        (
                            "LC plugs: the caller must enforce Assumptions (after folding constants)"
                                .into(),
                            None,
                        )
                    }
                }
            },
            Some(sub) => {
                let var = |e: &LinearCombination| match &e.terms[..] {
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
                if !k.is_empty() && p.trivial {
                    // The empty vector: the obligation that soundness assumes nothing.
                    (
                        "covered with constant plugs (no assumptions)".into(),
                        Some(Vec::new()),
                    )
                } else if !k.is_empty()
                    && distinct
                    && vars.len() + k.len() == sub.len()
                    && UNASSUMED_TAIL.contains(&p.template.name.as_str())
                    && k.iter()
                        .all(|(i, _)| *i as usize >= p.template.inputs.len() / 2)
                {
                    // `soundness_consts` needs nothing of these constants.
                    (
                        "covered with constant plugs (none it assumes anything of)".into(),
                        None,
                    )
                } else if !k.is_empty() && distinct && vars.len() + k.len() == sub.len() {
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
    proven: &BTreeMap<String, Vec<Proven>>,
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
    for (harness, vs) in vectors {
        let p = proven
            .values()
            .flatten()
            .find(|p| &p.harness == harness)
            .context("a vector of no harness")?;
        let (gadget, proof) = (&p.template.name, &p.proof);
        let module = crate::lean::camel(harness);
        let file = format!("{module}.lean");
        let path = dir.join(&file);
        let have = std::fs::read_to_string(&path).ok();
        if examples {
            let text = consts_file(gadget, &module, proof, vs);
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
fn consts_file(gadget: &str, module: &str, proof: &str, vectors: &Vectors) -> String {
    let mut s = format!(
        "-- Generated by `cargo xtask lean-export --coverage --update`: what `{gadget}`'s\n\
         -- production calls with constant or LC plugs need (formal/README.md, \"Coverage\").\n\
         -- Don't edit: `cargo xtask lean-export --coverage` fails when the examples stop\n\
         -- needing exactly these.\n\
         import {proof}\n\n\
         set_option linter.style.header false\n\
         set_option linter.style.longLine false\n\
         -- One `simp` serves every gadget: `IsBit` is unused where `Assumptions` has no bit.\n\
         set_option linter.unusedSimpArgs false\n\n\
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

#[cfg(test)]
mod tests {
    use super::*;

    fn var(v: u32) -> LinearCombination {
        LinearCombination::var(v)
    }

    fn to_bits(class: &str, input: u32, outputs: &[u32], rows: usize) -> Call {
        Call {
            gadget: "xark::lang::to_bits".into(),
            harness: "to_bits".into(),
            site: String::new(),
            class: class.into(),
            consts: None,
            inputs: vec![var(input)],
            outputs: outputs.iter().map(|&v| var(v)).collect(),
            rows,
            witnesses: if rows == 0 { 0 } else { 1 },
            parent: None,
        }
    }

    /// A memo hit returns the bits of the same input at the same width. A call that
    /// emits nothing and returns a covered decomposition's bits as another input's
    /// (which the frontend's memo, keyed by input and width, never does) proves
    /// nothing about that input, and isn't covered.
    #[test]
    fn a_silent_to_bits_of_another_input_does_not_reuse_a_decomposition() {
        let mut calls = [
            to_bits("covered", 0, &[1, 2], 2),
            to_bits("refused: it reads variable #", 0, &[1, 2], 0),
            to_bits("refused: it reads variable #", 5, &[1, 2], 0),
            to_bits("refused: it reads variable #", 0, &[1], 0),
        ];
        in_context(&mut calls, &[]);
        let classes: Vec<&str> = calls.iter().map(|c| c.class.as_str()).collect();
        assert_eq!(
            classes,
            [
                "covered",
                "covered: reuses a covered decomposition",
                "refused: it reads variable #",
                "refused: it reads variable #",
            ]
        );
    }
}
