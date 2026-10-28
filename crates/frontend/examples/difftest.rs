//! Differential test of two builds of the same circuit (e.g. before and after a change)
//! on a corpus of real inputs recorded by the prover (`XARK_DUMP_INPUTS=<dir>` while
//! running the circuit crate's `cargo test`).
//!
//! `cargo run -p xark-frontend --release --example difftest -- <a.xbc> <b.xbc> <dump-dir>
//!     [--circuit NAME] [--mutations N] [--analyze] [--search]`
//!
//! For every recorded input: both builds must reach the same verdict, and it must be
//! the verdict the test saw. Then up to `N` mutations per input (each one leaf + 1):
//! both builds must reach the same verdict; a changed **public** leaf that both still
//! accept is reported as a note (usually the statement genuinely still holds).
//! `--analyze` also runs the under-constraint analyzer on build `b` for accepted inputs.
//! `--search` decides every input and mutation on build `b` by exhaustive witness
//! search (the adversary): exactly one witness where the honest solver accepts, none
//! where it rejects. Inconclusive searches are counted, not failed (limits:
//! `XARK_SEARCH_SECS`, `XARK_SEARCH_BUDGET`).
//! Exit status 1 on any disagreement, 2 when every search was inconclusive.

use std::collections::BTreeMap;
use std::path::Path;

use num_bigint::BigInt;
use xark_ir::VarId;
use xark_ir::primitive::{PrimitiveProgram, VarRole};
use xark_ir::solver;

struct Build {
    prog: PrimitiveProgram,
    /// leaf name → (var id, public?)
    leaves: BTreeMap<String, (VarId, bool)>,
}

fn load(path: &str) -> Build {
    let bytes = std::fs::read(path).unwrap_or_else(|e| panic!("reading {path}: {e}"));
    let cp = xark_ir::function_decode::expand_function_blob(&bytes)
        .unwrap_or_else(|e| panic!("expanding {path}: {e}"));
    let prog = cp.to_primitive();
    let leaves = prog
        .vars
        .iter()
        .filter_map(|v| match v.role {
            VarRole::PublicInput => Some((v.name.clone(), (v.id, true))),
            VarRole::PrivateInput => Some((v.name.clone(), (v.id, false))),
            _ => None,
        })
        .collect();
    Build { prog, leaves }
}

impl Build {
    fn ids(&self, inputs: &[(String, String)]) -> Result<BTreeMap<VarId, String>, String> {
        let mut m = BTreeMap::new();
        for (name, val) in inputs {
            let (id, _) = self
                .leaves
                .get(name)
                .ok_or_else(|| format!("no input leaf `{name}`"))?;
            m.insert(*id, val.clone());
        }
        if m.len() != self.leaves.len() {
            return Err(format!(
                "{} leaves given, circuit has {}",
                m.len(),
                self.leaves.len()
            ));
        }
        Ok(m)
    }

    fn accepts(&self, inputs: &[(String, String)]) -> Result<bool, String> {
        Ok(solver::solve_and_check(&self.prog, &self.ids(inputs)?).is_ok())
    }

    /// `Some(accepts)` when the witness search decides, `Err` on a forged or
    /// duplicate witness.
    fn search(&self, inputs: &[(String, String)]) -> Result<Option<bool>, String> {
        use xark_ir::witness_search::{WitnessSearch, search_witnesses_within};
        // Per-search time limit and node budget (`XARK_SEARCH_SECS`, default 20;
        // `XARK_SEARCH_BUDGET`, default 4096), for slower machines.
        let env = |k: &str, d: u64| {
            std::env::var(k)
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(d)
        };
        let limit = Some(std::time::Duration::from_secs(env("XARK_SEARCH_SECS", 20)));
        let budget = env("XARK_SEARCH_BUDGET", 1 << 12) as usize;
        match search_witnesses_within(&self.prog, &self.ids(inputs)?, budget, limit)
            .map_err(|e| e.to_string())?
        {
            WitnessSearch::Unique(_) => Ok(Some(true)),
            WitnessSearch::None => Ok(Some(false)),
            WitnessSearch::Multiple { name, .. } => {
                Err(format!("two witnesses (differ at `{name}`)"))
            }
            WitnessSearch::Inconclusive(why) => {
                // Say why once per distinct reason, so the log shows what blocks it.
                static SEEN: std::sync::Mutex<Vec<String>> = std::sync::Mutex::new(Vec::new());
                let mut seen = SEEN.lock().unwrap();
                if !seen.contains(&why) {
                    println!("note: search inconclusive: {why}");
                    seen.push(why);
                }
                Ok(None)
            }
        }
    }
}

fn bump(v: &str) -> String {
    (v.parse::<BigInt>().unwrap_or_default() + BigInt::from(1)).to_string()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let flag = |f: &str| {
        args.iter()
            .position(|a| a == f)
            .map(|i| args[i + 1].clone())
    };
    let (a, b) = (load(&args[0]), load(&args[1]));
    let dir = Path::new(&args[2]);
    let only = flag("--circuit");
    let max_mut: usize = flag("--mutations").map_or(16, |n| n.parse().unwrap());
    let analyze = args.iter().any(|x| x == "--analyze");
    let search = args.iter().any(|x| x == "--search");
    let (mut searched, mut undecided) = (0usize, 0usize);
    let mut adversary =
        |name: &str, what: &str, inputs: &[(String, String)], honest: bool| -> bool {
            if !search {
                return true;
            }
            searched += 1;
            match b.search(inputs) {
                Ok(Some(v)) if v == honest => true,
                Ok(Some(v)) => {
                    println!("FAIL {name}{what}: honest solver says {honest}, witness search {v}");
                    false
                }
                Ok(None) => {
                    undecided += 1;
                    true
                }
                Err(e) => {
                    println!("FAIL {name}{what}: {e}");
                    false
                }
            }
        };

    if a.leaves.keys().collect::<Vec<_>>() != b.leaves.keys().collect::<Vec<_>>() {
        eprintln!("FAIL: the builds' input leaves differ");
        std::process::exit(1);
    }

    let mut files: Vec<_> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("reading {}: {e}", dir.display()))
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
        .collect();
    files.sort();

    let (mut cases, mut muts, mut fails, mut notes) = (0usize, 0usize, 0usize, 0usize);
    for f in &files {
        let doc: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(f).unwrap())
            .unwrap_or_else(|e| panic!("{}: {e}", f.display()));
        if only.as_deref().is_some_and(|c| doc["circuit"] != c) {
            continue;
        }
        let inputs: Vec<(String, String)> = doc["inputs"]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| {
                (
                    p[0].as_str().unwrap().to_string(),
                    p[1].as_str().unwrap().to_string(),
                )
            })
            .collect();
        let want = doc["ok"].as_bool().unwrap();
        let name = f.file_name().unwrap().to_string_lossy();
        let (va, vb) = match (a.accepts(&inputs), b.accepts(&inputs)) {
            (Ok(x), Ok(y)) => (x, y),
            (ra, rb) => {
                // The test fed inputs the circuit doesn't take (e.g. a different
                // circuit's dump): not a verdict.
                eprintln!("skip {name}: {ra:?} / {rb:?}");
                continue;
            }
        };
        cases += 1;
        if va != want || vb != want {
            fails += 1;
            println!("FAIL {name}: test saw ok={want}, a={va}, b={vb}");
            continue;
        }
        if !adversary(&name, "", &inputs, want) {
            fails += 1;
        }
        if want && analyze {
            let assign = solver::solve(&b.prog, &b.ids(&inputs).unwrap()).unwrap();
            // Witness-only scratch (in no constraint) is causally disconnected, as
            // the test harness's `check` treats it.
            let holes: Vec<_> = solver::analyze_underconstrained(&b.prog, &assign)
                .into_iter()
                .filter(|u| u.reason != "no constraint references this variable")
                .collect();
            if !holes.is_empty() {
                fails += 1;
                println!(
                    "FAIL {name}: b under-constrained: {:?}",
                    &holes[..holes.len().min(5)]
                );
            }
        }
        // Mutations: spread over the leaves, publics first.
        let mut order: Vec<usize> = (0..inputs.len()).collect();
        order.sort_by_key(|&i| !a.leaves[&inputs[i].0].1);
        let step = (order.len() / max_mut.max(1)).max(1);
        for &i in order.iter().step_by(step).take(max_mut) {
            let public = a.leaves[&inputs[i].0].1;
            let mut m = inputs.clone();
            m[i].1 = bump(&m[i].1);
            let (ma, mb) = (a.accepts(&m).unwrap(), b.accepts(&m).unwrap());
            muts += 1;
            if !adversary(&name, &format!(" `{}`+1", inputs[i].0), &m, mb) {
                fails += 1;
            }
            if ma != mb {
                fails += 1;
                println!("FAIL {name}: `{}`+1: a={ma} b={mb}", inputs[i].0);
            } else if want && public && mb {
                // Both agree, and the statement still holds for the new public value
                // (e.g. `(2·3) mod m` for a larger modulus `m`): worth a look, not
                // a disagreement.
                notes += 1;
                println!(
                    "note {name}: public `{}`+1 still accepted by both",
                    inputs[i].0
                );
            }
        }
    }
    println!("{cases} cases, {muts} mutations, {fails} failures, {notes} notes");
    if search {
        println!("{searched} witness searches, {undecided} inconclusive");
    }
    if fails > 0 || cases == 0 {
        std::process::exit(1);
    }
    // Every search inconclusive: the adversarial half checked nothing. Exit 2 so a
    // caller can tell it apart from a pass (and from a failure).
    if search && searched > 0 && undecided == searched {
        std::process::exit(2);
    }
}
