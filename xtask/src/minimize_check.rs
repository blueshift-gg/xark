//! `cargo xtask minimize-check`: every minimizer run on every example's keyed path —
//! each template body and the top stream (`expand_function_blob_reduced`), then the
//! global pass (`xark_ir::minimize`) — certified by the Lean checker
//! `formal/MinimizeCheck.lean`, whose acceptance `formal/Formal/Minimize/Sound.lean`
//! proves means: the minimized rows have exactly the original rows' solutions, with
//! every eliminated variable `Internal` and recomputed from the survivors.
//!
//! The certified rows are the keyed rows: their keyed-rows digest must be the example's
//! line in tests/stable-digests.txt.
//!
//! # Certificate stream
//!
//! `u` is unsigned LEB128, `f` a field element as zigzag LEB128 of its representative
//! in `(-p/2, p/2]`.
//!
//! ```text
//! b"XMC1" ‖ (0x01 ‖ problem)* ‖ 0x00
//! problem = u p ‖ u n ‖ n × (u id ‖ u visibility ‖ u (eliminating step + 1, or 0))
//!                                              input variables, ascending id
//!           u n ‖ n × (u id ‖ u visibility)    output variables, ascending id
//!           u n ‖ n × (u var ‖ lc ‖ orig)       steps: var := lc, and its defining row
//!           u n ‖ n × (orig ‖ fate)             the other original rows, in order
//! fate    = 0x00 ‖ row   kept, as this minimized row (the next one, in order)
//!         | 0x01         dropped as identically true
//! orig    = row ‖ 3 × (u n ‖ n × (u step ‖ f m))   per form a, b, c: the substitutions
//! row     = lc a ‖ lc b ‖ lc c
//! lc      = f constant ‖ u n ‖ n × (f coefficient ‖ u var)
//! ```

use std::collections::BTreeMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail};
use num_bigint::{BigInt, BigUint};
use xark_ir::function_decode::Certificate;
use xark_ir::minimize::{MAX_FILL, minimize_traced};
use xark_ir::{FieldConst, LinearCombination, R1csConstraint, Visibility};

#[derive(clap::Args)]
pub struct Args {
    /// Only these examples (default: every circuit).
    names: Vec<String>,
    /// Circuits built at once.
    #[arg(long, default_value_t = crate::default_jobs())]
    jobs: usize,
}

pub fn run(args: Args) -> Result<()> {
    let checker = build_checker()?;
    let names = if args.names.is_empty() {
        crate::circuits()?
    } else {
        args.names
    };
    let target = crate::target_dir().join("minimize-check");
    let results = Mutex::new(BTreeMap::new());
    crate::parallel(names, args.jobs, |name| {
        let r = certify(&checker, &name, &target.join(&name));
        results.lock().unwrap().insert(name, r);
    });
    let mut failed = Vec::new();
    for (name, r) in results.into_inner().unwrap() {
        match r {
            Ok(t) => println!(
                "{name}: {} certificates, {} steps; minimize {:.2}s, Lean check {:.2}s",
                t.certificates,
                t.steps,
                t.minimize.as_secs_f64(),
                t.check.as_secs_f64()
            ),
            Err(e) => {
                println!("{name}: FAILED: {e:#}");
                failed.push(name);
            }
        }
    }
    if !failed.is_empty() {
        bail!("minimizer certificates refused: {}", failed.join(", "));
    }
    Ok(())
}

/// `lake build minimize_check` in formal/: the checker's path.
fn build_checker() -> Result<PathBuf> {
    let formal = crate::root().join("formal");
    crate::run(
        Command::new("lake")
            .args(["build", "--wfail", "minimize_check"])
            .current_dir(&formal),
    )?;
    Ok(formal.join(".lake/build/bin/minimize_check"))
}

struct Timing {
    certificates: usize,
    steps: usize,
    minimize: Duration,
    check: Duration,
}

/// Build the example, certify both minimizer passes, and tie them to its pinned digest.
fn certify(checker: &Path, name: &str, target: &Path) -> Result<Timing> {
    let xbc = crate::digests::build(&crate::root().join("examples").join(name), target)?;
    let t = Instant::now();
    let (reduced, mut certs) =
        xark_ir::function_decode::expand_function_blob_reduced_certified(&xbc)
            .map_err(|e| anyhow::anyhow!(e))?;
    let reduced = reduced.into_r1cs();
    let (minimized, trace) = minimize_traced(&reduced, MAX_FILL);
    let minimize = t.elapsed();
    let digest = crate::digests::forms_digest(&reduced, &minimized)?;
    let pinned = std::fs::read_to_string(crate::root().join("tests/stable-digests.txt"))?;
    if !pinned.lines().any(|l| l == format!("{name} {digest}")) {
        bail!("the certified rows aren't the pinned keyed rows (digest {digest})");
    }
    certs.push(Certificate {
        input: reduced,
        output: minimized,
        trace,
    });
    let t = Instant::now();
    check(checker, &certs)?;
    Ok(Timing {
        certificates: certs.len(),
        steps: certs.iter().map(|c| c.trace.steps.len()).sum(),
        minimize,
        check: t.elapsed(),
    })
}

/// Stream `certs` to the Lean checker; `Err` unless it accepts every one.
fn check(checker: &Path, certs: &[Certificate]) -> Result<()> {
    let mut child = Command::new(checker)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| format!("running {}", checker.display()))?;
    let mut stdin = std::io::BufWriter::new(child.stdin.take().unwrap());
    let written = (|| -> Result<()> {
        stdin.write_all(b"XMC1")?;
        for c in certs {
            stdin.write_all(&[1])?;
            write_problem(&mut stdin, c)?;
        }
        stdin.write_all(&[0])?;
        Ok(stdin.flush()?)
    })();
    drop(stdin);
    let out = child.wait_with_output()?;
    written?;
    if !out.status.success() {
        bail!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    Ok(())
}

fn write_problem(w: &mut dyn Write, c: &Certificate) -> Result<()> {
    let decimal = c
        .input
        .field
        .modulus_decimal
        .as_deref()
        .context("no field modulus")?;
    let p: BigUint = decimal.parse()?;
    let e = Enc {
        p: BigInt::from(p.clone()),
    };
    let tr = &c.trace;
    let mut elim = BTreeMap::new();
    for (k, s) in tr.steps.iter().enumerate() {
        elim.insert(s.var, k as u64 + 1);
    }
    let mut subs: BTreeMap<usize, [Vec<(u32, &FieldConst)>; 3]> = BTreeMap::new();
    for (row, form, step, m) in &tr.substitutions {
        subs.entry(*row).or_default()[*form as usize].push((*step, m));
    }
    let orig = |w: &mut dyn Write, i: usize| -> Result<()> {
        e.row(w, &c.input.constraints[i])?;
        let none = Default::default();
        for form in subs.get(&i).unwrap_or(&none) {
            uvar(w, form.len() as u64)?;
            for &(step, m) in form {
                uvar(w, step as u64)?;
                e.fe(w, m)?;
            }
        }
        Ok(())
    };

    let mut buf = Vec::new();
    e.big(&mut buf, &p)?;
    let mut vars: Vec<_> = c.input.variables.iter().collect();
    vars.sort_by_key(|v| v.id);
    uvar(&mut buf, vars.len() as u64)?;
    for v in vars {
        uvar(&mut buf, v.id as u64)?;
        uvar(&mut buf, vis(&v.visibility))?;
        uvar(&mut buf, elim.get(&v.id).copied().unwrap_or(0))?;
    }
    let mut out_vars: Vec<_> = c.output.variables.iter().collect();
    out_vars.sort_by_key(|v| v.id);
    uvar(&mut buf, out_vars.len() as u64)?;
    for v in out_vars {
        uvar(&mut buf, v.id as u64)?;
        uvar(&mut buf, vis(&v.visibility))?;
    }
    uvar(&mut buf, tr.steps.len() as u64)?;
    for s in &tr.steps {
        uvar(&mut buf, s.var as u64)?;
        e.lc(&mut buf, &s.lc)?;
        orig(&mut buf, s.row)?;
    }
    w.write_all(&buf)?;

    let defining: std::collections::BTreeSet<usize> = tr.steps.iter().map(|s| s.row).collect();
    let dropped: std::collections::BTreeSet<usize> = tr.dropped.iter().copied().collect();
    let n = c.input.constraints.len();
    uvar(w, (n - defining.len()) as u64)?;
    let mut kept = c.output.constraints.iter();
    for i in (0..n).filter(|i| !defining.contains(i)) {
        orig(w, i)?;
        if dropped.contains(&i) {
            w.write_all(&[1])?;
        } else {
            let m = kept
                .next()
                .context("fewer minimized rows than the trace keeps")?;
            w.write_all(&[0])?;
            e.row(w, m)?;
        }
    }
    if kept.next().is_some() {
        bail!("more minimized rows than the trace keeps");
    }
    Ok(())
}

fn vis(v: &Visibility) -> u64 {
    match v {
        Visibility::Public => 0,
        Visibility::Private => 1,
        Visibility::Internal => 2,
    }
}

fn uvar(w: &mut dyn Write, mut x: u64) -> Result<()> {
    loop {
        let b = (x & 0x7f) as u8;
        x >>= 7;
        if x == 0 {
            w.write_all(&[b])?;
            return Ok(());
        }
        w.write_all(&[b | 0x80])?;
    }
}

/// Field-element encoding modulo `p`.
struct Enc {
    p: BigInt,
}

impl Enc {
    /// LEB128 of a big natural.
    fn big(&self, w: &mut dyn Write, x: &BigUint) -> Result<()> {
        let mut x = x.clone();
        loop {
            let b = (x.iter_u64_digits().next().unwrap_or(0) & 0x7f) as u8;
            x >>= 7;
            if x == BigUint::ZERO {
                w.write_all(&[b])?;
                return Ok(());
            }
            w.write_all(&[b | 0x80])?;
        }
    }

    fn fe(&self, w: &mut dyn Write, k: &FieldConst) -> Result<()> {
        if let Some(i) = k.as_i64().filter(|i| i.unsigned_abs() < 1 << 62) {
            return uvar(
                w,
                if i >= 0 {
                    2 * i as u64
                } else {
                    2 * i.unsigned_abs() - 1
                },
            );
        }
        let x = ((k.big() % &self.p) + &self.p) % &self.p;
        let z: BigInt = if 2 * &x <= self.p {
            2 * x
        } else {
            2 * (&self.p - x) - 1
        };
        self.big(w, z.magnitude())
    }

    fn lc(&self, w: &mut dyn Write, lc: &LinearCombination) -> Result<()> {
        self.fe(w, &lc.constant)?;
        uvar(w, lc.terms.len() as u64)?;
        for t in &lc.terms {
            self.fe(w, &t.coeff)?;
            uvar(w, t.var as u64)?;
        }
        Ok(())
    }

    fn row(&self, w: &mut dyn Write, r: &R1csConstraint) -> Result<()> {
        for side in [&r.a, &r.b, &r.c] {
            self.lc(w, side)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The optimizer bug class of circom#425 (bug checklist 12): a minimizer mutated to
    /// drop a row, to substitute wrongly, or to eliminate a public input is refused by
    /// the Lean checker, on the global pass over a real example's keyed rows.
    #[test]
    #[ignore = "needs lake and formal/'s packages; lean.yml runs it"]
    fn the_checker_refuses_a_mutated_minimizer() {
        let checker = build_checker().unwrap();
        let name = "sha256";
        let xbc = crate::digests::build(
            &crate::root().join("examples").join(name),
            &crate::target_dir().join("minimize-check-test").join(name),
        )
        .unwrap();
        let reduced = xark_ir::function_decode::expand_function_blob_reduced(&xbc)
            .unwrap()
            .into_r1cs();
        let certified = || {
            let (output, trace) = minimize_traced(&reduced, MAX_FILL);
            Certificate {
                input: reduced.clone(),
                output,
                trace,
            }
        };
        let honest = certified();
        assert!(!honest.trace.steps.is_empty(), "{name} eliminates nothing");
        check(&checker, &[certified()]).unwrap();

        // The first kept row a substitution went into, and its index among the kept.
        let defining: Vec<usize> = honest.trace.steps.iter().map(|s| s.row).collect();
        let fate = |i: &usize| !defining.contains(i) && !honest.trace.dropped.contains(i);
        let row = honest
            .trace
            .substitutions
            .iter()
            .map(|s| s.0)
            .find(fate)
            .expect("a kept row with a substitution");
        let out = (0..row).filter(fate).count();
        let plus_one = |k: &mut FieldConst| *k = FieldConst::from_bigint(k.big() + 1);

        let mut drops_row = certified();
        drops_row.trace.dropped.push(row);
        drops_row.output.constraints.remove(out);

        let mut wrong_row = certified();
        plus_one(&mut wrong_row.output.constraints[out].c.constant);

        let mut wrong_step = certified();
        plus_one(&mut wrong_step.trace.steps[0].lc.constant);

        let mut eliminates_public = certified();
        let v = eliminates_public.trace.steps[0].var;
        let var = eliminates_public
            .input
            .variables
            .iter_mut()
            .find(|x| x.id == v);
        var.unwrap().visibility = Visibility::Public;

        for (what, mutant) in [
            ("drops a row", drops_row),
            ("substitutes wrongly into a kept row", wrong_row),
            ("eliminates by a wrong form", wrong_step),
            ("eliminates a public input", eliminates_public),
        ] {
            let err = check(&checker, &[mutant]).expect_err(what);
            assert!(
                err.to_string().contains("refused 1 of 1"),
                "{what}: {err:#}"
            );
        }
    }
}
