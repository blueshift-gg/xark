//! Human-readable diagnostics for a witness that fails to satisfy the circuit.
//!
//! Turns a [`SolveError`] into an actionable explanation: the source statement
//! the failing constraint came from (from `sources.json`, which every build
//! writes), then the constraint itself. Shared by the `xark_prover` test harness
//! ([`Circuit::check`](../../xark_prover/struct.Circuit.html)) and the CLI
//! soundness gate (`xark prove` / `xark check --inputs`), so both worlds surface
//! the *same* explanation from one place.

use crate::Visibility;
use crate::linear_combination::LinearCombination;
use crate::r1cs::R1csProgram;
use crate::solver::SolveError;
use crate::sources::SourceMap;

/// ANSI palette for the diagnostic, matching the `xark` CLI. Empty strings when
/// stderr is not a terminal or `NO_COLOR` is set, so piped output / CI logs stay
/// plain. `hi` is red **and underlined** — it marks the implicated input.
struct Palette {
    err: &'static str,
    hi: &'static str,
    dim: &'static str,
    reset: &'static str,
}

fn palette() -> Palette {
    use std::io::IsTerminal;
    let on = std::env::var_os("NO_COLOR").is_none()
        && (std::env::var_os("CLICOLOR_FORCE").is_some() || std::io::stderr().is_terminal());
    if on {
        Palette {
            err: "\x1b[1;38;2;255;85;85m",  // red, bold — the failure
            hi: "\x1b[1;4;38;2;255;85;85m", // red, bold, underlined — the input
            dim: "\x1b[2m",                 // faint — locations / structure labels
            reset: "\x1b[0m",
        }
    } else {
        Palette {
            err: "",
            hi: "",
            dim: "",
            reset: "",
        }
    }
}

/// Render one linear combination compactly: *input* terms (public/private) are
/// shown by name and highlighted; internal wire terms collapse to `⟨N wires⟩` so
/// a large constraint stays one readable line showing its shape.
fn render_lc(lc: &LinearCombination, r1cs: &R1csProgram, p: &Palette) -> String {
    let mut parts: Vec<String> = Vec::new();
    let mut wires = 0usize;
    for t in &lc.terms {
        match r1cs
            .variables
            .iter()
            .find(|v| v.id == t.var)
            .filter(|v| !matches!(v.visibility, Visibility::Internal))
        {
            Some(v) => {
                let name = format!("{}{}{}", p.hi, v.name, p.reset);
                parts.push(if t.coeff.is_one() {
                    name
                } else {
                    format!("{}·{name}", t.coeff.decimal())
                });
            }
            None => wires += 1,
        }
    }
    if wires > 0 {
        parts.push(format!(
            "⟨{wires} wire{}⟩",
            if wires == 1 { "" } else { "s" }
        ));
    }
    if !lc.constant.is_zero() {
        parts.push(lc.constant.decimal());
    }
    if parts.is_empty() {
        "0".to_string()
    } else {
        parts.join(" + ")
    }
}

/// Render a solve/check failure into a colored, multi-line explanation.
///
/// For a constraint violation ([`SolveError::ConstraintFailed`]) this shows the
/// statement it came from (`file:line:col`, the source line, the function it
/// failed in) when `sources` is given, then the constraint's `a·b = c` form (with
/// the implicated input underlined) and its debug note. Constraint ids are
/// index-aligned across the primitive IR, `r1cs.json` and `sources.json`. Any
/// other error renders via `Display`.
pub fn describe_unsatisfied(
    err: &SolveError,
    r1cs: &R1csProgram,
    sources: Option<&SourceMap>,
) -> String {
    let p = palette();
    let SolveError::ConstraintFailed(i) = err else {
        return format!("{}witness could not be solved:{} {err}", p.err, p.reset);
    };
    let i = *i;
    let site = sources.and_then(|s| s.at(i));

    let mut msg = format!("{}witness does not satisfy the circuit{}", p.err, p.reset);
    // The statement first: it's what the reader wrote.
    if let Some(s) = site {
        msg.push_str(&format!(
            "\n\n  {}{}{}  {}",
            p.dim,
            s.location(),
            p.reset,
            s.text
        ));
        // The functions it went through, when the line alone doesn't say.
        if s.chain.last().is_some_and(|f| !s.text.contains(f.as_str())) {
            msg.push_str(&format!(
                "\n  {}in{} {}",
                p.dim,
                p.reset,
                s.chain.join(" → ")
            ));
        }
    }
    msg.push_str(&format!("\n\n  constraint #{i} does not hold"));

    let failing = r1cs.constraints.iter().find(|c| c.id as usize == i);

    // The constraint's `a · b = c` shape, with the input(s) highlighted in place.
    if let Some(c) = failing {
        msg.push_str(&format!(
            "\n  {}form{}  ({}) · ({}) = {}",
            p.dim,
            p.reset,
            render_lc(&c.a, r1cs, &p),
            render_lc(&c.b, r1cs, &p),
            render_lc(&c.c, r1cs, &p),
        ));
    }

    // The `a·b = c` debug note (kept in `r1cs.json`) names the operation.
    if let Some(note) = failing
        .and_then(|c| c.debug.as_ref())
        .and_then(|d| d.note.as_deref())
    {
        msg.push_str(&format!("\n  {}note{}  {note}", p.dim, p.reset));
    }

    // Call out each *input* the constraint touches, so a wrong input value points
    // at itself instead of leaving the reader with an opaque index. A constraint
    // over only internal wires (most of them) adds no line here.
    if let Some(c) = failing {
        let mut seen = std::collections::BTreeSet::new();
        for lc in [&c.a, &c.b, &c.c] {
            for t in &lc.terms {
                if !seen.insert(t.var) {
                    continue;
                }
                if let Some(v) = r1cs.variables.iter().find(|v| v.id == t.var) {
                    let vis = match v.visibility {
                        Visibility::Public => "public input",
                        Visibility::Private => "private input",
                        Visibility::Internal => continue,
                    };
                    msg.push_str(&format!(
                        "\n\n  → check {}{}{}, a {vis}",
                        p.hi, v.name, p.reset
                    ));
                }
            }
        }
    }

    if sources.is_none() {
        msg.push_str(&format!(
            "\n\n  {}(rebuild with `xark build` for the source line){}",
            p.dim, p.reset
        ));
    }
    msg
}
