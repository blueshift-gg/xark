//! Human-readable diagnostics for a witness that fails to satisfy the circuit.
//!
//! Turns a [`SolveError`] into an actionable explanation naming the failing
//! constraint and — when `profile.json` attribution is available — the source
//! line and function chain it came from. Shared by the `xark_prover` test harness
//! ([`Circuit::check`](../../xark_prover/struct.Circuit.html)) and the CLI
//! soundness gate (`xark prove` / `xark check --inputs`), so both worlds surface
//! the *same* explanation from one place.

use crate::profile::ProfileProgram;
use crate::r1cs::R1csProgram;
use crate::solver::SolveError;

/// Render a solve/check failure into a multi-line explanation.
///
/// For a constraint violation ([`SolveError::ConstraintFailed`]) this names the
/// constraint index, its `a·b = c` debug note (from `r1cs`), and — if `profile`
/// is `Some` — the `file:line:col`, function chain, and kind. Constraint ids are
/// index-aligned across the primitive IR, `r1cs.json`, and `profile.json` (the
/// lowering emits them 1:1), so the single failing index resolves all three.
/// Any other error is rendered via its `Display`.
pub fn describe_unsatisfied(
    err: &SolveError,
    r1cs: &R1csProgram,
    profile: Option<&ProfileProgram>,
) -> String {
    let SolveError::ConstraintFailed(i) = err else {
        return format!("witness could not be solved: {err}");
    };
    let i = *i;
    let mut msg = format!("witness does not satisfy the circuit — constraint #{i} does not hold");

    // The `a·b = c` debug note (kept in `r1cs.json`) names the operation.
    if let Some(note) = r1cs
        .constraints
        .iter()
        .find(|c| c.id as usize == i)
        .and_then(|c| c.debug.as_ref())
        .and_then(|d| d.note.as_deref())
    {
        msg.push_str(&format!("\n        {note}"));
    }

    // Full attribution (source line + function chain + kind) when the circuit was
    // built with `--profile` (as `xark test` does); otherwise a hint on how to
    // get it.
    match profile.and_then(|p| p.constraints.iter().find(|c| c.id as usize == i)) {
        Some(p) => {
            if !p.file.is_empty() {
                msg.push_str(&format!("\n        at {}:{}:{}", p.file, p.line, p.col));
            }
            if !p.chain.is_empty() {
                msg.push_str(&format!("\n        function: {}", p.chain.join(" → ")));
            }
            msg.push_str(&format!("\n        kind: {}", p.kind.as_str()));
        }
        None => msg.push_str(
            "\n        (build with `--profile`, or run via `xark test`, for the \
             source line and function chain)",
        ),
    }
    msg
}
