//! DOT graph emission for an [`R1csProgram`].
//!
//! Variables become oval nodes labelled `name\nVisibility`; each constraint
//! becomes a box node. Variables appearing in the `a`/`b` sides of a constraint
//! feed *into* the constraint node; variables in the `c` side are fed *from* it.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use crate::linear_combination::{LinearCombination, VarId};
use crate::r1cs::{R1csProgram, Visibility};

fn visibility_label(v: &Visibility) -> &'static str {
    match v {
        Visibility::Private => "Private",
        Visibility::Public => "Public",
        Visibility::Internal => "Internal",
    }
}

fn vars_of(lc: &LinearCombination) -> BTreeSet<VarId> {
    lc.terms.iter().map(|t| t.var).collect()
}

/// Render the human-readable constraint description used in the box label.
fn constraint_label(id: u32, note: Option<&str>) -> String {
    match note {
        Some(note) => format!("C{id}: {note}"),
        None => format!("C{id}"),
    }
}

pub fn to_dot(program: &R1csProgram) -> String {
    let mut out = String::new();
    out.push_str("digraph R1CS {\n");
    out.push_str("  rankdir=LR;\n\n");

    // Variable nodes, ordered by id for determinism.
    for var in &program.variables {
        let _ = writeln!(
            out,
            "  v{} [label=\"{}\\n{}\"];",
            var.id,
            var.name,
            visibility_label(&var.visibility)
        );
    }
    out.push('\n');

    // Constraint nodes.
    for c in &program.constraints {
        let note = c.debug.as_ref().and_then(|d| d.note.as_deref());
        let _ = writeln!(
            out,
            "  constraint{} [shape=box, label=\"{}\"];",
            c.id,
            constraint_label(c.id, note)
        );
    }
    out.push('\n');

    // Edges: inputs (a, b) feed the constraint; outputs (c) are produced by it.
    for c in &program.constraints {
        let mut inputs = vars_of(&c.a);
        inputs.extend(vars_of(&c.b));
        for v in &inputs {
            let _ = writeln!(out, "  v{} -> constraint{};", v, c.id);
        }
        for v in vars_of(&c.c) {
            let _ = writeln!(out, "  constraint{} -> v{};", c.id, v);
        }
    }

    out.push_str("}\n");
    out
}
