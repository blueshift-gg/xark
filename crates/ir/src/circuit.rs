//! The **circuit program** — the single lossless artifact the bytecode
//! (`circuit.xbc`) encodes.
//!
//! # Why this and not `PrimitiveProgram`
//!
//! The bytecode used to encode a [`PrimitiveProgram`], whose constraints are
//! flattened `Expression`s (`Σ mul_terms + Σ linear_terms + const == 0`). That
//! form is **lossy** with respect to the R1CS: `expr_from_r1cs` multiplies out
//! `a·b` into a flat bag of `mul_terms`, and `(x+y)·(x−y)` collapses to `x²−y²`
//! — the factorization Groth16 needs is gone. So a `.xbc` built from the
//! primitive form could not reconstruct the R1CS, which is why `r1cs.json` had
//! to be kept alongside it.
//!
//! A [`CircuitProgram`] instead stores the R1CS `a·b=c` rows verbatim (the
//! lossless superset) plus the witness-generation program. From it we can derive
//! **both** consumer views on load:
//!
//! * [`CircuitProgram::to_r1cs`] → the [`R1csProgram`] the Groth16 backend needs.
//! * [`CircuitProgram::to_primitive`] → the [`PrimitiveProgram`] the reference
//!   solver needs (constraints flattened via [`expr_from_r1cs`], a pure function
//!   of the R1CS).
//!
//! So `circuit.xbc` becomes the sole build artifact: `r1cs.json` and
//! `circuit.json` are now derivable (and only emitted with `--emit-json`).

use std::collections::BTreeMap;

use crate::field::FieldConst;
use crate::linear_combination::{LinearCombination, VarId};
use crate::primitive::{self, Expression, LinearTerm, MulTerm, PrimitiveProgram, Var, VarRole};
use crate::r1cs::{
    DebugInfo, FieldSpec as R1csFieldSpec, R1csConstraint, R1csProgram, Variable, Visibility,
};

/// One rank-1 constraint `a · b = c` (all [`LinearCombination`]s). The compact,
/// on-disk analogue of [`R1csConstraint`] without the redundant sequential `id`
/// (implied by position) or the debug-only `DebugInfo` (regenerated on export).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R1csRow {
    pub a: LinearCombination,
    pub b: LinearCombination,
    pub c: LinearCombination,
    /// Debug annotation (e.g. `secret * secret = t0`), carried so the
    /// solver-facing `Expression` reproduces the compiler's exactly. Debug-only;
    /// Phase A drops it from the wire.
    pub note: Option<String>,
}

/// The whole circuit as the bytecode encodes it: R1CS rows (the lossless
/// constraint form) + the ordered witness-generation program, over a named
/// field, with the variable table. Both the [`R1csProgram`] (backend) and the
/// [`PrimitiveProgram`] (solver) are pure functions of this.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitProgram {
    pub field: primitive::FieldSpec,
    pub vars: Vec<Var>,
    /// R1CS `a·b=c` rows, in order.
    pub constraints: Vec<R1csRow>,
    /// The ordered witness-generation (hint) program.
    pub witness_gen: Vec<primitive::WitnessGen>,
}

impl CircuitProgram {
    /// Assemble from the compiler's two lowered views: the R1CS carries the
    /// factored constraints, the primitive program carries the vars + witness
    /// program (both share the same `VarId`s and ordering).
    pub fn from_lowered(r1cs: &R1csProgram, prim: &PrimitiveProgram) -> Self {
        CircuitProgram {
            field: prim.field.clone(),
            vars: prim.vars.clone(),
            constraints: r1cs
                .constraints
                .iter()
                .map(|c| R1csRow {
                    a: c.a.clone(),
                    b: c.b.clone(),
                    c: c.c.clone(),
                    note: c.debug.as_ref().and_then(|d| d.note.clone()),
                })
                .collect(),
            witness_gen: prim.witness_gen.clone(),
        }
    }

    /// The reference-solver view: each R1CS row flattened to an AssertZero
    /// `Expression` via [`expr_from_r1cs`]. Deterministic and identical to what
    /// the compiler produced for `circuit.json`, so the solver behaves the same
    /// whether it loaded the JSON or the bytecode.
    pub fn to_primitive(&self) -> PrimitiveProgram {
        PrimitiveProgram {
            field: self.field.clone(),
            vars: self.vars.clone(),
            constraints: self
                .constraints
                .iter()
                .map(|r| expr_from_r1cs(&r.a, &r.b, &r.c, r.note.clone()))
                .collect(),
            witness_gen: self.witness_gen.clone(),
        }
    }

    /// The Groth16-backend view: the R1CS rows as an [`R1csProgram`], with the
    /// `role → visibility` mapping inverted (`PublicInput→Public`,
    /// `PrivateInput→Private`, `Derived→Internal`) — the exact inverse of the
    /// bijection the compiler applied, so the reconstructed variable table
    /// (ids, order, visibilities) matches the original constraint system. The
    /// debug-only `note`/`source_span` are not reconstructed (the backend
    /// ignores them).
    pub fn to_r1cs(&self) -> R1csProgram {
        R1csProgram {
            field: R1csFieldSpec {
                name: self.field.name.clone(),
                modulus_decimal: Some(self.field.modulus_decimal.clone()),
            },
            variables: self
                .vars
                .iter()
                .map(|v| Variable {
                    id: v.id,
                    name: v.name.clone(),
                    visibility: match v.role {
                        VarRole::PublicInput => Visibility::Public,
                        VarRole::PrivateInput => Visibility::Private,
                        VarRole::Derived => Visibility::Internal,
                    },
                })
                .collect(),
            constraints: self
                .constraints
                .iter()
                .enumerate()
                .map(|(i, r)| R1csConstraint {
                    id: i as u32,
                    a: r.a.clone(),
                    b: r.b.clone(),
                    c: r.c.clone(),
                    debug: r.note.as_ref().map(|n| DebugInfo {
                        source_span: None,
                        note: Some(n.clone()),
                    }),
                })
                .collect(),
        }
    }

    /// Like [`to_r1cs`](Self::to_r1cs) but **consumes** `self`, moving each row's
    /// linear combinations into the `R1csProgram` instead of deep-cloning them.
    /// The prover uses this once the solver is done with the `CircuitProgram`, so
    /// handing the R1CS to the Groth16 backend costs O(rows) shallow moves rather
    /// than re-allocating every constraint's `Vec<Term>`.
    pub fn into_r1cs(self) -> R1csProgram {
        R1csProgram {
            field: R1csFieldSpec {
                name: self.field.name,
                modulus_decimal: Some(self.field.modulus_decimal),
            },
            variables: self
                .vars
                .into_iter()
                .map(|v| Variable {
                    id: v.id,
                    name: v.name,
                    visibility: match v.role {
                        VarRole::PublicInput => Visibility::Public,
                        VarRole::PrivateInput => Visibility::Private,
                        VarRole::Derived => Visibility::Internal,
                    },
                })
                .collect(),
            constraints: self
                .constraints
                .into_iter()
                .enumerate()
                .map(|(i, r)| R1csConstraint {
                    id: i as u32,
                    a: r.a,
                    b: r.b,
                    c: r.c,
                    debug: r.note.map(|n| DebugInfo {
                        source_span: None,
                        note: Some(n),
                    }),
                })
                .collect(),
        }
    }
}

/// Expand an R1CS constraint `a · b = c` (all linear combinations) into an
/// AssertZero-style expression `a·b − c == 0`. Pure over xark-ir types; moved
/// here from the compiler so the solver-facing primitive view can be derived
/// from the bytecode without a `rustc` dependency.
pub fn expr_from_r1cs(
    a: &LinearCombination,
    b: &LinearCombination,
    c: &LinearCombination,
    note: Option<String>,
) -> Expression {
    let mut linear: BTreeMap<VarId, FieldConst> = BTreeMap::new();
    let add_lin = |var: VarId, coeff: FieldConst, linear: &mut BTreeMap<VarId, FieldConst>| {
        let e = linear.entry(var).or_insert_with(FieldConst::zero);
        *e = e.add(&coeff);
    };

    // a·b: constant·constant + a_i·b_const·x_i + a_const·b_j·x_j + a_i·b_j·x_i·x_j
    let mut constant = a.constant.mul(&b.constant);
    for ta in &a.terms {
        add_lin(ta.var, ta.coeff.mul(&b.constant), &mut linear);
    }
    for tb in &b.terms {
        add_lin(tb.var, a.constant.mul(&tb.coeff), &mut linear);
    }
    let mut mul_terms = Vec::new();
    for ta in &a.terms {
        for tb in &b.terms {
            let coeff = ta.coeff.mul(&tb.coeff);
            if !coeff.is_zero() {
                mul_terms.push(MulTerm {
                    coeff,
                    left: ta.var,
                    right: tb.var,
                });
            }
        }
    }

    // − c
    constant = constant.add(&c.constant.neg());
    for tc in &c.terms {
        add_lin(tc.var, tc.coeff.neg(), &mut linear);
    }

    let linear_terms = linear
        .into_iter()
        .filter(|(_, coeff)| !coeff.is_zero())
        .map(|(var, coeff)| LinearTerm { coeff, var })
        .collect();

    Expression {
        mul_terms,
        linear_terms,
        constant,
        note,
    }
}
