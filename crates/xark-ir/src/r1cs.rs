//! R1CS program data structures.

use serde::{Deserialize, Serialize};

use crate::field::FieldConst;
use crate::linear_combination::{LinearCombination, VarId};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Visibility {
    Private,
    Public,
    Internal,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Variable {
    pub id: VarId,
    pub name: String,
    pub visibility: Visibility,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DebugInfo {
    pub source_span: Option<String>,
    pub note: Option<String>,
}

/// A single rank-1 constraint: `a * b = c`, where each of `a`, `b`, `c` is a
/// [`LinearCombination`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct R1csConstraint {
    pub id: u32,
    pub a: LinearCombination,
    pub b: LinearCombination,
    pub c: LinearCombination,
    pub debug: Option<DebugInfo>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FieldSpec {
    pub name: String,
    pub modulus_decimal: Option<String>,
}

impl FieldSpec {
    /// The MVP field spec: unknown field, no modulus.
    pub fn unknown() -> Self {
        FieldSpec {
            name: "unknown".to_string(),
            modulus_decimal: None,
        }
    }

    /// The BN254 scalar field (a.k.a. `Fr`), the common R1CS/Groth16 field.
    pub fn bn254() -> Self {
        FieldSpec {
            name: "bn254".to_string(),
            modulus_decimal: Some(
                "21888242871839275222246405745257275088548364400416034343698204186575808495617"
                    .to_string(),
            ),
        }
    }

    /// Look up a named field, or treat the name as a raw decimal modulus.
    pub fn named(name: &str) -> Self {
        match name {
            "bn254" | "bn128" => FieldSpec::bn254(),
            "unknown" => FieldSpec::unknown(),
            other => FieldSpec {
                name: "custom".to_string(),
                modulus_decimal: Some(other.to_string()),
            },
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct R1csProgram {
    pub field: FieldSpec,
    pub variables: Vec<Variable>,
    pub constraints: Vec<R1csConstraint>,
}

impl R1csConstraint {
    /// Build a multiplication constraint `lhs * rhs = out_var`.
    pub fn mul(id: u32, lhs: LinearCombination, rhs: LinearCombination, out: VarId, note: &str) -> Self {
        R1csConstraint {
            id,
            a: lhs,
            b: rhs,
            c: LinearCombination::var(out),
            debug: Some(DebugInfo {
                source_span: None,
                note: Some(note.to_string()),
            }),
        }
    }

    /// Build a general constraint `a * b = c` from explicit linear combinations.
    pub fn general(
        id: u32,
        a: LinearCombination,
        b: LinearCombination,
        c: LinearCombination,
        note: &str,
    ) -> Self {
        R1csConstraint {
            id,
            a,
            b,
            c,
            debug: Some(DebugInfo {
                source_span: None,
                note: Some(note.to_string()),
            }),
        }
    }

    /// Build an equality constraint `(lhs - rhs) * 1 = 0`.
    pub fn equal(id: u32, lhs: LinearCombination, rhs: LinearCombination, note: &str) -> Self {
        R1csConstraint {
            id,
            a: lhs.sub(rhs),
            b: LinearCombination::one(),
            c: LinearCombination {
                constant: FieldConst::zero(),
                terms: Vec::new(),
            },
            debug: Some(DebugInfo {
                source_span: None,
                note: Some(note.to_string()),
            }),
        }
    }
}
