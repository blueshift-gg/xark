//! Circuit *profiling* data: a per-constraint attribution back to the user's
//! source line, the function call-chain that produced it, and its kind.
//!
//! This is written to a **separate** `profile.json` (never mixed into
//! `r1cs.json` / `circuit.json`, whose `debug` slots stay byte-identical). It is
//! consumed by `xark profile`, which aggregates a per-line / per-function /
//! per-kind drill-down so the circuit author can see which source lines cost the
//! most constraints and what those constraints are.

use serde::{Deserialize, Serialize};

/// The kind of an emitted R1CS constraint — what circuit operation produced it.
/// Set at each lowering emit-site so the profiler can bucket constraints by
/// their purpose (a range-check bit vs. a genuine multiplication vs. an
/// equality, …).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ConstraintKind {
    /// A genuine multiplication gate `a * b = c` (both `a`, `b` non-constant).
    Mul,
    /// A booleanity check `b * b = b` (⟺ `b ∈ {0, 1}`).
    Booleanity,
    /// A bit of an `n`-bit range proof (decomposition + recomposition pin).
    RangeCheck,
    /// A structural part of an ordered comparison (`<`, `<=`, `>`, `>=`).
    Comparison,
    /// An equality constraint `(a - b) * 1 = 0` (from `assert_eq`).
    Equality,
    /// A fused boolean XOR gate.
    Xor,
    /// A fused boolean OR gate.
    Or,
    /// A constraint that pins a hint/advice output to its defining relation.
    HintPin,
    /// Anything else (e.g. an internal linear-combination materialization).
    Other,
}

impl ConstraintKind {
    /// A short, stable label for display / JSON.
    pub fn as_str(self) -> &'static str {
        match self {
            ConstraintKind::Mul => "Mul",
            ConstraintKind::Booleanity => "Booleanity",
            ConstraintKind::RangeCheck => "RangeCheck",
            ConstraintKind::Comparison => "Comparison",
            ConstraintKind::Equality => "Equality",
            ConstraintKind::Xor => "Xor",
            ConstraintKind::Or => "Or",
            ConstraintKind::HintPin => "HintPin",
            ConstraintKind::Other => "Other",
        }
    }
}

/// One constraint's profile record: which constraint (`id`, matching the
/// `R1csConstraint::id`), the top-level user source location that triggered it,
/// the function call-chain it expanded through, and its [`ConstraintKind`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ConstraintProfile {
    /// The R1CS constraint id (identical to its index in `r1cs.json`).
    pub id: u32,
    /// Source file of the top-level circuit statement/terminator (may be
    /// relative to `source_root`, or empty if the span had no location).
    pub file: String,
    /// 1-based source line.
    pub line: u32,
    /// 1-based source column.
    pub col: u32,
    /// Function names (outermost → innermost) the user line expanded
    /// into, with low-level arithmetic operator impls elided.
    pub chain: Vec<String>,
    /// What kind of constraint this is.
    pub kind: ConstraintKind,
}

/// The whole `profile.json`: every emitted constraint's attribution, plus the
/// absolute source root the (possibly relative) `file` paths resolve against.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProfileProgram {
    /// Absolute path the compile ran from (the crate dir under `xark build`),
    /// used to resolve relative `file` paths back to readable source.
    pub source_root: String,
    pub constraints: Vec<ConstraintProfile>,
}

/// Serialize a profile to pretty JSON (deterministic across runs).
pub fn to_json_pretty(profile: &ProfileProgram) -> String {
    serde_json::to_string_pretty(profile).expect("ProfileProgram is always serializable")
}

/// Parse a [`ProfileProgram`] from JSON (inverse of [`to_json_pretty`]).
pub fn from_json(s: &str) -> Result<ProfileProgram, serde_json::Error> {
    serde_json::from_str(s)
}
