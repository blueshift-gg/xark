//! JSON serialization of an [`R1csProgram`].

use crate::r1cs::R1csProgram;

/// Serialize a program to pretty JSON (deterministic across runs).
pub fn to_json_pretty(program: &R1csProgram) -> String {
    serde_json::to_string_pretty(program).expect("R1csProgram is always serializable")
}

/// Serialize a program to compact JSON. Used for very large circuits where the
/// pretty form would be multi-gigabyte; consumed by the backend (`xark setup` /
/// `xark prove`) exactly like [`to_json_pretty`].
pub fn to_json(program: &R1csProgram) -> String {
    serde_json::to_string(program).expect("R1csProgram is always serializable")
}

/// Parse an [`R1csProgram`] from JSON (inverse of [`to_json_pretty`]).
pub fn from_json(s: &str) -> Result<crate::R1csProgram, serde_json::Error> {
    serde_json::from_str(s)
}
