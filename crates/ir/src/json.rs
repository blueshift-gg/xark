//! JSON serialization of an [`R1csProgram`].

use crate::r1cs::R1csProgram;

/// Serialize a program to pretty JSON (deterministic across runs).
pub fn to_json_pretty(program: &R1csProgram) -> String {
    serde_json::to_string_pretty(program).expect("R1csProgram is always serializable")
}

/// Serialize a program to compact JSON (for very large circuits).
pub fn to_json(program: &R1csProgram) -> String {
    serde_json::to_string(program).expect("R1csProgram is always serializable")
}

/// Serialize compact JSON straight into `w` — no intermediate `String` (the flat
/// `r1cs.json` is multi-GB on heavy circuits, so the string form is a full copy).
pub fn write_json<W: std::io::Write>(program: &R1csProgram, w: W) -> std::io::Result<()> {
    serde_json::to_writer(w, program).map_err(std::io::Error::from)
}

/// Pretty JSON straight into `w` (see [`write_json`]).
pub fn write_json_pretty<W: std::io::Write>(program: &R1csProgram, w: W) -> std::io::Result<()> {
    serde_json::to_writer_pretty(w, program).map_err(std::io::Error::from)
}

/// Parse an [`R1csProgram`] from JSON (inverse of [`to_json_pretty`]).
pub fn from_json(s: &str) -> Result<crate::R1csProgram, serde_json::Error> {
    serde_json::from_str(s)
}
