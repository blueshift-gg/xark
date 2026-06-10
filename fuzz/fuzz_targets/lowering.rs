// Fuzz target: ACIR → R1CS lowering, end-to-end.
//
// Composes `parse_artifact_bytes` + `lower_program`. Looks for panics in
// the lowering passes that the per-opcode tests may have missed: opcode
// dispatch, witness-index shifting (cross-circuit Call), memory-op
// constant- vs variable-index detection, gated predicate handling.

#![no_main]

use libfuzzer_sys::fuzz_target;
use xark_acir_r1cs::{artifact::parse_artifact_bytes, lower_program};

fuzz_target!(|data: &[u8]| {
    if let Ok(artifact) = parse_artifact_bytes(data, "fuzz".to_string()) {
        let _ = lower_program(artifact);
    }
});
