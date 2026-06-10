// Fuzz target: NoirArtifact parser.
//
// `parse_artifact_bytes` deserializes a base64'd compressed-bincode Noir
// artifact. Adversarial input here would let an attacker confuse the
// proving / verifying path before any cryptographic check fires. The
// target asserts the parser doesn't panic on arbitrary bytes — any
// reachable panic is a bug.

#![no_main]

use libfuzzer_sys::fuzz_target;
use xark_acir_r1cs::artifact::parse_artifact_bytes;

fuzz_target!(|data: &[u8]| {
    // We only check totality (no panic). Errors are expected on most inputs;
    // the bug we're looking for is an unhandled panic or infinite loop.
    let _ = parse_artifact_bytes(data, "fuzz".to_string());
});
