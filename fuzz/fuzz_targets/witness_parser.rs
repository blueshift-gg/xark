// Fuzz target: witness-map parser.
//
// `parse_witness_bytes` deserializes a gzipped bincode-encoded ACIR
// witness map. Like the artifact parser, the target asserts totality
// (no panic) on arbitrary bytes.

#![no_main]

use libfuzzer_sys::fuzz_target;
use xark_acir_r1cs::witness::parse_witness_bytes;

fuzz_target!(|data: &[u8]| {
    let _ = parse_witness_bytes(data);
});
