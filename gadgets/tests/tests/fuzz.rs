//! Property/fuzz tests for the verifier against adversarial bytes.
//!
//! Two invariants the on-chain verifier must hold for *any* attacker-supplied
//! input:
//! * **No panic** — a panic on chain aborts the program (compute exhaustion /
//!   DoS); off chain it's a crash. `verify_groth16` must always return a
//!   `Result`, never unwind.
//! * **Fail-closed** — random / mutated bytes must never return `Ok(true)`.
//!   A false accept is a forgery.
//!
//! proptest shrinks any counterexample to a minimal failing input.

use proptest::prelude::*;
use xark_tests::{fixtures, verify_groth16, verify_proof_only, verify_proof_only_strict};

proptest! {
 #![proptest_config(ProptestConfig::with_cases(2048))]

 /// Arbitrary (vk, proof, public_inputs) byte strings: never panic, never
 /// accept.
 #[test]
 fn verify_groth16_total_and_fail_closed(
 vk in prop::collection::vec(any::<u8>(), 0..1200),
 proof in prop::collection::vec(any::<u8>(), 0..400),
 pi in prop::collection::vec(any::<u8>(), 0..400),
 ) {
 prop_assert!(!matches!(verify_groth16(&vk, &proof, &pi), Ok(true)));
 }

 /// Same for the instruction-data entry point.
 #[test]
 fn verify_proof_only_total_and_fail_closed(
 vk in prop::collection::vec(any::<u8>(), 0..1200),
 data in prop::collection::vec(any::<u8>(), 0..600),
 ) {
 prop_assert!(!matches!(verify_proof_only(&vk, &data), Ok(true)));
 }

 /// Structured fuzz near a *valid* proof: overwrite one byte of the committed
 /// KAT instruction data. Under the **strict** verifier, *any* single-byte
 /// change must break verification.
 ///
 /// This is checked against `verify_proof_only_strict`, not the plain entry
 /// point: the `alt_bn128` syscall masks the unused top flag bits of each
 /// coordinate limb, so flipping one of those bits (e.g. bit 255 of `-A.y`,
 /// byte 63) decodes to the *same* point and still verifies under the plain
 /// path. The strict path rejects that non-canonical encoding, restoring the
 /// "every byte matters" property. (The plain path's masking behaviour — and
 /// that it matches the on-chain syscall — is pinned by
 /// `sbpf.rs::flag_bit_mutation_onchain`.)
 #[test]
 fn single_byte_mutation_never_verifies_strict(idx in 0usize..288, byte in any::<u8>()) {
 let mut data = fixtures::ARITHMETIC_SQUARE_INSTRUCTION_DATA.to_vec();
 if data[idx] != byte {
 data[idx] = byte;
 prop_assert!(
 !matches!(verify_proof_only_strict(fixtures::ARITHMETIC_SQUARE_VK_LE, &data), Ok(true)),
 "single-byte mutation at index {idx} verified under strict"
 );
 }
 }

 /// Truncations of valid instruction data must never verify.
 #[test]
 fn truncation_never_verifies(len in 0usize..288) {
 let data = &fixtures::ARITHMETIC_SQUARE_INSTRUCTION_DATA[..len];
 prop_assert!(
 !matches!(verify_proof_only(fixtures::ARITHMETIC_SQUARE_VK_LE, data), Ok(true))
 );
 }
}

proptest! {
 #![proptest_config(ProptestConfig::with_cases(1024))]

 /// The DAG-compact artifact decoder must be TOTAL: arbitrary bytes — a corrupted
 /// or hostile `circuit.xbc` — return a clean `Err`, never panic. A panic in a
 /// build/prove tool is a crash; in a shared decoder it's a DoS.
 #[test]
 fn function_decode_arbitrary_never_panics(bytes in prop::collection::vec(any::<u8>(), 0..2048)) {
 let _ = xark_ir::function_decode::expand_function_blob(&bytes);
 }

 /// Past the version dispatch: a well-formed `XBC`+v1 header with a random body
 /// exercises the parser interior, not just the magic check.
 #[test]
 fn function_decode_body_never_panics(tail in prop::collection::vec(any::<u8>(), 0..2048)) {
 let mut bytes = xark_ir::bytecode::MAGIC.to_vec();
 bytes.extend_from_slice(&1u16.to_le_bytes());
 bytes.extend_from_slice(&tail);
 let _ = xark_ir::function_decode::expand_function_blob(&bytes);
 }
}
