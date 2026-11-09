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

 /// A valid artifact cut anywhere, then a huge count and junk: whichever field
 /// the count lands in, every entry point returns rather than aborting (#64).
 #[test]
 fn function_decode_huge_count_after_valid_prefix(
 cut in 6usize..4096,
 bits in 20u32..64,
 tail in prop::collection::vec(any::<u8>(), 0..64),
 ) {
 let xbc = include_bytes!("../../../../crates/groth16/tests/fixtures/zkyc.xbc");
 let mut b = xbc[..cut.min(xbc.len())].to_vec();
 hostile_xbc::uv(&mut b, (1u64 << bits) | 1);
 b.extend_from_slice(&tail);
 let _ = xark_ir::function_decode::decode_input_vars(&b);
 let _ = xark_ir::function_decode::expand_function_blob(&b);
 let _ = xark_ir::function_decode::expand_function_blob_reduced(&b);
 let _ = xark_ir::function_decode::ReducedRowStream::new(&b);
 }
}

/// Hostile `circuit.xbc` shapes that used to abort the process (an allocation
/// sized by a declared count, or a stack overflow) instead of unwinding: each must
/// now come back as an `Err` from every entry point that promises one.
mod hostile_xbc {
    use xark_ir::function_decode::{
        ReducedRowStream, decode_input_vars, expand_function_blob, expand_function_blob_reduced,
    };

    pub(super) fn uv(out: &mut Vec<u8>, mut v: u64) {
        loop {
            let b = (v & 0x7f) as u8;
            v >>= 7;
            out.push(if v == 0 { b } else { b | 0x80 });
            if v == 0 {
                return;
            }
        }
    }

    /// Magic, container version 2, an empty name, modulus "7", then the counts.
    fn header(num_vars: u64, num_inputs: u64) -> Vec<u8> {
        let mut b = xark_ir::bytecode::MAGIC.to_vec();
        b.extend_from_slice(&2u16.to_le_bytes());
        uv(&mut b, 0);
        uv(&mut b, 1);
        b.push(b'7');
        uv(&mut b, num_vars);
        uv(&mut b, num_inputs);
        b
    }

    /// A CALL item (tag 5) of template `def` at base 16, no plugs.
    fn call(b: &mut Vec<u8>, def: u64) {
        b.push(5);
        uv(b, def);
        uv(b, 16);
        uv(b, 0);
    }

    /// `header(16, 0)`, an empty constant pool and `defs` templates (each: base
    /// 16, no plugs or outputs, the constraint items `body` writes, no witness
    /// items), then a top level whose constraint stream calls template `top`.
    fn artifact(defs: usize, body: impl Fn(usize, &mut Vec<u8>), top: u64) -> Vec<u8> {
        let mut b = header(16, 0);
        uv(&mut b, 0);
        uv(&mut b, defs as u64);
        for d in 0..defs {
            b.extend_from_slice(&[16, 0, 0]);
            body(d, &mut b);
            uv(&mut b, 0);
        }
        uv(&mut b, 1);
        call(&mut b, top);
        b.extend_from_slice(&[0, 0]);
        b
    }

    /// One `0 · 0 = 0` row (tag 0, three empty LCs).
    fn zero_row(b: &mut Vec<u8>) {
        b.push(0);
        for _ in 0..3 {
            b.extend_from_slice(&[0, 0, 0]);
        }
    }

    fn assert_rejected(b: &[u8], what: &str) {
        assert!(expand_function_blob(b).is_err(), "{what}: expand");
        assert!(expand_function_blob_reduced(b).is_err(), "{what}: reduced");
        assert!(ReducedRowStream::new(b).is_err(), "{what}: row stream");
    }

    /// #64: a 16-byte header declaring 2^40 signature inputs.
    #[test]
    fn huge_input_count_is_an_error() {
        let b = header(16, 1 << 40);
        assert!(decode_input_vars(&b).is_err());
        assert_rejected(&b, "2^40 inputs");
    }

    /// #64: 2^40 variables over an empty, well-formed body.
    #[test]
    fn huge_variable_count_is_an_error() {
        let body = [0, 0, 0, 0, 0]; // no pool, templates, items or keeps
        let mut b = header(1 << 40, 0);
        b.extend_from_slice(&body);
        assert_rejected(&b, "2^40 vars");
        // The same body with a sane count decodes.
        let mut ok = header(16, 0);
        ok.extend_from_slice(&body);
        assert!(expand_function_blob(&ok).is_ok());
        assert!(ReducedRowStream::new(&ok).is_ok());
    }

    /// #64: a rolled-CALL block (tag 6) repeating its one call 2^40 times.
    #[test]
    fn huge_rolled_call_count_is_an_error() {
        let rolled = |count: u64| {
            let mut b = header(16, 0);
            b.extend_from_slice(&[0, 1, 16, 0, 0, 0, 0]); // one empty template
            b.extend_from_slice(&[1, 6]);
            uv(&mut b, count);
            uv(&mut b, 1); // period
            b.extend_from_slice(&[0, 16, 2, 0]); // template 0, base 16, step +1, no plugs
            b.extend_from_slice(&[0, 0]);
            b
        };
        assert_rejected(&rolled(1 << 40), "rolled calls");
        assert!(expand_function_blob(&rolled(3)).is_ok());
    }

    /// #64: a rolled run (tag 7) of two nested 2^32 − 1-iteration loops around an
    /// empty body: a few bytes standing for 2^64 iterations.
    #[test]
    fn nested_rolled_run_is_an_error() {
        let nested = |count: u32| {
            let mut run = vec![1]; // one item
            for body in [1, 0] {
                run.push(1); // a Repeat
                uv(&mut run, u64::from(count));
                uv(&mut run, body); // body items: the inner Repeat, then none
            }
            run.extend_from_slice(&[0, 0, 0, 0, 0, 0]); // each: no steps, no notes
            let mut b = header(16, 0);
            b.extend_from_slice(&[0, 0, 1, 7]);
            uv(&mut b, run.len() as u64);
            b.extend_from_slice(&run);
            b.extend_from_slice(&[0, 0]);
            b
        };
        assert_rejected(&nested(u32::MAX), "nested rolled run");
        assert!(expand_function_blob(&nested(3)).is_ok());
    }

    /// #65: a template that calls itself (the issue's 29-byte reproducer).
    #[test]
    fn self_calling_template_is_an_error() {
        let b = artifact(
            1,
            |_, b| {
                uv(b, 1);
                call(b, 0);
            },
            0,
        );
        assert_rejected(&b, "self call");
    }

    /// #65: two templates that call each other.
    #[test]
    fn mutually_recursive_templates_are_an_error() {
        let b = artifact(
            2,
            |d, b| {
                uv(b, 1);
                call(b, 1 - d as u64);
            },
            0,
        );
        assert_rejected(&b, "mutual recursion");
    }

    /// #65: a call to a template that isn't there.
    #[test]
    fn call_to_a_missing_template_is_an_error() {
        assert_rejected(&artifact(1, |_, b| uv(b, 0), 5), "missing template");
    }

    /// #65: no cycle, but template `k` calls `k − 1` twice, 40 deep: a few hundred
    /// bytes that expand to 2^40 rows.
    #[test]
    fn exponential_nesting_is_an_error() {
        let nest = |depth: usize| {
            artifact(
                depth + 1,
                |d, b| {
                    if d == 0 {
                        uv(b, 1);
                        zero_row(b);
                    } else {
                        uv(b, 2);
                        call(b, d as u64 - 1);
                        call(b, d as u64 - 1);
                    }
                },
                depth as u64,
            )
        };
        assert_rejected(&nest(40), "2^40 rows");
        // Shallow, the same shape is a circuit: 2^4 `0 = 0` rows.
        assert_eq!(
            expand_function_blob(&nest(4)).unwrap().constraints.len(),
            16
        );
    }
}
