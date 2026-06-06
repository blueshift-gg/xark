//! Per-circuit proof tests.
//!
//! For each committed circuit, lower its artifact + witness and run Groth16
//! setup → prove → verify entirely in-process, asserting that lowering succeeds
//! (every opcode is supported), the proof verifies, and every public input is
//! bound (flipping any one fails verification). See
//! [`common::assert_circuit_proves`].
//!
//! These replace the old per-gadget tests that shelled out to the `xark` binary
//! and parsed stdout; the binary surface itself is still covered by
//! `end_to_end.rs`, and the on-chain verifier by `sbpf.rs`.

mod common;
use common::assert_circuit_proves;

macro_rules! circuit_test {
    ($fn:ident, $name:literal, $pi:literal) => {
        #[test]
        fn $fn() {
            assert_circuit_proves($name, $pi);
        }
    };
}

// Gadget circuits (was aes128.rs, bitwise.rs, … — one `*_verifies` +
// `*_tampered_*_fails` test each, now both covered by the helper).
circuit_test!(aes128_basic, "aes128_basic", 32);
circuit_test!(bitwise_basic, "bitwise_basic", 2);
circuit_test!(blake2s_basic, "blake2s_basic", 32);
circuit_test!(blake3_basic, "blake3_basic", 32);
circuit_test!(keccak_basic, "keccak_basic", 25);
circuit_test!(poseidon_basic, "poseidon_basic", 4);
circuit_test!(curve_basic, "curve_basic", 2);
circuit_test!(brillig_basic, "brillig_basic", 1);
circuit_test!(memory_const, "memory_const", 1);

// Cross-circuit `Call` (was the prove/verify test in multi_function.rs; the
// `inspect`-helper-reporting tests stay there as CLI-surface tests).
circuit_test!(multi_function, "multi_function", 1);
circuit_test!(nested_calls, "nested_calls", 1);

// Public-input shapes (was public_inputs_matrix.rs).
circuit_test!(return_values_only, "return_values_only", 1);
circuit_test!(mixed_pi, "mixed_pi", 2);
circuit_test!(reorder_pi, "reorder_pi", 2);
circuit_test!(large_pi, "large_pi", 16);
