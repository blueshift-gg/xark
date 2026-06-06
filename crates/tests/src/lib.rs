//! The workspace's integration-test + benchmark suite (and the committed
//! circuit fixtures), gathered into one `publish = false` crate.
//!
//! Why a crate (not loose `/tests` files): the `#[svm_test]` cdylibs that
//! `svm-unit-test` generates depend on this crate's *lib*, so the fixture
//! `const`s must live here; and the CLI integration tests need to locate the
//! `xark` binary, which [`xark_bin`] does. The lib stays no_std / SBF-buildable
//! (only `xark-verifier` is a normal dependency, re-exported below); the
//! heavier test deps are dev-dependencies.
#![cfg_attr(any(target_os = "solana", target_arch = "bpf"), no_std)]

pub use xark_verifier::*;

/// Path to the built `xark` CLI binary, for the CLI integration tests.
/// Locates it next to the running test binary; if it isn't there yet (e.g.
/// `cargo test -p xark-tests` without a prior workspace build), builds it once.
#[cfg(not(any(target_os = "solana", target_arch = "bpf")))]
pub fn xark_bin() -> std::path::PathBuf {
    use std::sync::OnceLock;
    static BIN: OnceLock<std::path::PathBuf> = OnceLock::new();
    BIN.get_or_init(|| {
        // current_exe is target/<profile>/deps/<test>-<hash>; the binary sits
        // at target/<profile>/xark.
        let mut dir = std::env::current_exe().expect("current_exe");
        dir.pop();
        if dir.ends_with("deps") {
            dir.pop();
        }
        let bin = dir.join(if cfg!(windows) { "xark.exe" } else { "xark" });
        if !bin.exists() {
            let mut cmd = std::process::Command::new(env!("CARGO"));
            cmd.args(["build", "-p", "xark-cli"]);
            if !cfg!(debug_assertions) {
                cmd.arg("--release");
            }
            assert!(
                cmd.status().expect("spawn cargo build").success(),
                "failed to build the `xark` binary"
            );
        }
        bin
    })
    .clone()
}

/// Committed test fixtures, embedded as `const`s reachable from every
/// compilation context — including the auto-generated cdylib crates that
/// `svm-unit-test` spawns for each `#[svm_test]` body.
///
/// Update the byte contents by re-running `xark export` on the matching
/// fixture directory under `crates/tests/fixtures/groth16/`.
pub mod fixtures {
    /// LE Solana wire-format verifying key for the `arithmetic_square`
    /// circuit (1 public input).
    pub const ARITHMETIC_SQUARE_VK_LE: &[u8] =
        include_bytes!("../fixtures/groth16/arithmetic_square/verifying_key.solana.bin");

    /// LE Solana instruction-data blob for the `arithmetic_square` KAT:
    /// `proof_bytes (256 B) || public_inputs (32 B)`. Pass it straight into
    /// `xark_verifier::verify_proof_only(VK, INSTRUCTION_DATA)`.
    pub const ARITHMETIC_SQUARE_INSTRUCTION_DATA: &[u8] =
        include_bytes!("../fixtures/groth16/arithmetic_square/instruction_data.bin");

    /// Generate the typed fixture consts (`<NAME>_VK: Verifier<N>`,
    /// `<NAME>_PROOF: Proof`, `<NAME>_INPUTS: [[u8; 32]; N]`) for one
    /// committed circuit. The `from_le_bytes` / `parse_public_inputs` const
    /// constructors check each blob's byte length against `N` at compile time,
    /// so a wrong `N` here is a build error, not a runtime one.
    macro_rules! typed_fixture {
        ($vk:ident, $proof:ident, $inputs:ident, $n:literal, $dir:literal) => {
            pub const $vk: xark_verifier::Verifier<$n> =
                xark_verifier::Verifier::from_le_bytes(include_bytes!(concat!(
                    "../fixtures/groth16/",
                    $dir,
                    "/verifying_key.solana.bin"
                )));
            pub const $proof: xark_verifier::Proof = xark_verifier::Proof::from_le_bytes(
                include_bytes!(concat!("../fixtures/groth16/", $dir, "/proof.solana.bin")),
            );
            pub const $inputs: [[u8; 32]; $n] = xark_verifier::parse_public_inputs(include_bytes!(
                concat!("../fixtures/groth16/", $dir, "/public_inputs.solana.bin")
            ));
        };
    }

    // One per committed circuit; `N` is the public-input count reported by
    // `xark export`. Spanning N = 0 (ecdsa) to N = 32 (aes128, blake).
    typed_fixture!(
        ARITHMETIC_SQUARE_VK,
        ARITHMETIC_SQUARE_PROOF,
        ARITHMETIC_SQUARE_INPUTS,
        1,
        "arithmetic_square"
    );
    typed_fixture!(
        AES128_BASIC_VK,
        AES128_BASIC_PROOF,
        AES128_BASIC_INPUTS,
        32,
        "aes128_basic"
    );
    typed_fixture!(
        ARITHMETIC_PUBLIC_INPUTS_VK,
        ARITHMETIC_PUBLIC_INPUTS_PROOF,
        ARITHMETIC_PUBLIC_INPUTS_INPUTS,
        1,
        "arithmetic_public_inputs"
    );
    typed_fixture!(
        BITWISE_BASIC_VK,
        BITWISE_BASIC_PROOF,
        BITWISE_BASIC_INPUTS,
        2,
        "bitwise_basic"
    );
    typed_fixture!(
        BLAKE2S_BASIC_VK,
        BLAKE2S_BASIC_PROOF,
        BLAKE2S_BASIC_INPUTS,
        32,
        "blake2s_basic"
    );
    typed_fixture!(
        BLAKE3_BASIC_VK,
        BLAKE3_BASIC_PROOF,
        BLAKE3_BASIC_INPUTS,
        32,
        "blake3_basic"
    );
    typed_fixture!(
        BRILLIG_BASIC_VK,
        BRILLIG_BASIC_PROOF,
        BRILLIG_BASIC_INPUTS,
        1,
        "brillig_basic"
    );
    typed_fixture!(
        CURVE_BASIC_VK,
        CURVE_BASIC_PROOF,
        CURVE_BASIC_INPUTS,
        2,
        "curve_basic"
    );
    typed_fixture!(
        ECDSA_BASIC_VK,
        ECDSA_BASIC_PROOF,
        ECDSA_BASIC_INPUTS,
        0,
        "ecdsa_basic"
    );
    typed_fixture!(
        ECDSA_R1_BASIC_VK,
        ECDSA_R1_BASIC_PROOF,
        ECDSA_R1_BASIC_INPUTS,
        0,
        "ecdsa_r1_basic"
    );
    typed_fixture!(
        KECCAK_BASIC_VK,
        KECCAK_BASIC_PROOF,
        KECCAK_BASIC_INPUTS,
        25,
        "keccak_basic"
    );
    typed_fixture!(LARGE_PI_VK, LARGE_PI_PROOF, LARGE_PI_INPUTS, 16, "large_pi");
    typed_fixture!(
        MEMORY_CONST_VK,
        MEMORY_CONST_PROOF,
        MEMORY_CONST_INPUTS,
        1,
        "memory_const"
    );
    typed_fixture!(
        MEMORY_VAR_VK,
        MEMORY_VAR_PROOF,
        MEMORY_VAR_INPUTS,
        1,
        "memory_var"
    );
    typed_fixture!(MIXED_PI_VK, MIXED_PI_PROOF, MIXED_PI_INPUTS, 2, "mixed_pi");
    typed_fixture!(
        MULTI_FUNCTION_VK,
        MULTI_FUNCTION_PROOF,
        MULTI_FUNCTION_INPUTS,
        1,
        "multi_function"
    );
    typed_fixture!(
        NESTED_CALLS_VK,
        NESTED_CALLS_PROOF,
        NESTED_CALLS_INPUTS,
        1,
        "nested_calls"
    );
    typed_fixture!(
        POSEIDON_BASIC_VK,
        POSEIDON_BASIC_PROOF,
        POSEIDON_BASIC_INPUTS,
        4,
        "poseidon_basic"
    );
    typed_fixture!(
        RANGE_BASIC_VK,
        RANGE_BASIC_PROOF,
        RANGE_BASIC_INPUTS,
        1,
        "range_basic"
    );
    typed_fixture!(
        REORDER_PI_VK,
        REORDER_PI_PROOF,
        REORDER_PI_INPUTS,
        2,
        "reorder_pi"
    );
    typed_fixture!(
        RETURN_VALUES_ONLY_VK,
        RETURN_VALUES_ONLY_PROOF,
        RETURN_VALUES_ONLY_INPUTS,
        1,
        "return_values_only"
    );
    typed_fixture!(
        SHA256_BASIC_VK,
        SHA256_BASIC_PROOF,
        SHA256_BASIC_INPUTS,
        8,
        "sha256_basic"
    );
}
