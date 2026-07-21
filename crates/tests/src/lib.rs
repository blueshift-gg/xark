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

// Re-export the BN254 group-op crate so the `#[svm_test]` cdylibs that
// svm-unit-test generates can reach it as `xark_tests::solana_nostd_alt_bn128`.
// Each generated cdylib's Cargo.toml only carries `xark-tests = { path = ... }`
// as its direct dep — the inner crate's deps are not in scope under cargo's
// resolver, so a bare `use solana_nostd_alt_bn128::...` in a #[svm_test] body
// fails to link on the SBF target. Routing through this re-export is the
// stable way to share the API.
pub use solana_nostd_alt_bn128;

/// The nightly channel the `xark-rustc` driver is pinned to (read from its
/// `rust-toolchain.toml`), used to build it via the `cargo` shim on a clean
/// checkout. Falls back to `"nightly"`.
#[cfg(not(any(target_os = "solana", target_arch = "bpf")))]
fn nightly_channel(rustc_crate: &std::path::Path) -> String {
    let toml = std::fs::read_to_string(rustc_crate.join("rust-toolchain.toml")).unwrap_or_default();
    for line in toml.lines() {
        let t = line.trim();
        if t.starts_with("channel") {
            if let Some(v) = t.split('"').nth(1) {
                return v.to_string();
            }
        }
    }
    "nightly".to_string()
}

/// Path to the built `xark` toolchain/CLI binary, for the CLI integration tests.
///
/// The toolchain is now two crates: `xark-cli` (the stable `xark` CLI, a normal
/// workspace member) and `xark-rustc` (the nightly `rustc_driver` shim, which is
/// *excluded* from the workspace under its own pinned nightly `rust-toolchain.toml`
/// and so is not built by a normal workspace `cargo build`).
///
/// This builds/locates both and — crucially — points the CLI at the separately
/// built driver by exporting `XARK_RUSTC` into this process's environment, which
/// every spawned `xark …` child inherits (the CLI's `rustc_shim()` honors it).
/// Returns the `xark` CLI binary path.
#[cfg(not(any(target_os = "solana", target_arch = "bpf")))]
pub fn xark_bin() -> std::path::PathBuf {
    use std::sync::OnceLock;
    static BIN: OnceLock<std::path::PathBuf> = OnceLock::new();
    BIN.get_or_init(|| {
        // CARGO_MANIFEST_DIR is crates/tests; the two toolchain crates are siblings.
        let crates_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
        let workspace_root = crates_dir.join("..");
        let rustc_crate = crates_dir.join("xark-rustc");

        // 1. The nightly `rustc_driver` shim. It's excluded from the workspace and
        //    pins its own nightly (its `rust-toolchain.toml`), so build it in place.
        let rustc_bin = 'found: {
            for profile in ["release", "debug"] {
                let p = rustc_crate.join("target").join(profile).join("xark-rustc");
                if p.exists() {
                    break 'found p;
                }
            }
            // The driver is nightly (`rustc_private`). `env!("CARGO")` is a concrete
            // binary that bypasses rustup's `rust-toolchain.toml`, so a clean
            // checkout (e.g. CI, no pre-built binary) would build it on the ambient
            // (stable) toolchain and fail. Invoke the `cargo` shim with
            // `RUSTUP_TOOLCHAIN` = the pinned channel instead (mirrors
            // `xark-test-harness`). `--features debug` compiles in the diagnostic
            // markers (`cached=`, timing) the harness asserts on; a `--features`
            // build still lands at `target/release/xark-rustc`.
            let channel = nightly_channel(&rustc_crate);
            let status = std::process::Command::new("cargo")
                .args([
                    "build",
                    "--release",
                    "--features",
                    "debug",
                    "--bin",
                    "xark-rustc",
                ])
                .current_dir(&rustc_crate)
                .env("RUSTUP_TOOLCHAIN", &channel)
                .env(
                    "RUSTFLAGS",
                    "--allow=unexpected_cfgs -Zalways-encode-mir -Zmir-opt-level=0",
                )
                .env_remove("CARGO_TARGET_DIR")
                .status()
                .expect("spawn cargo build for the xark-rustc driver");
            assert!(status.success(), "failed to build the `xark-rustc` driver");
            rustc_crate
                .join("target")
                .join("release")
                .join("xark-rustc")
        };
        // Every child `xark …` command inherits this and uses it as the driver.
        std::env::set_var("XARK_RUSTC", &rustc_bin);

        // 2. The stable `xark` CLI (a workspace member → workspace target dir).
        // Always (re)build it with `--features debug` — do NOT reuse a pre-built
        // `target/release/xark`: the surrounding `cargo test --workspace` builds it
        // *without* the feature, and this harness asserts on the `debug`-only
        // diagnostic markers (`cached=`, timing). cargo cache-hits when it's already
        // debug-built, so this only recompiles after a non-debug workspace build.
        let exe = "xark";
        let status = std::process::Command::new(env!("CARGO"))
            .args([
                "build",
                "--release",
                "--features",
                "debug",
                "-p",
                "xark-cli",
                "--bin",
                "xark",
            ])
            .current_dir(&workspace_root)
            .status()
            .expect("spawn cargo build for the xark CLI binary");
        assert!(status.success(), "failed to build the `xark` CLI binary");
        workspace_root.join("target").join("release").join(exe)
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
    // `xark export` (e.g. ecdsa's aggregate `Point`/`Fq` inputs flatten to 15).
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
        16,
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
        2,
        "blake2s_basic"
    );
    typed_fixture!(
        BLAKE3_BASIC_VK,
        BLAKE3_BASIC_PROOF,
        BLAKE3_BASIC_INPUTS,
        2,
        "blake3_basic"
    );
    typed_fixture!(
        CURVE_BASIC_VK,
        CURVE_BASIC_PROOF,
        CURVE_BASIC_INPUTS,
        12,
        "curve_basic"
    );
    typed_fixture!(
        SECP256K1_ECDSA_VK,
        SECP256K1_ECDSA_PROOF,
        SECP256K1_ECDSA_INPUTS,
        10,
        "secp256k1_ecdsa"
    );
    typed_fixture!(
        SECP256R1_ECDSA_VK,
        SECP256R1_ECDSA_PROOF,
        SECP256R1_ECDSA_INPUTS,
        10,
        "secp256r1_ecdsa"
    );
    typed_fixture!(
        KECCAK_BASIC_VK,
        KECCAK_BASIC_PROOF,
        KECCAK_BASIC_INPUTS,
        2,
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
        3,
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
        2,
        "sha256_basic"
    );
}
