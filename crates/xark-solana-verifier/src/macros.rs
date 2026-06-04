//! `xark_groth16_program!` — generates a complete Solana program from an
//! embedded VK.
//!
//! Usage in a downstream program crate:
//!
//! ```ignore
//! // your_program/src/lib.rs
//! xark_solana_verifier::xark_groth16_program! {
//!     vk: include_bytes!("vk.bin"),
//! }
//! ```
//!
//! That expansion declares:
//!
//! * `pub const VK_BYTES: &[u8]` — the raw embedded VK.
//! * `pub fn verify_payload<B: Bn128Backend>(instruction_data: &[u8]) -> Result<bool, VerifierError>`
//!   — backend-generic verifier that consumes
//!   `proof_bytes || public_inputs` from the instruction data and runs
//!   the pairing check against the embedded VK. Use this from host-side
//!   tests with a non-syscall backend.
//! * A pinocchio entrypoint compiled in only under
//!   `target_os = "solana"`. Calls `verify_payload::<SolanaBackend>` and
//!   maps `Ok(true)` → `Ok(())`, anything else → `InvalidInstructionData`.
//!
//! `vk` accepts any expression that evaluates to `&'static [u8]`, so
//! `include_bytes!`, a `const` byte array, or a `static` pulled from disk
//! at startup all work.

/// Generate a Solana program that verifies a Groth16 proof against an
/// embedded verifying key. See the module-level docs for usage.
#[macro_export]
macro_rules! xark_groth16_program {
    (vk: $vk:expr $(,)?) => {
        /// Raw bytes of the embedded verifying key. Use this from host-
        /// side test code that wants to call `verify_payload` directly.
        pub const VK_BYTES: &[u8] = $vk;

        /// Verify the proof + public inputs carried by instruction data
        /// against the embedded VK. Generic over the backend so tests
        /// can plug in an Arkworks impl.
        pub fn verify_payload<B: $crate::Bn128Backend>(
            instruction_data: &[u8],
        ) -> ::core::result::Result<bool, $crate::VerifierError> {
            $crate::verify_proof_only_with::<B>(VK_BYTES, instruction_data)
        }

        // Pinocchio entrypoint — only compiled when targeting Solana SBF.
        // Tests on the host compile without this so they can drive
        // `verify_payload` with a host-side backend.
        #[cfg(target_os = "solana")]
        ::pinocchio::entrypoint!(__xark_groth16_entry);

        #[cfg(target_os = "solana")]
        pub fn __xark_groth16_entry(
            _program_id: &::pinocchio::Address,
            _accounts: &mut [::pinocchio::AccountView],
            instruction_data: &[u8],
        ) -> ::pinocchio::ProgramResult {
            match verify_payload::<$crate::SolanaBackend>(instruction_data) {
                Ok(true) => Ok(()),
                _ => Err(::pinocchio::error::ProgramError::InvalidInstructionData),
            }
        }
    };
}

// =============================================================================
// Tests — exercise the macro both compile-time (`include_bytes!`) and
// runtime (`const` slice) on the host with the ArkBackend.
// =============================================================================

#[cfg(all(test, feature = "ark-backend"))]
mod tests {
    // The macro emits items at the call site's module scope, so we put it
    // in a fresh nested module so we don't have to worry about name
    // collisions with the existing host-side test helpers.
    //
    // We use a fixture VK assembled at runtime from the Arkworks
    // `VerifyingKey` instead of relying on a pre-existing `.bin` file —
    // the existing `tests/fixtures/groth16/arithmetic_square/verifying_key.solana.bin`
    // is the BE wire format; LE bytes are produced on the fly inside
    // the test below.

    // The `xark_groth16_program!` macro embeds the LE VK at compile
    // time via `include_bytes!`. The fixture is the literal output of
    // `xark export solana --endianness le` against the
    // arithmetic_square circuit — committed under `tests/fixtures/` so
    // this stays a genuine compile-time path, mirroring how downstream
    // users would invoke the macro on their own committed VK.
    crate::xark_groth16_program! {
        vk: include_bytes!(
            "../../../tests/fixtures/groth16/arithmetic_square/verifying_key.solana.bin"
        ),
    }

    use crate::ark_backend::ArkBackend;
    use crate::{
        verify_groth16_with, verify_proof_only_with, FR_BYTES, G1_BYTES, G2_BYTES, PROOF_BYTES,
        VK_FIXED_PREFIX_BYTES,
    };

    use ark_bn254::{Bn254, Fq, Fr, G1Affine, G2Affine};
    use ark_ec::AffineRepr;
    use ark_ff::{PrimeField, Zero};
    use ark_groth16::{Proof, VerifyingKey};
    use ark_serialize::{CanonicalDeserialize, Compress, Validate};
    use num_bigint::BigUint;
    use std::path::{Path, PathBuf};

    // -- LE encoding helpers ------------------------------------------------

    fn encode_fq_le(value: &Fq) -> [u8; 32] {
        let big: BigUint = (*value).into();
        let mut bytes = big.to_bytes_le();
        bytes.resize(32, 0);
        bytes.try_into().unwrap()
    }

    fn encode_fr_le(value: &Fr) -> [u8; FR_BYTES] {
        let big: BigUint = (*value).into();
        let mut bytes = big.to_bytes_le();
        bytes.resize(FR_BYTES, 0);
        bytes.try_into().unwrap()
    }

    fn encode_g1_le(p: &G1Affine) -> [u8; G1_BYTES] {
        let mut out = [0u8; G1_BYTES];
        if p.is_zero() {
            return out;
        }
        let (x, y) = p.xy().unwrap();
        out[..32].copy_from_slice(&encode_fq_le(&x));
        out[32..].copy_from_slice(&encode_fq_le(&y));
        out
    }

    fn encode_g2_le(p: &G2Affine) -> [u8; G2_BYTES] {
        let mut out = [0u8; G2_BYTES];
        if p.is_zero() {
            return out;
        }
        let (x, y) = p.xy().unwrap();
        // Solana LE wire format for Fq2: (c0, c1) per coord.
        out[0..32].copy_from_slice(&encode_fq_le(&x.c0));
        out[32..64].copy_from_slice(&encode_fq_le(&x.c1));
        out[64..96].copy_from_slice(&encode_fq_le(&y.c0));
        out[96..128].copy_from_slice(&encode_fq_le(&y.c1));
        out
    }

    fn negate_g1(p: &G1Affine) -> G1Affine {
        if p.is_zero() {
            return G1Affine::zero();
        }
        let (x, y) = p.xy().unwrap();
        G1Affine::new_unchecked(x, Fq::zero() - y)
    }

    // -- Fixture loading ----------------------------------------------------

    fn fixture_dir() -> PathBuf {
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        manifest
            .parent()
            .and_then(|p| p.parent())
            .expect("workspace root")
            .join("tests")
            .join("fixtures")
            .join("groth16")
            .join("arithmetic_square")
    }

    fn read_vk() -> VerifyingKey<Bn254> {
        let path = fixture_dir().join("verifying_key.bin");
        let bytes = std::fs::read(path).expect("read vk");
        VerifyingKey::<Bn254>::deserialize_with_mode(bytes.as_slice(), Compress::Yes, Validate::Yes)
            .expect("parse vk")
    }

    fn read_proof() -> Proof<Bn254> {
        let path = fixture_dir().join("proof.bin");
        let bytes = std::fs::read(path).expect("read proof");
        Proof::<Bn254>::deserialize_with_mode(bytes.as_slice(), Compress::Yes, Validate::Yes)
            .expect("parse proof")
    }

    fn read_public_inputs() -> Vec<Fr> {
        let path = fixture_dir().join("public_inputs.json");
        let json_bytes = std::fs::read(path).expect("read public_inputs.json");
        #[derive(serde::Deserialize)]
        struct Pi {
            inputs: Vec<String>,
        }
        let pi: Pi = serde_json::from_slice(&json_bytes).expect("parse public_inputs");
        pi.inputs
            .iter()
            .map(|s| {
                let big: BigUint = s.trim().parse().expect("decimal scalar");
                Fr::from_be_bytes_mod_order(&big.to_bytes_be())
            })
            .collect()
    }

    fn assemble_vk_le(vk: &VerifyingKey<Bn254>) -> Vec<u8> {
        let mut out =
            Vec::with_capacity(VK_FIXED_PREFIX_BYTES + 4 + vk.gamma_abc_g1.len() * G1_BYTES);
        out.extend_from_slice(&encode_g1_le(&vk.alpha_g1));
        out.extend_from_slice(&encode_g2_le(&vk.beta_g2));
        out.extend_from_slice(&encode_g2_le(&vk.gamma_g2));
        out.extend_from_slice(&encode_g2_le(&vk.delta_g2));
        out.extend_from_slice(&(vk.gamma_abc_g1.len() as u32).to_le_bytes());
        for ic in &vk.gamma_abc_g1 {
            out.extend_from_slice(&encode_g1_le(ic));
        }
        out
    }

    fn assemble_proof_le(proof: &Proof<Bn254>) -> Vec<u8> {
        let mut out = Vec::with_capacity(PROOF_BYTES);
        out.extend_from_slice(&encode_g1_le(&negate_g1(&proof.a)));
        out.extend_from_slice(&encode_g2_le(&proof.b));
        out.extend_from_slice(&encode_g1_le(&proof.c));
        out
    }

    fn assemble_public_inputs_le(inputs: &[Fr]) -> Vec<u8> {
        let mut out = Vec::with_capacity(inputs.len() * FR_BYTES);
        for f in inputs {
            out.extend_from_slice(&encode_fr_le(f));
        }
        out
    }

    fn assemble_instruction_data(proof_le: &[u8], pi_le: &[u8]) -> Vec<u8> {
        let mut data = Vec::with_capacity(proof_le.len() + pi_le.len());
        data.extend_from_slice(proof_le);
        data.extend_from_slice(pi_le);
        data
    }

    /// Exercise the macro-generated `verify_payload` against the
    /// build-time-embedded VK. Demonstrates the "include_bytes! a VK
    /// and you're done" path the macro is designed for.
    #[test]
    fn macro_embedded_vk_verifies_fixture() {
        let proof = read_proof();
        let inputs = read_public_inputs();

        let proof_le = assemble_proof_le(&proof);
        let pi_le = assemble_public_inputs_le(&inputs);
        let instruction_data = assemble_instruction_data(&proof_le, &pi_le);

        // Sanity-check the embedded VK matches the runtime-assembled one.
        let vk = read_vk();
        let vk_runtime = assemble_vk_le(&vk);
        assert_eq!(
            VK_BYTES, vk_runtime.as_slice(),
            "build.rs output must match runtime LE assembly"
        );

        let ok = verify_payload::<ArkBackend>(&instruction_data).expect("verify_payload");
        assert!(
            ok,
            "embedded VK + macro-generated verify_payload must accept the KAT proof"
        );
    }

    /// Same flow as the embedded path, but with the VK supplied at
    /// runtime via `verify_proof_only_with` — confirms both invocation
    /// styles share semantics.
    #[test]
    fn verify_proof_only_with_le_fixture() {
        let vk = read_vk();
        let proof = read_proof();
        let inputs = read_public_inputs();

        let vk_le = assemble_vk_le(&vk);
        let proof_le = assemble_proof_le(&proof);
        let pi_le = assemble_public_inputs_le(&inputs);
        let instruction_data = assemble_instruction_data(&proof_le, &pi_le);

        let ok =
            verify_proof_only_with::<ArkBackend>(&vk_le, &instruction_data).expect("verify");
        assert!(ok, "arithmetic_square fixture must verify with LE wire format");
    }

    /// Generic verifier path (separate vk + proof + inputs) still works.
    #[test]
    fn verify_groth16_with_le_fixture() {
        let vk = read_vk();
        let proof = read_proof();
        let inputs = read_public_inputs();

        let vk_le = assemble_vk_le(&vk);
        let proof_le = assemble_proof_le(&proof);
        let pi_le = assemble_public_inputs_le(&inputs);

        let ok =
            verify_groth16_with::<ArkBackend>(&vk_le, &proof_le, &pi_le).expect("verify");
        assert!(ok, "arithmetic_square fixture must verify with LE wire format");
    }

    /// Tampering with the public input flips the pairing check.
    #[test]
    fn tampered_input_le_fails() {
        let vk = read_vk();
        let proof = read_proof();
        let inputs = read_public_inputs();

        let vk_le = assemble_vk_le(&vk);
        let proof_le = assemble_proof_le(&proof);
        let mut pi_le = assemble_public_inputs_le(&inputs);
        // Flip the LE LSB — still a valid Fr.
        pi_le[0] ^= 0x01;
        let instruction_data = assemble_instruction_data(&proof_le, &pi_le);

        let ok =
            verify_proof_only_with::<ArkBackend>(&vk_le, &instruction_data).expect("verify");
        assert!(!ok, "tampered public input must fail the pairing");
    }
}
