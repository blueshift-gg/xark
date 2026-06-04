//! Stability test for the EVM Solidity verifier exporter (WS-E.1).
//!
//! Reads the committed `arithmetic_square` verifying key fixture, runs the
//! exporter, and asserts:
//!
//! * Common Solidity boilerplate is present.
//! * The right number of IC entries are emitted.
//! * The `verifyProof` signature has arity `1` (matches the circuit's single
//!   public input).
//! * The SHA-256 of the generated string is pinned, so any silent template
//!   change shows up in CI.

use std::path::{Path, PathBuf};

use ark_bn254::Bn254;
use ark_groth16::VerifyingKey;
use sha2::{Digest, Sha256};

use groth16_backend::evm::export_verifier_solidity;
use groth16_backend::keys::Groth16Keys;

// Pinned hash of the generated Verifier.sol for the committed fixture. If
// the template intentionally changes, regenerate via the failure message and
// paste the new hash here.
const EXPORTED_SHA256: &str = "68ecfbf7675dd3dd4840170de7ae1b90cab1ae41f716a6407375a2c967cc73af";

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

fn load_vk() -> VerifyingKey<Bn254> {
    Groth16Keys::read_verifying_key(&fixture_dir().join("verifying_key.bin"))
        .expect("read fixture verifying_key.bin")
}

#[test]
fn exported_contract_has_expected_shape() {
    let vk = load_vk();
    let src = export_verifier_solidity(&vk).expect("export Solidity verifier");

    // Solidity boilerplate.
    assert!(src.contains("pragma solidity ^0.8.0;"), "pragma missing");
    assert!(src.contains("contract Verifier"), "contract missing");
    assert!(
        src.contains("library Pairing"),
        "Pairing helper library missing"
    );

    // Arithmetic-square has 1 public input → IC array length 2 (ic[0] + ic[1]).
    let ic_len = vk.gamma_abc_g1.len();
    assert_eq!(ic_len, 2, "fixture should have 2 IC entries");
    assert!(
        src.contains(&format!("Pairing.G1Point[{ic_len}] ic")),
        "expected IC array of length {ic_len}"
    );
    // Both IC assignments are present.
    assert!(src.contains("vk.ic[0] = Pairing.G1Point("));
    assert!(src.contains("vk.ic[1] = Pairing.G1Point("));
    // No bogus third entry.
    assert!(
        !src.contains("vk.ic[2] = Pairing.G1Point("),
        "spurious ic[2] entry emitted"
    );

    // Signature arity must match `gamma_abc_g1.len() - 1`.
    let expected_sig = format!("uint256[{}] memory inputs", ic_len - 1);
    assert!(
        src.contains(&expected_sig),
        "expected verifyProof signature with `{expected_sig}` — got:\n{src}"
    );
    assert!(
        src.contains("function verifyProof(") && src.contains("returns (bool)"),
        "verifyProof signature missing"
    );

    // The pairing precompile call must include all four pairs.
    assert!(
        src.contains("Pairing.G1Point[] memory p1 = new Pairing.G1Point[](4);"),
        "pairing input length must be 4"
    );

    // Sanity check: the contract should reference the precompile addresses
    // it depends on.
    assert!(
        src.contains("staticcall(sub(gas(), 2000), 6"),
        "G1 add precompile call missing"
    );
    assert!(
        src.contains("staticcall(sub(gas(), 2000), 7"),
        "G1 mul precompile call missing"
    );
    assert!(
        src.contains("staticcall(\n                sub(gas(), 2000),\n                8,"),
        "pairing precompile call missing"
    );
}

#[test]
fn exported_contract_sha256_is_pinned() {
    let vk = load_vk();
    let src = export_verifier_solidity(&vk).expect("export Solidity verifier");
    let actual = hex::encode(Sha256::digest(src.as_bytes()));
    assert_eq!(
        actual, EXPORTED_SHA256,
        "Verifier.sol SHA-256 changed (template edit?). Actual hash: {actual}"
    );
}

/// Set `XARK_DUMP_VERIFIER_SOL=/path/to/Verifier.sol` and run this test to
/// materialize the exported contract on disk for manual inspection. Mostly
/// useful as a sandbox-safe replacement for running the CLI binary.
#[test]
fn dump_exported_contract_on_request() {
    let Ok(path) = std::env::var("XARK_DUMP_VERIFIER_SOL") else {
        return;
    };
    let vk = load_vk();
    let src = export_verifier_solidity(&vk).expect("export Solidity verifier");
    std::fs::write(path, src).expect("write dump");
}

// Sandbox-friendly dump: unconditionally writes the exported contract to
// `target/tmp/Verifier.sol` so callers can inspect the artifact without
// needing to run the CLI binary directly. Kept here so we get one file
// per `cargo test` invocation.
#[test]
fn dump_exported_contract_to_target_tmp() {
    let vk = load_vk();
    let src = export_verifier_solidity(&vk).expect("export Solidity verifier");
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let out_dir = manifest
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .join("target")
        .join("tmp");
    std::fs::create_dir_all(&out_dir).expect("mkdir target/tmp");
    let path = out_dir.join("Verifier.sol");
    std::fs::write(&path, &src).expect("write dump");
    // Sanity: file exists and is non-empty.
    let meta = std::fs::metadata(&path).expect("stat dump");
    assert!(meta.len() > 0, "wrote empty Verifier.sol");
}

/// Dump the proof + public-inputs of the committed fixture to
/// `target/tmp/proof_fixture.txt` as Solidity-ready decimal literals so
/// `tests/evm/Verifier.t.sol` can hard-code the values. Run via
/// `cargo test -p groth16-backend --test evm_export dump_fixture_for_foundry`
/// any time you regenerate the fixture.
#[test]
fn dump_fixture_for_foundry() {
    use ark_bn254::Bn254 as _Bn254;
    use ark_bn254::{Fq2, G1Affine, G2Affine};
    use ark_ec::AffineRepr;
    use ark_groth16::Proof;
    use groth16_backend::proof::ProofBundle;
    use groth16_backend::serialization::PublicInputsJson;
    use num_bigint::BigUint;
    use std::fmt::Write as _;

    let dir = fixture_dir();
    let proof: Proof<_Bn254> = ProofBundle::read_proof(&dir.join("proof.bin")).expect("read proof");
    let public_inputs_bytes =
        std::fs::read(dir.join("public_inputs.json")).expect("read public_inputs.json");
    let pi_json: PublicInputsJson =
        serde_json::from_slice(&public_inputs_bytes).expect("parse public_inputs.json");

    fn fq_dec(x: &ark_bn254::Fq) -> String {
        let big: BigUint = (*x).into();
        big.to_str_radix(10)
    }

    fn g1_dec(p: &G1Affine) -> (String, String) {
        if p.is_zero() {
            ("0".into(), "0".into())
        } else {
            let (x, y) = p.xy().expect("g1 not at infinity");
            (fq_dec(&x), fq_dec(&y))
        }
    }

    fn g2_dec(p: &G2Affine) -> ((String, String), (String, String)) {
        if p.is_zero() {
            (("0".into(), "0".into()), ("0".into(), "0".into()))
        } else {
            let (x, y) = p.xy().expect("g2 not at infinity");
            let Fq2 { c0: x0, c1: x1 } = x;
            let Fq2 { c0: y0, c1: y1 } = y;
            // Solidity uses (c1, c0) order.
            ((fq_dec(&x1), fq_dec(&x0)), (fq_dec(&y1), fq_dec(&y0)))
        }
    }

    let (ax, ay) = g1_dec(&proof.a);
    let ((bx_c1, bx_c0), (by_c1, by_c0)) = g2_dec(&proof.b);
    let (cx, cy) = g1_dec(&proof.c);

    let mut out = String::new();
    let _ = writeln!(out, "// auto-generated by dump_fixture_for_foundry");
    let _ = writeln!(out, "uint256[2] memory a = [");
    let _ = writeln!(out, "    {ax},");
    let _ = writeln!(out, "    {ay}");
    let _ = writeln!(out, "];");
    let _ = writeln!(out, "uint256[2][2] memory b = [");
    let _ = writeln!(out, "    [");
    let _ = writeln!(out, "        {bx_c1},");
    let _ = writeln!(out, "        {bx_c0}");
    let _ = writeln!(out, "    ],");
    let _ = writeln!(out, "    [");
    let _ = writeln!(out, "        {by_c1},");
    let _ = writeln!(out, "        {by_c0}");
    let _ = writeln!(out, "    ]");
    let _ = writeln!(out, "];");
    let _ = writeln!(out, "uint256[2] memory c = [");
    let _ = writeln!(out, "    {cx},");
    let _ = writeln!(out, "    {cy}");
    let _ = writeln!(out, "];");
    let _ = writeln!(out, "// public inputs:");
    for input in &pi_json.inputs {
        let _ = writeln!(out, "//   {input}");
    }

    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let out_dir = manifest
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .join("target")
        .join("tmp");
    std::fs::create_dir_all(&out_dir).expect("mkdir");
    let path = out_dir.join("proof_fixture.txt");
    std::fs::write(&path, &out).expect("write fixture dump");
}
