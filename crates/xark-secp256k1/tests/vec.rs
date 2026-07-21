//! Validate the secp256k1 ECDSA gadget against the `k256` reference crate: sign a
//! message with `k256`, feed the real `(q, r, s, e)` into `examples/secp256k1_ecdsa`,
//! and confirm the circuit accepts it — and rejects a tampered signature. The
//! cross-implementation guarantee sha256 gets from `sha2`, for ECDSA.
//!
//! The native `k256` values drive the circuit directly: `Point`/`Scalar` own the
//! byte → limb decomposition and the flatten leaf naming, and `Compiled::check`
//! resolves them against the compiled program — so the test reads like the sha256
//! example, with no hand-built limb maps or variable-id plumbing.

use k256::ecdsa::{signature::Signer, Signature, SigningKey};
use num_bigint::BigUint;
use sha2::{Digest, Sha256};
// The circuit takes the transparent compound types `Point` (pubkey), `Signature`
// (r‖s), `Scalar` (digest), all in the 2×128-bit leaf layout — mirror them with the
// harness's packed leaf types.
use xark_test_harness::bignum::{
    PointPacked as Point, ScalarPacked as Scalar, SignaturePacked as Sig, Uint256,
};

#[test]
fn ecdsa_verify_matches_k256() {
    // Deterministic key + message → a real signature.
    let sk = SigningKey::from_slice(&[0x42u8; 32]).unwrap();
    let vk = sk.verifying_key();
    let msg = b"xark secp256k1 ecdsa vector";
    let sig: Signature = sk.sign(msg);

    // Native inputs, straight from the k256 wire encodings.
    let pubkey = Point::from_sec1(vk.to_encoded_point(false).as_bytes());
    let sig_leaf = Sig::from_rs(sig.to_bytes().as_slice());
    // ECDSA challenge e = int(SHA-256(msg)) mod n (n = secp256k1 group order).
    let n = BigUint::parse_bytes(
        b"fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141",
        16,
    )
    .unwrap();
    let digest = Scalar(Uint256::from(
        BigUint::from_bytes_be(&Sha256::digest(msg)) % &n,
    ));

    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/secp256k1_ecdsa/src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "ecdsa_k256_vec", "bn254");
    assert!(
        c.status_success,
        "compiling secp256k1_ecdsa failed: {}",
        c.stderr
    );

    // A genuine k256 signature satisfies the circuit (and it is fully constrained).
    c.check(&[("pubkey", &pubkey), ("sig", &sig_leaf), ("digest", &digest)])
        .expect("a valid k256 ECDSA signature must verify");

    // A tampered signature (wrong `r`) is rejected.
    let bad_sig = Sig {
        r: Uint256::from(1u128),
        s: sig_leaf.s.clone(),
    };
    assert!(
        c.check(&[("pubkey", &pubkey), ("sig", &bad_sig), ("digest", &digest)])
            .is_err(),
        "a tampered signature must be rejected"
    );
}
