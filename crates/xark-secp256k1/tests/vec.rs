//! Validate the secp256k1 ECDSA gadget against the `k256` reference crate: sign a
//! message with `k256`, feed the real `(q, r, s, e)` into `examples/ecdsa_basic`,
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
use xark_test_harness::bignum::{Point, Scalar};

#[test]
fn ecdsa_verify_matches_k256() {
    // Deterministic key + message → a real signature.
    let sk = SigningKey::from_slice(&[0x42u8; 32]).unwrap();
    let vk = sk.verifying_key();
    let msg = b"xark secp256k1 ecdsa vector";
    let sig: Signature = sk.sign(msg);

    // Native inputs, straight from the k256 wire encodings.
    let q = Point::from_sec1(vk.to_encoded_point(false).as_bytes());
    let sig_bytes = sig.to_bytes();
    let r = Scalar::from_bytes_be(&sig_bytes[..32]);
    let s = Scalar::from_bytes_be(&sig_bytes[32..]);
    // ECDSA challenge e = int(SHA-256(msg)) mod n (n = secp256k1 group order).
    let n = BigUint::parse_bytes(
        b"fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141",
        16,
    )
    .unwrap();
    let e = Scalar::from(BigUint::from_bytes_be(&Sha256::digest(msg)) % &n);

    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/ecdsa_basic/src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "ecdsa_k256_vec", "bn254");
    assert!(
        c.status_success,
        "compiling ecdsa_basic failed: {}",
        c.stderr
    );

    // A genuine k256 signature satisfies the circuit (and it is fully constrained).
    c.check(&[("q", &q), ("r", &r), ("s", &s), ("e", &e)])
        .expect("a valid k256 ECDSA signature must verify");

    // A tampered signature (any wrong `r`) is rejected.
    let bad_r = Scalar::from(1u128);
    assert!(
        c.check(&[("q", &q), ("r", &bad_r), ("s", &s), ("e", &e)])
            .is_err(),
        "a tampered signature must be rejected"
    );
}
