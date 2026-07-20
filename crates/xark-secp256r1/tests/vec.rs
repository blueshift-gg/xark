//! Validate the secp256r1 (NIST P-256) ECDSA gadget against the `p256` reference
//! crate: sign a message with `p256`, feed the real `(q, r, s, e)` into
//! `examples/secp256r1_ecdsa`, and confirm the circuit accepts it — and rejects a
//! tampered signature.
//!
//! Native `p256` values drive the circuit directly: `Point`/`Scalar` own the
//! byte → limb decomposition and the flatten leaf naming, and `Compiled::check`
//! resolves them against the compiled program — so the test reads like the sha256
//! example, with no hand-built limb maps or variable-id plumbing.

use num_bigint::BigUint;
use p256::ecdsa::{signature::Signer, Signature as P256Sig, SigningKey};
use sha2::{Digest, Sha256};
// The circuit takes the transparent compound types `Point` (pubkey), `Signature`
// (r‖s), `Scalar` (digest), all in the 2×128-bit leaf layout — mirror them with the
// `*Packed` harness types.
use xark_test_harness::bignum::{
    PointPacked as Point, ScalarPacked as Scalar, SignaturePacked as Sig, Uint256,
};

#[test]
fn ecdsa_verify_matches_p256() {
    let sk = SigningKey::from_slice(&[0x42u8; 32]).unwrap();
    let vk = sk.verifying_key();
    let msg = b"xark secp256r1 ecdsa vector";
    let sig: P256Sig = sk.sign(msg);

    // Native inputs, straight from the p256 wire encodings.
    let pubkey = Point::from_sec1(vk.to_encoded_point(false).as_bytes());
    let sig_leaf = Sig::from_rs(sig.to_bytes().as_slice());
    // ECDSA challenge e = int(SHA-256(msg)) mod n (n = P-256 group order).
    let n = BigUint::parse_bytes(
        b"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        16,
    )
    .unwrap();
    let digest = Scalar(Uint256::from(
        BigUint::from_bytes_be(&Sha256::digest(msg)) % &n,
    ));

    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/secp256r1_ecdsa/src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "ecdsa_p256_vec", "bn254");
    assert!(
        c.status_success,
        "compiling secp256r1_ecdsa failed: {}",
        c.stderr
    );

    // A genuine p256 signature satisfies the circuit (and it is fully constrained).
    c.check(&[("pubkey", &pubkey), ("sig", &sig_leaf), ("digest", &digest)])
        .expect("a valid p256 ECDSA signature must verify");

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
