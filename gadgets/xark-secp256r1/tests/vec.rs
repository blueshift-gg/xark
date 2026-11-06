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
use p256::ecdsa::{
    Signature, SigningKey, VerifyingKey, signature::Signer, signature::hazmat::PrehashVerifier,
};
use p256::elliptic_curve::{PrimeField, point::AffineCoordinates};
use p256::{ProjectivePoint, Scalar as K};
use sha2::{Digest, Sha256};
// The circuit takes the transparent compound types `Point` (pubkey), `Signature`
// (r‖s), `Scalar` (digest), all in the 2×128-bit leaf layout — mirror them with the
// `*Packed` harness types.
use xark_test_harness::bignum::{
    PointPacked as Point, ScalarPacked as Scalar, SignaturePacked as Sig, Uint256,
};

/// Release-mode hints against `p256` (bug checklist 14): private keys `1` (`Q = G`), `2`,
/// `3`, `n − 1`, `n − 2`, `2^128`, `2^255` and a generic one over two messages, each signature
/// accepted, and the same signature with `r` or `s` changed, or a digest off by one,
/// rejected. No key is refused; the refused set is the nonces `k ≡ ±q`, where `R = ±Q`
/// makes a table add `Q ± R` meet `x_Q = x_R` (see `ecdsa_verify`): such signatures `p256`
/// accepts are refused.
#[test]
fn ecdsa_verify_matches_p256() {
    let n = BigUint::parse_bytes(
        b"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        16,
    )
    .unwrap();
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/secp256r1_ecdsa/src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "ecdsa_p256_vec", "bn254");
    assert!(
        c.status_success,
        "compiling secp256r1_ecdsa failed: {}",
        c.stderr
    );
    let bytes = |k: &BigUint| {
        let mut b = [0u8; 32];
        let be = k.to_bytes_be();
        b[32 - be.len()..].copy_from_slice(&be);
        b
    };
    let key = |k: &BigUint| SigningKey::from_slice(&bytes(k)).unwrap();
    let keys = [
        BigUint::from(1u8),
        BigUint::from(2u8),
        BigUint::from(3u8),
        &n - 1u8,
        &n - 2u8,
        BigUint::from(1u8) << 128u32,
        BigUint::from(1u8) << 255u32,
        BigUint::from_bytes_be(&[0x42u8; 32]),
    ];
    let msgs: [&[u8]; 2] = [b"xark secp256r1 ecdsa vector", b""];
    for sk in keys.iter().map(key) {
        for msg in msgs {
            let sig: Signature = sk.sign(msg);
            let pubkey = Point::from_sec1(sk.verifying_key().to_sec1_point(false).as_bytes());
            let sig_leaf = Sig::from_rs(sig.to_bytes().as_ref());
            let e = BigUint::from_bytes_be(&Sha256::digest(msg)) % &n;
            let digest = Scalar(Uint256::from(e.clone()));
            c.check(&[("pubkey", &pubkey), ("sig", &sig_leaf), ("digest", &digest)])
                .expect("a valid p256 ECDSA signature must verify");
            let (r, s) = sig.split_scalars();
            let bump = |x: &[u8]| Uint256::from((BigUint::from_bytes_be(x) + 1u8) % &n);
            let bad_r = Sig {
                r: bump(&r.to_bytes()),
                s: sig_leaf.s.clone(),
            };
            let bad_s = Sig {
                r: sig_leaf.r.clone(),
                s: bump(&s.to_bytes()),
            };
            let bad_e = Scalar(Uint256::from((e + 1u8) % &n));
            for (sg, dg) in [(&bad_r, &digest), (&bad_s, &digest), (&sig_leaf, &bad_e)] {
                assert!(
                    c.check(&[("pubkey", &pubkey), ("sig", sg), ("digest", dg)])
                        .is_err(),
                    "a tampered signature must be rejected"
                );
            }
        }
    }
    // A nonce `k ≡ ±q` puts `R = kG = ±Q`: p256 accepts the signature, the circuit refuses.
    let sc = |x: &BigUint| K::from_repr(bytes(x).into()).unwrap();
    let q = BigUint::from_bytes_be(&[0x42u8; 32]);
    let sk = key(&q);
    let vk = VerifyingKey::from(&sk);
    let pubkey = Point::from_sec1(vk.to_sec1_point(false).as_bytes());
    let h = Sha256::digest(b"xark secp256r1 ecdsa vector");
    let e = BigUint::from_bytes_be(&h) % &n;
    for k in [q.clone(), &n - &q] {
        let xr = (ProjectivePoint::GENERATOR * sc(&k)).to_affine().x();
        let r = BigUint::from_bytes_be(&xr) % &n;
        let s = k.modpow(&(&n - 2u8), &n) * (&e + &r * &q) % &n;
        let sig = Signature::from_scalars(sc(&r).to_repr(), sc(&s).to_repr()).unwrap();
        vk.verify_prehash(&h, &sig)
            .expect("p256 accepts the signature");
        assert!(
            c.check(&[
                ("pubkey", &pubkey),
                ("sig", &Sig::from_rs(sig.to_bytes().as_ref())),
                ("digest", &Scalar(Uint256::from(e.clone()))),
            ])
            .is_err(),
            "a nonce with R = ±Q must be refused by its table add"
        );
    }
}
