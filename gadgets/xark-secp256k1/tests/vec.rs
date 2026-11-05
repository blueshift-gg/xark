//! Validate the secp256k1 ECDSA gadget against the `k256` reference crate: sign a
//! message with `k256`, feed the real `(q, r, s, e)` into `examples/secp256k1_ecdsa`,
//! and confirm the circuit accepts it — and rejects a tampered signature. The
//! cross-implementation guarantee sha256 gets from `sha2`, for ECDSA.
//!
//! The native `k256` values drive the circuit directly: `Point`/`Scalar` own the
//! byte → limb decomposition and the flatten leaf naming, and `Compiled::check`
//! resolves them against the compiled program — so the test reads like the sha256
//! example, with no hand-built limb maps or variable-id plumbing.

use k256::ecdsa::{
    Signature, SigningKey, VerifyingKey, signature::Signer, signature::hazmat::PrehashVerifier,
};
use k256::elliptic_curve::{PrimeField, point::AffineCoordinates};
use k256::{ProjectivePoint, Scalar as K};
use num_bigint::BigUint;
use sha2::{Digest, Sha256};
// The circuit takes the transparent compound types `Point` (pubkey), `Signature`
// (r‖s), `Scalar` (digest), all in the 2×128-bit leaf layout — mirror them with the
// harness's packed leaf types.
use xark_test_harness::bignum::{
    PointPacked as Point, ScalarPacked as Scalar, SignaturePacked as Sig, Uint256,
};

/// Release-mode 64-bit hints against `k256` (bug checklist 14): private keys `2`, `3`,
/// `n − 2`, `7`, `n − 7`, `2^128`, `2^255`, the six keys `±1`, `±(1+λ)/(1−λ)`,
/// `±(1−λ)/(1+λ)` and a generic one over two messages, each signature accepted, and the
/// same signature with `r` or `s` changed, or a digest off by one, rejected. No key is
/// refused; the refused set is the nonces `k ≡ μ·q` with `μ ∈ {±1, ±(1+λ)/(1−λ),
/// ±(1−λ)/(1+λ)}`, where `R = μ·Q` makes a table add `(Q ± φQ) ± (R ± φR)` meet
/// `x_P = x_T` (see `ecdsa_verify_packed`): such signatures `k256` accepts are refused.
#[test]
fn ecdsa_verify_matches_k256() {
    let n = BigUint::parse_bytes(
        b"fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141",
        16,
    )
    .unwrap();
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/secp256k1_ecdsa/src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "ecdsa_k256_vec", "bn254");
    assert!(
        c.status_success,
        "compiling secp256k1_ecdsa failed: {}",
        c.stderr
    );
    let key = |k: &BigUint| {
        let mut b = [0u8; 32];
        let be = k.to_bytes_be();
        b[32 - be.len()..].copy_from_slice(&be);
        SigningKey::from_slice(&b).unwrap()
    };
    let lam = BigUint::parse_bytes(
        b"5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72",
        16,
    )
    .unwrap();
    let ratio = |a: &BigUint, b: &BigUint| a * b.modpow(&(&n - 2u8), &n) % &n;
    let (pl, ml) = (1u8 + &lam, &n + 1u8 - &lam);
    let excluded = [BigUint::from(1u8), ratio(&pl, &ml), ratio(&ml, &pl)];
    let mut keys = vec![
        BigUint::from(2u8),
        BigUint::from(3u8),
        &n - 2u8,
        BigUint::from(7u8),
        &n - 7u8,
        BigUint::from(1u8) << 128u32,
        BigUint::from(1u8) << 255u32,
        BigUint::from_bytes_be(&[0x42u8; 32]),
    ];
    keys.extend(excluded.iter().flat_map(|q| [q.clone(), &n - q]));
    let msgs: [&[u8]; 2] = [b"xark secp256k1 ecdsa vector", b""];
    for sk in keys.iter().map(key) {
        for msg in msgs {
            let sig: Signature = sk.sign(msg);
            let pubkey = Point::from_sec1(sk.verifying_key().to_encoded_point(false).as_bytes());
            let sig_leaf = Sig::from_rs(sig.to_bytes().as_ref());
            let e = BigUint::from_bytes_be(&Sha256::digest(msg)) % &n;
            let digest = Scalar(Uint256::from(e.clone()));
            c.check(&[("pubkey", &pubkey), ("sig", &sig_leaf), ("digest", &digest)])
                .expect("a valid k256 ECDSA signature must verify");
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
    // A nonce `k ≡ μ·q` puts `R = kG = μ·Q`: k256 accepts the signature, the circuit refuses.
    let sc = |x: &BigUint| {
        let mut b = [0u8; 32];
        let be = x.to_bytes_be();
        b[32 - be.len()..].copy_from_slice(&be);
        K::from_repr(b.into()).unwrap()
    };
    let q = BigUint::from_bytes_be(&[0x42u8; 32]);
    let sk = key(&q);
    let vk = VerifyingKey::from(&sk);
    let pubkey = Point::from_sec1(vk.to_encoded_point(false).as_bytes());
    let h = Sha256::digest(b"xark secp256k1 ecdsa vector");
    let e = BigUint::from_bytes_be(&h) % &n;
    for mu in excluded.iter().flat_map(|m| [m.clone(), &n - m]) {
        let k = &mu * &q % &n;
        let xr = (ProjectivePoint::GENERATOR * sc(&k)).to_affine().x();
        let r = BigUint::from_bytes_be(&xr) % &n;
        let s = k.modpow(&(&n - 2u8), &n) * (&e + &r * &q) % &n;
        // A low `s` (k256's rule) flips `R` to `−μ·Q`, still in the set.
        let sig = Signature::from_scalars(sc(&r).to_repr(), sc(&s).to_repr()).unwrap();
        let sig = sig.normalize_s().unwrap_or(sig);
        vk.verify_prehash(&h, &sig)
            .expect("k256 accepts the signature");
        assert!(
            c.check(&[
                ("pubkey", &pubkey),
                ("sig", &Sig::from_rs(sig.to_bytes().as_ref())),
                ("digest", &Scalar(Uint256::from(e.clone()))),
            ])
            .is_err(),
            "a nonce with R = μ·Q must be refused by its table add"
        );
    }
}
