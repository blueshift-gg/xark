//! Validate the Ed25519 EdDSA gadget end to end against `ed25519-dalek`: sign a
//! real message with a fixed-seed keypair, feed the public key `A`, signature
//! point `R`, scalar `S`, and challenge `k = SHA-512(R‖A‖M) mod L` into
//! `examples/ed25519`, and confirm the circuit accepts it and rejects a
//! tampered signature. Also pins the minimized constraint count.
//!
//! dalek does keygen + signing (the real cross-check) but its `EdwardsPoint`
//! deliberately never exposes affine `(x, y)` — so the one thing it won't hand us,
//! the `x` behind a compressed point, is recovered by the small [`decompress`]
//! below (`y` is just the compressed bytes; only `x` needs a square root).

use ed25519_dalek::{Signer, SigningKey};
use num_bigint::BigUint;
use sha2::{Digest, Sha512};
use xark_test_harness::bignum::{LeafInput, Point85, Scalar};

/// The ed25519 `Signature` compound: the point `R` (3×85) then the scalar `S`
/// (3×86), flattening to `sig.r.x.limbs` / `sig.r.y.limbs` / `sig.s.limbs`.
struct EddsaSig {
    r: Point85,
    s: Scalar,
}

impl LeafInput for EddsaSig {
    fn leaves(&self, prefix: &str) -> Vec<(String, String)> {
        let mut out = self.r.leaves(&format!("{prefix}.r"));
        out.extend(self.s.leaves(&format!("{prefix}.s")));
        out
    }
}

/// Recover the affine `(x, y)` of a 32-byte RFC-8032 compressed Edwards point.
/// `y` is the compressed bytes (LE, top bit cleared); `x` is the one value dalek
/// computes but hides — `x² = (y²−1)/(d·y²+1)`, `x = ·^((p+3)/8)` with the `√−1`
/// branch, sign-fixed from the top bit. All curve constants are local.
fn decompress(bytes: &[u8; 32]) -> Point85 {
    let p = (BigUint::from(1u8) << 255u32) - 19u8; // 2^255 − 19
    let d = BigUint::parse_bytes(
        b"37095705934669439343138083508754565189542113879843219016388785533085940283555",
        10,
    )
    .unwrap();
    let sqrt_m1 = BigUint::parse_bytes(
        b"19681161376707505956807079304988542015446066515923890162744021073123829784752",
        10,
    )
    .unwrap();

    let mut b = *bytes;
    let sign = b[31] >> 7;
    b[31] &= 0x7f;
    let y = BigUint::from_bytes_le(&b);
    let y2 = &y * &y % &p;
    let uv = (&y2 + &p - 1u8) * (&d * &y2 + 1u8).modpow(&(&p - 2u8), &p) % &p; // (y²−1)/(d·y²+1)
    let mut x = uv.modpow(&((&p + 3u8) / 8u8), &p);
    if &x * &x % &p != uv {
        x = x * &sqrt_m1 % &p;
    }
    assert_eq!(&x * &x % &p, uv, "not a valid compressed Edwards point");
    if &x % 2u8 != BigUint::from(sign) {
        x = &p - x;
    }
    Point85 {
        x: Scalar::from(x),
        y: Scalar::from(y),
    }
}

#[test]
fn eddsa_verify_matches_dalek() {
    let sk = SigningKey::from_bytes(&[0x42u8; 32]);
    let vk = sk.verifying_key();
    let msg = b"xark ed25519 eddsa vector";
    let sig = sk.sign(msg);

    let a_bytes = vk.to_bytes();
    let sig_bytes = sig.to_bytes();
    let r_bytes: [u8; 32] = sig_bytes[..32].try_into().unwrap();

    // A, R decompressed to affine; S is the low half of the signature; the
    // challenge k = SHA-512(R‖A‖M) mod L (L = the ed25519 group order).
    let a = decompress(&a_bytes);
    let r = decompress(&r_bytes);
    let s = Scalar::from_bytes_le(&sig_bytes[32..]);
    let mut h = Sha512::new();
    h.update(r_bytes);
    h.update(a_bytes);
    h.update(msg);
    let l = (BigUint::from(1u8) << 252u32)
        + BigUint::parse_bytes(b"27742317777372353535851937790883648493", 10).unwrap();
    let k = Scalar::from(BigUint::from_bytes_le(&h.finalize()) % l);

    let src =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/ed25519/src/lib.rs");
    let c = xark_test_harness::compile_file_xbc(&src, "ed25519", "bn254");
    assert!(c.status_success, "compiling ed25519 failed: {}", c.stderr);

    // Constraint-count regression pin (minimized R1CS, what the prover proves).
    // Sound lazy extended-coordinate path (was 4_554_355 affine).
    let n = c.minimized_r1cs_len();
    eprintln!("ed25519 eddsa_verify (lazy): {n} constraints");
    assert_eq!(
        n, 2_358_142,
        "ed25519 eddsa_verify constraint count changed"
    );

    // A genuine ed25519-dalek signature satisfies the circuit (fully constrained).
    let sig = EddsaSig {
        r: r.clone(),
        s: s.clone(),
    };
    c.check(&[("pubkey", &a), ("sig", &sig), ("digest", &k)])
        .expect("a valid ed25519-dalek signature must verify");

    // A tampered signature (any wrong `s`) is rejected.
    let bad_sig = EddsaSig {
        r: r.clone(),
        s: Scalar::from(1u128),
    };
    assert!(
        c.check(&[("pubkey", &a), ("sig", &bad_sig), ("digest", &k)])
            .is_err(),
        "a tampered signature must be rejected"
    );
}
