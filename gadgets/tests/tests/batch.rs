//! `verify_groth16_batch`: several proofs against one VK in one pairing call.
//!
//! The fixtures hold one proof per circuit; more valid proofs of the same
//! statement come from re-randomizing it (`A' = A/r`, `B' = r·B + r·s·δ`,
//! `C' = C + s·A`), so each batch entry is a distinct valid proof.

use ark_bn254::{Fr, G1Affine, G2Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField, UniformRand};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use xark_tests::{
    PAIRING_PAIR_BYTES, PROOF_BYTES, VerifierError, solana_nostd_alt_bn128::pairing_bytes,
    verify_groth16_batch, verify_proof_only,
};

/// `(vk, instruction_data)` of a committed fixture.
fn fixture(name: &str) -> (Vec<u8>, Vec<u8>) {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/groth16")
        .join(name);
    let read = |f: &str| std::fs::read(dir.join(f)).unwrap();
    (
        read("verifying_key.solana.bin"),
        read("instruction_data.bin"),
    )
}

fn g1(b: &[u8]) -> G1Affine {
    G1Affine::deserialize_uncompressed(b).unwrap()
}
fn g2(b: &[u8]) -> G2Affine {
    G2Affine::deserialize_uncompressed(b).unwrap()
}
/// A point's raw `x || y` coordinates: the wire format has no flag bits (ark's
/// point serialization would set them in `y`). The point at infinity is all zeros.
fn put<P: AffineRepr>(p: &P, out: &mut [u8]) {
    let Some((x, y)) = p.xy() else {
        out.fill(0);
        return;
    };
    let half = out.len() / 2;
    x.serialize_uncompressed(&mut out[..half]).unwrap();
    y.serialize_uncompressed(&mut out[half..]).unwrap();
}

/// A different valid proof of the same statement (`ix` = proof || inputs).
/// The wire `A` is pre-negated, so `A'_wire = A_wire / r` and `C' = C - s·A_wire`.
fn rerandomize(vk: &[u8], ix: &[u8], rng: &mut ChaCha20Rng) -> Vec<u8> {
    let (r, s) = (Fr::rand(rng), Fr::rand(rng));
    let delta = g2(&vk[64 + 2 * 128..64 + 3 * 128]);
    let (a, b, c) = (g1(&ix[..64]), g2(&ix[64..192]), g1(&ix[192..256]));
    let mut out = ix.to_vec();
    put(&(a * r.inverse().unwrap()).into_affine(), &mut out[..64]);
    put(&(b * r + delta * (r * s)).into_affine(), &mut out[64..192]);
    put(&(c.into_group() - a * s).into_affine(), &mut out[192..256]);
    out
}

/// `n` distinct valid proofs of `name`'s statement, concatenated.
fn valid_batch(name: &str, n: usize, seed: u64) -> (Vec<u8>, Vec<u8>) {
    let (vk, ix) = fixture(name);
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let batch = (0..n)
        .flat_map(|_| rerandomize(&vk, &ix, &mut rng))
        .collect();
    (vk, batch)
}

fn batch_verify(vk: &[u8], batch: &[u8], n: usize) -> Result<bool, VerifierError> {
    verify_groth16_batch(vk, batch, &mut vec![[0u8; PAIRING_PAIR_BYTES]; n + 3])
}

#[test]
fn rerandomized_proofs_verify_alone() {
    let (vk, batch) = valid_batch("arithmetic_square", 3, 1);
    for e in batch.chunks(batch.len() / 3) {
        assert_eq!(verify_proof_only(&vk, e), Ok(true));
    }
}

#[test]
fn valid_batches_verify() {
    for (name, n) in [
        ("arithmetic_square", 1),
        ("arithmetic_square", 2),
        ("arithmetic_square", 7),
        ("large_pi", 3),
        ("mixed_pi", 4),
        ("secp256k1_ecdsa", 2),
    ] {
        let (vk, batch) = valid_batch(name, n, n as u64);
        assert_eq!(batch_verify(&vk, &batch, n), Ok(true), "{name} x{n}");
    }
}

/// One wrong public input anywhere fails the whole batch.
#[test]
fn one_bad_proof_fails_the_batch() {
    let n = 5;
    let (vk, batch) = valid_batch("arithmetic_square", n, 9);
    let entry = batch.len() / n;
    for i in 0..n {
        let mut bad = batch.clone();
        bad[i * entry + PROOF_BYTES] ^= 1; // a public input, still canonical
        assert_eq!(batch_verify(&vk, &bad, n), Ok(false), "bad proof #{i}");
    }
}

/// Two invalid proofs whose errors cancel, `C + D` and `C - D`: an unweighted
/// product of their checks is 1 (the attack the weights stop), the batch isn't.
#[test]
fn cancelling_invalid_proofs_fail() {
    let (vk, ix) = fixture("arithmetic_square");
    let d = (G1Affine::generator() * Fr::from(12345u64)).into_affine();
    let c = g1(&ix[192..256]);
    let (mut p1, mut p2) = (ix.clone(), ix.clone());
    put(&(c + d).into_affine(), &mut p1[192..256]);
    put(&(c.into_group() - d).into_affine(), &mut p2[192..256]);
    assert_eq!(verify_proof_only(&vk, &p1), Ok(false));
    assert_eq!(verify_proof_only(&vk, &p2), Ok(false));

    // Unweighted: both proofs' four pairs in one product, with
    // vk_x = ic[0] + x·ic[1] for the single public input x.
    let ic = |k: usize| g1(&vk[448 + 64 * k..448 + 64 * (k + 1)]);
    let x = Fr::from_le_bytes_mod_order(&ix[PROOF_BYTES..]);
    let vk_x = (ic(0) + ic(1) * x).into_affine();
    let mut pairs = Vec::new();
    for p in [&p1, &p2] {
        let mut x = [0u8; 64];
        put(&vk_x, &mut x);
        for (a, b) in [
            (&p[..64], &p[64..192]),
            (&vk[..64], &vk[64..192]),
            (&x[..], &vk[192..320]),
            (&p[192..256], &vk[320..448]),
        ] {
            pairs.extend_from_slice(a);
            pairs.extend_from_slice(b);
        }
    }
    assert_eq!(
        pairing_bytes(&pairs).unwrap()[0],
        1,
        "unweighted product passes"
    );

    let batch = [p1, p2].concat();
    assert_eq!(batch_verify(&vk, &batch, 2), Ok(false));
}

#[test]
fn malformed_batches_are_rejected() {
    let (vk, batch) = valid_batch("arithmetic_square", 2, 3);
    let entry = PROOF_BYTES + 32;
    assert_eq!(
        batch_verify(&vk, &[], 1),
        Err(VerifierError::BatchLength { entry, actual: 0 })
    );
    assert_eq!(
        batch_verify(&vk, &batch[..batch.len() - 1], 2),
        Err(VerifierError::BatchLength {
            entry,
            actual: batch.len() - 1
        })
    );
    let mut small = vec![[0u8; PAIRING_PAIR_BYTES]; 2 + 3 - 1];
    assert_eq!(
        verify_groth16_batch(&vk, &batch, &mut small),
        Err(VerifierError::ScratchTooSmall {
            expected: 2 + 3,
            actual: 2 + 3 - 1
        })
    );
    // Strict: a masked top bit in a proof coordinate, or in the VK.
    let mut bad = batch.clone();
    bad[entry + 63] |= 0x80;
    assert_eq!(
        batch_verify(&vk, &bad, 2),
        Err(VerifierError::NonCanonicalCoordinate)
    );
    let mut bad_vk = vk.clone();
    bad_vk[31] |= 0x80;
    assert_eq!(
        batch_verify(&bad_vk, &batch, 2),
        Err(VerifierError::NonCanonicalCoordinate)
    );
    // A non-canonical public input in the second entry (`r` itself).
    let mut bad = batch.clone();
    let r_le =
        hex::decode("010000f093f5e1439170b97948e833285d588181b64550b829a031e1724e6430").unwrap();
    bad[entry + PROOF_BYTES..2 * entry].copy_from_slice(&r_le);
    assert_eq!(
        batch_verify(&vk, &bad, 2),
        Err(VerifierError::NonCanonicalPublicInput { index: 0 })
    );
}

/// The batch answers exactly what verifying each proof would, over random mixes
/// of valid and tampered entries.
#[test]
fn batch_agrees_with_single_verification() {
    let mut rng = ChaCha20Rng::seed_from_u64(42);
    let (vk, ix) = fixture("mixed_pi");
    let entry = ix.len();
    for round in 0..20 {
        let n = 1 + round % 6;
        let mut batch: Vec<u8> = (0..n)
            .flat_map(|_| rerandomize(&vk, &ix, &mut rng))
            .collect();
        if round % 3 != 0 {
            let i = (round * 7) % n;
            batch[i * entry + 200] ^= 1 << (round % 8); // somewhere in C
        }
        let each: Result<Vec<bool>, _> = batch
            .chunks(entry)
            .map(|e| verify_proof_only(&vk, e))
            .collect();
        let want = each.map(|v| v.iter().all(|&ok| ok));
        let got = batch_verify(&vk, &batch, n);
        // A flipped bit can leave C off the curve: both report the error then.
        match (&want, &got) {
            (Ok(w), Ok(g)) => assert_eq!(w, g, "round {round}"),
            (Err(_), Err(_)) => {}
            _ => panic!("round {round}: single {want:?}, batch {got:?}"),
        }
    }
}

/// The committed batch fixture the on-chain tests use (`tests/sbpf.rs`): 16
/// distinct valid proofs of `arithmetic_square`. Rewrite it with
/// `REGEN_FIXTURES=1`.
#[test]
fn batch_fixture_is_16_distinct_valid_proofs() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/groth16/arithmetic_square/batch16.bin");
    if std::env::var_os("REGEN_FIXTURES").is_some() {
        std::fs::write(&path, valid_batch("arithmetic_square", 16, 2026).1).unwrap();
    }
    let (vk, ix) = fixture("arithmetic_square");
    let batch = std::fs::read(&path).unwrap();
    let entries: Vec<&[u8]> = batch.chunks(ix.len()).collect();
    assert_eq!(entries.len(), 16);
    for (i, e) in entries.iter().enumerate() {
        assert_eq!(
            xark_tests::verify_proof_only_strict(&vk, e),
            Ok(true),
            "#{i}"
        );
        assert!(entries[..i].iter().all(|p| p != e), "#{i} repeats");
    }
    assert_eq!(batch_verify(&vk, &batch, 16), Ok(true));
}

/// Proof 0 carries no weight (`r₀ = 1`): a tampered `A` there still fails.
#[test]
fn tampered_first_proof_fails() {
    let (vk, batch) = valid_batch("arithmetic_square", 3, 21);
    let mut bad = batch.clone();
    let a = g1(&bad[..64]);
    put(&(a + G1Affine::generator()).into_affine(), &mut bad[..64]);
    assert_eq!(verify_proof_only(&vk, &bad[..batch.len() / 3]), Ok(false));
    assert_eq!(batch_verify(&vk, &bad, 3), Ok(false));
}

/// A circuit with no public inputs (256-byte entries), from a synthetic VK with a
/// known trapdoor: α = a·G₁, β = b·G₂, γ = δ = G₂, ic₀ = k·G₁, and the proof
/// `(A, B, C) = (x·G₁, G₂, (x - ab - k)·G₁)` for any `x`.
#[test]
fn zero_input_circuit_batches() {
    use ark_bn254::{G1Projective, G2Projective};
    use ark_ec::PrimeGroup;
    let (g1g, g2g) = (G1Projective::generator(), G2Projective::generator());
    let (a, b, k) = (Fr::from(3u64), Fr::from(5u64), Fr::from(7u64));
    let mut vk = vec![0u8; 448 + 64];
    put(&(g1g * a).into_affine(), &mut vk[..64]);
    put(&(g2g * b).into_affine(), &mut vk[64..192]);
    put(&g2g.into_affine(), &mut vk[192..320]);
    put(&g2g.into_affine(), &mut vk[320..448]);
    put(&(g1g * k).into_affine(), &mut vk[448..]);
    let proof = |x: u64, valid: bool| {
        let x = Fr::from(x);
        let mut p = vec![0u8; PROOF_BYTES];
        put(&(-(g1g * x)).into_affine(), &mut p[..64]); // the wire `A` is negated
        put(&g2g.into_affine(), &mut p[64..192]);
        let c = x - a * b - k + Fr::from(!valid as u64);
        put(&(g1g * c).into_affine(), &mut p[192..]);
        p
    };
    assert_eq!(verify_proof_only(&vk, &proof(11, true)), Ok(true));
    assert_eq!(verify_proof_only(&vk, &proof(11, false)), Ok(false));
    assert_eq!(batch_verify(&vk, &proof(11, true), 1), Ok(true));
    assert_eq!(batch_verify(&vk, &proof(11, false), 1), Ok(false));
    let good: Vec<_> = (11..14).map(|x| proof(x, true)).collect();
    assert_eq!(batch_verify(&vk, &good.concat(), 3), Ok(true));
    for j in 0..3 {
        let mut v = good.clone();
        v[j] = proof(20 + j as u64, false);
        assert_eq!(batch_verify(&vk, &v.concat(), 3), Ok(false), "bad #{j}");
    }
    // The same invalid proof twice can't cancel itself.
    assert_eq!(
        batch_verify(&vk, &[proof(11, false), proof(11, false)].concat(), 2),
        Ok(false)
    );
}
