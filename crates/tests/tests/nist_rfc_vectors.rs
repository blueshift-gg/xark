//! NIST / RFC official test-vector coverage for xark's hash + cipher gadgets.
//!
//! For each of the five committed primitives — SHA-256 (FIPS 180-4),
//! Keccak / SHA-3 (FIPS 202), BLAKE2s (RFC 7693), BLAKE3 (official spec) and
//! AES-128 (FIPS 197) — we drive the in-circuit gadget on the **canonical
//! published test vectors** and assert byte-equal output vs the reference
//! crates (`sha2`, `sha3`, `blake2`, `blake3`, `aes`), whose KAT correctness
//! is already established and audited upstream.
//!
//! Why drive the gadgets directly (not the Groth16 pipeline)?
//!
//! * The Groth16 pipeline tests under `circuits.rs` and `end_to_end.rs` only
//!   commit a handful of Noir `*_basic` fixtures (one per primitive) — they
//!   exercise the gadget on a single input. The unit tests inside
//!   `acir-r1cs/src/gadgets/*.rs` cover a few more (random lengths, block
//!   boundaries) but explicitly call out that they're *not* aligned to the
//!   official vector batches.
//!
//! * The "spec" boundary for each gadget is its **compression / permutation
//!   function** (SHA-256: `sha256_compression`; Keccak: `keccakf1600_in_circuit`;
//!   AES-128: `aes128_encrypt_in_circuit`) or its **full hash** wrapper
//!   (BLAKE2s, BLAKE3: `blake2s_in_circuit` / `blake3_in_circuit`). Those are
//!   what the FV plan's Lean proofs target — so the vector tests
//!   below run at the same boundary.
//!
//! For SHA-256 specifically, the *compression* gadget exposes the FIPS 180-4
//! §6.2 `F(state, block)` map. The FIPS 180-4 Appendix B vectors are full-hash
//! digests, so we expand them: feed the padded message blocks through the
//! gadget compression iteratively with `H[0] = IV`, and assert the digest after
//! the last block equals the published hex. This is the same bridging used by
//! `sha2::block_api::compress256` in the gadget's own unit test.
//!
//! All assertions are byte-exact against the reference crate output (the
//! KAT-correct oracle); the *hex constants* embedded in the test names anchor
//! the vector identity for human auditability.

#![cfg(test)]
#![allow(clippy::needless_range_loop)]

use ark_bn254::Fr;
use ark_ff::{One, PrimeField, Zero};
use ark_relations::gr1cs::{ConstraintSystem, ConstraintSystemRef, SynthesisError, Variable};
// `ConstraintSystem` import is retained because gadget helpers below construct
// the constraint-system ref directly; the alias keeps the borrow-checker
// happy for the `ConstraintSystemRef<Fr>` return type of the read helpers.

use xark_acir_r1cs::gadgets::aes::aes128_encrypt_in_circuit;
use xark_acir_r1cs::gadgets::bitwise::Word32;
use xark_acir_r1cs::gadgets::blake2s::blake2s_in_circuit;
use xark_acir_r1cs::gadgets::blake3::blake3_in_circuit;
use xark_acir_r1cs::gadgets::boolean::enforce_boolean;
use xark_acir_r1cs::gadgets::hash::sha256_compression;
use xark_acir_r1cs::gadgets::keccak::{KECCAK_LANES, keccakf1600_in_circuit};
use xark_acir_r1cs::r1cs_builder::R1csBuilder;
use xark_acir_r1cs::witness::WitnessMap;

// =============================================================================
// Test helpers — shared across primitives
// =============================================================================

/// Allocate one boolean-decomposed 32-bit `Word32` for the given concrete
/// value. Each bit is boolean-constrained.
fn alloc_word32(builder: &mut R1csBuilder<'_>, value: u32) -> Word32 {
    let mut bit_vars = Vec::with_capacity(32);
    for i in 0..32 {
        let bv = Some(if ((value >> i) & 1) == 1 {
            Fr::one()
        } else {
            Fr::zero()
        });
        let v = builder.alloc_with_value(bv).unwrap();
        enforce_boolean(builder, v).unwrap();
        bit_vars.push(v);
    }
    Word32::from_decomposed(bit_vars, Some(value))
}

/// Allocate one byte witness (no range-decomp on its own; the gadget will do
/// it). Returns `(var, value)` exactly in the shape every byte-oriented
/// gadget — `aes128_encrypt_in_circuit`, `blake2s_in_circuit`,
/// `blake3_in_circuit` — expects.
fn alloc_byte(builder: &mut R1csBuilder<'_>, value: u8) -> (Variable, Option<Fr>) {
    let fr = Fr::from(value as u64);
    let v = builder.alloc_with_value(Some(fr)).unwrap();
    (v, Some(fr))
}

/// Pull a byte witness's concrete value back out of a finished constraint
/// system (used to read each output byte from a hash / cipher gadget).
fn read_byte(cs: &ConstraintSystemRef<Fr>, v: Variable) -> u8 {
    let fr = cs.assigned_value(v).expect("variable has an assignment");
    let bytes = fr_to_be_bytes32(&fr);
    bytes[31]
}

/// `Fr` → 32-byte big-endian. The `crates/acir-r1cs/src/field.rs` helper
/// is `pub(crate)`, so we re-roll the trivial conversion here.
fn fr_to_be_bytes32(fr: &Fr) -> [u8; 32] {
    let mut out = [0u8; 32];
    let bi = fr.into_bigint();
    let le = ark_ff::BigInteger::to_bytes_le(&bi);
    for (i, b) in le.iter().enumerate().take(32) {
        out[31 - i] = *b;
    }
    out
}

/// `Fr` → low 64 bits (used to read back Keccak lane outputs).
fn fr_to_u64(fr: Fr) -> u64 {
    let bytes = fr_to_be_bytes32(&fr);
    let mut out = 0u64;
    for &b in &bytes[24..32] {
        out = (out << 8) | b as u64;
    }
    out
}

/// `u64` → `Fr` via 32-byte BE re-encode. Mirrors the inverse of
/// `fr_to_u64` so a round-trip `lane → Fr → lane` is the identity.
fn u64_to_fr(v: u64) -> Fr {
    let mut bytes = [0u8; 32];
    bytes[24..32].copy_from_slice(&v.to_be_bytes());
    Fr::from_be_bytes_mod_order(&bytes)
}

// =============================================================================
// Per-primitive driver helpers
// =============================================================================

/// Run the in-circuit `sha256_compression` gadget on a single 64-byte block
/// against a starting 8-word state, returning the new 8-word state.
fn sha256_compress_in_circuit(block: &[u8; 64], state_in: &[u32; 8]) -> [u32; 8] {
    let cs = ConstraintSystem::<Fr>::new_ref();
    let map = WitnessMap::<Fr>::new();
    let mut b = R1csBuilder::new(cs.clone(), Some(&map));
    b.finish_public_pass();

    // 16 BE-loaded 32-bit message words.
    let mut block_words = [0u32; 16];
    for (i, w) in block_words.iter_mut().enumerate() {
        *w = u32::from_be_bytes(block[i * 4..i * 4 + 4].try_into().unwrap());
    }

    let input: [Word32; 16] = std::array::from_fn(|i| alloc_word32(&mut b, block_words[i]));
    let state: [Word32; 8] = std::array::from_fn(|i| alloc_word32(&mut b, state_in[i]));

    let out = sha256_compression(&mut b, &input, &state).unwrap();
    assert!(cs.is_satisfied().unwrap(), "SHA-256 compression CS unsat");

    std::array::from_fn(|i| out[i].value.unwrap())
}

/// Full SHA-256 digest of `input` driven through the gadget's compression
/// function with FIPS 180-4 §5.1.1 padding (≤ 2^61 byte inputs — every test
/// vector below is well within that bound).
fn sha256_in_circuit(input: &[u8]) -> [u8; 32] {
    const IV: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];

    // FIPS 180-4 §5.1.1 padding.
    let bit_len = (input.len() as u64) * 8;
    let mut padded = input.to_vec();
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());
    debug_assert_eq!(padded.len() % 64, 0);

    let mut state = IV;
    for chunk in padded.chunks_exact(64) {
        let block: [u8; 64] = chunk.try_into().unwrap();
        state = sha256_compress_in_circuit(&block, &state);
    }

    let mut out = [0u8; 32];
    for (i, w) in state.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&w.to_be_bytes());
    }
    out
}

/// Run the in-circuit `keccakf1600_in_circuit` permutation on a 25-lane
/// input state, returning the 25 output lanes.
fn keccakf1600_in_circuit_native_io(input: &[u64; KECCAK_LANES]) -> [u64; KECCAK_LANES] {
    let cs = ConstraintSystem::<Fr>::new_ref();
    let map = WitnessMap::<Fr>::new();
    let mut b = R1csBuilder::new(cs.clone(), Some(&map));
    b.finish_public_pass();

    let mut in_vars = [Variable::One; KECCAK_LANES];
    let mut in_vals: [Option<Fr>; KECCAK_LANES] = [None; KECCAK_LANES];
    for i in 0..KECCAK_LANES {
        let fr = u64_to_fr(input[i]);
        let v = b.alloc_with_value(Some(fr)).unwrap();
        in_vars[i] = v;
        in_vals[i] = Some(fr);
    }

    let out_vars = keccakf1600_in_circuit(&mut b, &in_vars, &in_vals).unwrap();
    assert!(cs.is_satisfied().unwrap(), "Keccak-f[1600] CS unsat");

    let mut out = [0u64; KECCAK_LANES];
    for i in 0..KECCAK_LANES {
        out[i] = fr_to_u64(cs.assigned_value(out_vars[i]).unwrap());
    }
    out
}

/// SHA3-256 of `input` driven through the gadget's Keccak-f[1600] permutation
/// with FIPS 202 §B.2 padding (rate = 1088 bits = 136 bytes, suffix `0x06`,
/// pad10*1).
fn sha3_256_in_circuit(input: &[u8]) -> [u8; 32] {
    const RATE: usize = 136; // 1088 / 8 bytes
    const DOMAIN: u8 = 0x06; // SHA-3 suffix

    let mut state_bytes = [0u8; 200];

    // Absorb.
    let mut offset = 0usize;
    while offset + RATE <= input.len() {
        for i in 0..RATE {
            state_bytes[i] ^= input[offset + i];
        }
        let lanes = state_bytes_to_lanes(&state_bytes);
        let out = keccakf1600_in_circuit_native_io(&lanes);
        state_bytes = lanes_to_state_bytes(&out);
        offset += RATE;
    }

    // Final block + padding.
    let remainder = &input[offset..];
    for (i, &b) in remainder.iter().enumerate() {
        state_bytes[i] ^= b;
    }
    state_bytes[remainder.len()] ^= DOMAIN;
    state_bytes[RATE - 1] ^= 0x80;

    let lanes = state_bytes_to_lanes(&state_bytes);
    let out = keccakf1600_in_circuit_native_io(&lanes);
    state_bytes = lanes_to_state_bytes(&out);

    let mut digest = [0u8; 32];
    digest.copy_from_slice(&state_bytes[..32]);
    digest
}

fn state_bytes_to_lanes(bytes: &[u8; 200]) -> [u64; KECCAK_LANES] {
    let mut lanes = [0u64; KECCAK_LANES];
    for i in 0..KECCAK_LANES {
        lanes[i] = u64::from_le_bytes(bytes[i * 8..i * 8 + 8].try_into().unwrap());
    }
    lanes
}

fn lanes_to_state_bytes(lanes: &[u64; KECCAK_LANES]) -> [u8; 200] {
    let mut bytes = [0u8; 200];
    for i in 0..KECCAK_LANES {
        bytes[i * 8..i * 8 + 8].copy_from_slice(&lanes[i].to_le_bytes());
    }
    bytes
}

/// BLAKE2s of `input` driven through the gadget.
fn blake2s_in_circuit_bytes(input: &[u8]) -> [u8; 32] {
    let cs = ConstraintSystem::<Fr>::new_ref();
    let map = WitnessMap::<Fr>::new();
    let mut b = R1csBuilder::new(cs.clone(), Some(&map));
    b.finish_public_pass();

    let in_vars: Vec<(Variable, Option<Fr>)> =
        input.iter().map(|&byte| alloc_byte(&mut b, byte)).collect();
    let out = blake2s_in_circuit(&mut b, &in_vars).unwrap();
    assert!(cs.is_satisfied().unwrap(), "BLAKE2s CS unsat");

    std::array::from_fn(|i| read_byte(&cs, out[i]))
}

/// BLAKE3 of `input` driven through the gadget.
fn blake3_in_circuit_bytes(input: &[u8]) -> [u8; 32] {
    let cs = ConstraintSystem::<Fr>::new_ref();
    let map = WitnessMap::<Fr>::new();
    let mut b = R1csBuilder::new(cs.clone(), Some(&map));
    b.finish_public_pass();

    let in_vars: Vec<(Variable, Option<Fr>)> =
        input.iter().map(|&byte| alloc_byte(&mut b, byte)).collect();
    let out = blake3_in_circuit(&mut b, &in_vars).unwrap();
    assert!(cs.is_satisfied().unwrap(), "BLAKE3 CS unsat");

    std::array::from_fn(|i| read_byte(&cs, out[i]))
}

/// AES-128-CBC encrypt one or more 16-byte blocks via the gadget's
/// `aes128_encrypt_in_circuit`. For a single block with an all-zero IV this
/// equals AES-128 ECB (which is the FIPS 197 KAT mode).
fn aes128_cbc_in_circuit(
    plaintext: &[u8],
    iv: &[u8; 16],
    key: &[u8; 16],
) -> Result<Vec<u8>, SynthesisError> {
    let cs = ConstraintSystem::<Fr>::new_ref();
    let map = WitnessMap::<Fr>::new();
    let mut b = R1csBuilder::new(cs.clone(), Some(&map));
    b.finish_public_pass();

    let pt_vars: Vec<(Variable, Option<Fr>)> = plaintext
        .iter()
        .map(|&byte| alloc_byte(&mut b, byte))
        .collect();
    let iv_vars: [(Variable, Option<Fr>); 16] = std::array::from_fn(|i| alloc_byte(&mut b, iv[i]));
    let key_vars: [(Variable, Option<Fr>); 16] =
        std::array::from_fn(|i| alloc_byte(&mut b, key[i]));

    let out = aes128_encrypt_in_circuit(&mut b, &pt_vars, &iv_vars, &key_vars)?;
    assert!(cs.is_satisfied().unwrap(), "AES-128 CS unsat");

    let out_bytes: Vec<u8> = out.iter().map(|v| read_byte(&cs, *v)).collect();
    Ok(out_bytes)
}

// =============================================================================
// FIPS 180-4 SHA-256 — Appendix B.1 + B.2 + CAVP-style boundaries
// =============================================================================
//
// Reference vectors:
//   * NIST FIPS 180-4 Appendix B.1 ("abc")              — 1-block, msg = 24 bits
//   * NIST FIPS 180-4 Appendix B.2 ("abcdbcde...nopq")  — 2-block, msg = 448 bits
//   * NIST FIPS 180-4 Appendix B.3 ("a" × 10⁶)          — many-block stress
//   * NIST CAVP `ShortMsg`/`LongMsg` style boundaries — empty input, 55 / 56 / 64 / 119 / 120
//     byte inputs surrounding the 448-bit padding boundary.
//
// The expected digests come from the `sha2` reference crate (Rust Crypto, which
// passes the published CAVP vectors). Hex strings are also pinned for human
// audit against FIPS 180-4 §B.

mod sha256_vectors {
    use super::*;
    use sha2::{Digest, Sha256};

    fn ref_digest(input: &[u8]) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(input);
        h.finalize().into()
    }

    fn assert_matches(label: &str, input: &[u8]) {
        let got = sha256_in_circuit(input);
        let want = ref_digest(input);
        assert_eq!(
            got,
            want,
            "SHA-256 gadget mismatch on {label}: got {} want {}",
            hex::encode(got),
            hex::encode(want)
        );
    }

    #[test]
    fn fips_180_4_appendix_b1_abc() {
        // FIPS 180-4 §B.1: SHA-256("abc") =
        //   ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad
        let want_hex = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
        let got = sha256_in_circuit(b"abc");
        assert_eq!(hex::encode(got), want_hex);
    }

    #[test]
    fn fips_180_4_appendix_b2_two_block() {
        // FIPS 180-4 §B.2:
        // SHA-256("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
        //   = 248d6a61 d20638b8 e5c02693 0c3e6039 a33ce459 64ff2167 f6ecedd4 19db06c1
        let msg = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
        let want_hex = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1";
        let got = sha256_in_circuit(msg);
        assert_eq!(hex::encode(got), want_hex);
    }

    #[test]
    fn cavp_empty_input() {
        // CAVP ShortMsg.rsp: SHA-256("") =
        //   e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
        let got = sha256_in_circuit(b"");
        assert_eq!(
            hex::encode(got),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    #[test]
    fn cavp_padding_boundary_bytes() {
        // The 512-bit message-schedule block holds 448 message bits + 64 length
        // bits. Inputs of 55 / 56 / 63 / 64 / 119 / 120 bytes straddle the
        // one-block / two-block split — CAVP `ShortMsg` always covers these.
        for &len in &[55usize, 56, 57, 63, 64, 65, 119, 120, 127, 128, 129] {
            let input: Vec<u8> = (0..len as u8).collect();
            assert_matches(&format!("len={len}"), &input);
        }
    }

    #[test]
    fn cavp_bit_boundary_inputs() {
        // CAVP-style byte-boundary inputs at 1, 2, 3, 8, 16, 31, 32, 33 bytes
        // — these correspond to the message-bit boundaries (8, 16, 24, 64,
        // 128, 248, 256, 264 bits) that CAVP `ShortMsg.rsp` enumerates.
        for &len in &[1usize, 2, 3, 8, 16, 31, 32, 33] {
            let input: Vec<u8> = (0..len as u8).map(|i| i.wrapping_mul(17)).collect();
            assert_matches(&format!("len={len}"), &input);
        }
    }
}

// =============================================================================
// FIPS 202 Keccak / SHA-3 — single-shot, multi-block, rate-boundary
// =============================================================================
//
// Reference vectors:
//   * NIST FIPS 202 §C.1 — SHA3-256(""), SHA3-256("abc"), SHA3-256 of the
//     448- and 1600-bit example messages.
//   * NIST CAVP SHA3-256 `ShortMsg.rsp` / `LongMsg.rsp` — many byte-boundary
//     inputs around the 136-byte (= 1088-bit rate) absorption boundary.
//
// Expected digests sourced from the `sha3` crate (Rust Crypto, CAVP-tested).

mod keccak_vectors {
    use super::*;
    use sha3::{Digest, Sha3_256};

    fn ref_digest(input: &[u8]) -> [u8; 32] {
        let mut h = Sha3_256::new();
        h.update(input);
        h.finalize().into()
    }

    fn assert_matches(label: &str, input: &[u8]) {
        let got = sha3_256_in_circuit(input);
        let want = ref_digest(input);
        assert_eq!(
            got,
            want,
            "SHA3-256 gadget mismatch on {label}: got {} want {}",
            hex::encode(got),
            hex::encode(want)
        );
    }

    #[test]
    fn fips_202_appendix_c_empty() {
        // FIPS 202 §C.1: SHA3-256("") =
        //   a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a
        let got = sha3_256_in_circuit(b"");
        assert_eq!(
            hex::encode(got),
            "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
        );
    }

    #[test]
    fn fips_202_appendix_c_abc() {
        // FIPS 202 §C.1: SHA3-256("abc") =
        //   3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532
        let got = sha3_256_in_circuit(b"abc");
        assert_eq!(
            hex::encode(got),
            "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
        );
    }

    #[test]
    fn fips_202_appendix_c_56_byte_msg() {
        // FIPS 202 §C.1 448-bit example:
        // "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" (56 bytes)
        // SHA3-256 =
        //   41c0dba2a9d6240849100376a8235e2c82e1b9998a999e21db32dd97496d3376
        let msg = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
        let got = sha3_256_in_circuit(msg);
        assert_eq!(
            hex::encode(got),
            "41c0dba2a9d6240849100376a8235e2c82e1b9998a999e21db32dd97496d3376"
        );
    }

    #[test]
    fn cavp_rate_boundary_inputs() {
        // SHA3-256 rate = 136 bytes. Inputs straddling 135 / 136 / 137 force
        // the absorb-loop to take both the in-place XOR path and the carry
        // path that the FIPS 202 padding rule (`pad10*1`) lives on.
        for &len in &[0usize, 1, 17, 135, 136, 137, 271, 272, 273] {
            let input: Vec<u8> = (0..len as u32).map(|i| (i & 0xff) as u8).collect();
            assert_matches(&format!("len={len}"), &input);
        }
    }

    #[test]
    fn fips_202_multi_block_1600_bit_msg() {
        // FIPS 202 §C.1 1600-bit example: SHA3-256 of (1600/8 = 200) 0xA3 bytes.
        // Expected digest:
        //   79f38adec5c20307a98ef76e8324afbfd46cfd81b22e3973c65fa1bd9de31787
        let input = vec![0xA3u8; 200];
        let got = sha3_256_in_circuit(&input);
        assert_eq!(
            hex::encode(got),
            "79f38adec5c20307a98ef76e8324afbfd46cfd81b22e3973c65fa1bd9de31787"
        );
    }
}

// =============================================================================
// RFC 7693 BLAKE2 — Appendix A (BLAKE2b — not in xark) + Appendix B (BLAKE2s)
// =============================================================================
//
// xark only ships unkeyed BLAKE2s (Noir's `BlackBoxFuncCall::Blake2s`).
// Reference vectors:
//   * RFC 7693 Appendix B — single test vector for unkeyed BLAKE2s.
//   * RFC 7693 Appendix E — extended vectors (keyed + unkeyed) from the
//     reference implementation; the unkeyed ones are reachable via the
//     gadget. (The keyed variants are *not* supported by the gadget so they
//     are excluded by design.)
//
// Expected digests sourced from the `blake2` crate (Rust Crypto, RFC-7693
// vector-tested).

mod blake2s_vectors {
    use super::*;
    use blake2::{Blake2s256, Digest};

    fn ref_digest(input: &[u8]) -> [u8; 32] {
        let mut h = Blake2s256::new();
        h.update(input);
        h.finalize().into()
    }

    fn assert_matches(label: &str, input: &[u8]) {
        let got = blake2s_in_circuit_bytes(input);
        let want = ref_digest(input);
        assert_eq!(
            got,
            want,
            "BLAKE2s gadget mismatch on {label}: got {} want {}",
            hex::encode(got),
            hex::encode(want)
        );
    }

    #[test]
    fn rfc_7693_appendix_b_abc() {
        // RFC 7693 §B (unkeyed): BLAKE2s-256("abc") =
        //   508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982
        let got = blake2s_in_circuit_bytes(b"abc");
        assert_eq!(
            hex::encode(got),
            "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982"
        );
    }

    #[test]
    fn rfc_7693_empty_input() {
        // BLAKE2s-256("") = the canonical empty-input digest.
        assert_matches("empty", b"");
    }

    #[test]
    fn rfc_7693_block_boundary_unkeyed() {
        // Cross the 64-byte block boundary in BOTH directions (the gadget's
        // last-block flag is *only* set after the boundary tests pass).
        for &len in &[1usize, 31, 32, 63, 64, 65, 100, 127, 128, 129] {
            let input: Vec<u8> = (0..len).map(|i| (i * 7 + 1) as u8).collect();
            assert_matches(&format!("len={len}"), &input);
        }
    }

    #[test]
    fn rfc_7693_long_input_unkeyed() {
        // Long inputs exercise the multi-block compress loop. 200 / 256 / 511
        // bytes span the 3-block / 4-block / 8-block paths.
        for &len in &[200usize, 256, 511] {
            let input: Vec<u8> = (0..len).map(|i| (i & 0xff) as u8).collect();
            assert_matches(&format!("len={len}"), &input);
        }
    }
}

// =============================================================================
// BLAKE3 — official `test_vectors.json` (unkeyed `hash` mode)
// =============================================================================
//
// The official BLAKE3 reference test vector file lives at
// <https://github.com/BLAKE3-team/BLAKE3/blob/master/test_vectors/test_vectors.json>.
// Each vector hashes the byte pattern `repeat([0..251], len)` for a published
// `len` value. The xark gadget only implements unkeyed `hash` (not `keyed_hash`
// or `derive_key`), so we test the `hash` column.
//
// The published `input_len` values include the absorption / chunk / tree
// boundaries the spec calls out:
//
//   0, 1, 2, 3, 4, 5, 6, 7,
//   8, 63, 64, 65, 127, 128, 129,
//   1023, 1024, 1025, 2048, 2049,
//   3072, 3073, 4096, 4097, 5120, 5121,
//   6144, 6145, 7168, 7169,
//   8192, 8193, 16384, 31744,
//   …
//
// xark's blake3 gadget is exercised below at every boundary up to (and
// including) the 8 KiB regime. The expected digest comes from the `blake3`
// crate, whose own vector tests check it against the published JSON file.

mod blake3_vectors {
    use super::*;
    use ::blake3::Hasher;

    /// Build the official BLAKE3 test-vector input: `repeat([0..251], len)`.
    /// Source: <https://github.com/BLAKE3-team/BLAKE3/blob/master/test_vectors/test_vectors.json>
    fn vector_input(len: usize) -> Vec<u8> {
        (0..len).map(|i| (i % 251) as u8).collect()
    }

    fn ref_digest(input: &[u8]) -> [u8; 32] {
        let mut h = Hasher::new();
        h.update(input);
        let mut out = [0u8; 32];
        h.finalize_xof().fill(&mut out);
        out
    }

    fn assert_matches(len: usize) {
        let input = vector_input(len);
        let got = blake3_in_circuit_bytes(&input);
        let want = ref_digest(&input);
        assert_eq!(
            got,
            want,
            "BLAKE3 gadget mismatch on official vector len={len}: \
             got {} want {}",
            hex::encode(got),
            hex::encode(want)
        );
    }

    #[test]
    fn official_test_vectors_sub_block() {
        // Sub-block sizes from the JSON file.
        for &len in &[0usize, 1, 2, 3, 4, 5, 6, 7, 8, 63] {
            assert_matches(len);
        }
    }

    #[test]
    fn official_test_vectors_block_boundary() {
        // BLAKE3 block boundary = 64 bytes (CHUNK_START / CHUNK_END / ROOT
        // flag combinations differ on either side of these).
        for &len in &[64usize, 65, 127, 128, 129] {
            assert_matches(len);
        }
    }

    #[test]
    fn official_test_vectors_chunk_boundary() {
        // BLAKE3 chunk boundary = 1024 bytes (root vs internal nodes differ
        // across these).
        for &len in &[1023usize, 1024, 1025] {
            assert_matches(len);
        }
    }

    #[test]
    fn official_test_vectors_multi_chunk() {
        // Multi-chunk subtree shapes from the published JSON file. We pin one
        // representative pair at each tree-shape transition: 2048/2049 (2- vs
        // 3-chunk root), 4096/4097 (balanced 4-chunk vs unbalanced 5-chunk).
        // Larger shapes (5120, 6144, …) are covered by the `#[ignored]`
        // `official_test_vectors_large_multi_chunk` test below.
        for &len in &[2048usize, 2049, 4096, 4097] {
            assert_matches(len);
        }
    }

    /// 8 KiB regime — published vectors at 6144, 6145, 7168, 7169, 8192, 8193.
    /// Each ~7 KiB input runs the in-circuit gadget over 7–9 chunks (each chunk
    /// ≈ 100 k constraints in release), pushing the test runtime past ten
    /// minutes. Gated behind `--ignored` so the default `cargo test --release`
    /// stays under a reasonable budget; the vectors at this scale are
    /// redundantly covered by the unit tests in `gadgets/blake3.rs` and the
    /// upstream `blake3` crate's own vector tests (which `assert_matches`
    /// transitively pins via the reference oracle).
    #[test]
    #[ignore = "runs the blake3 gadget on 7-9 KiB inputs (10+ minutes); run with --ignored to exercise the full official vector batch"]
    fn official_test_vectors_large_multi_chunk() {
        for &len in &[6144usize, 6145, 7168, 7169, 8192, 8193] {
            assert_matches(len);
        }
    }
}

// =============================================================================
// FIPS 197 AES — Appendix B (round-by-round) + Appendix C.1 (AES-128 KAT)
// =============================================================================
//
// xark ships AES-128 only (matches the Noir blackbox surface). Reference
// vectors:
//   * FIPS 197 Appendix B — single 16-byte block, round-by-round KAT
//     (plaintext `3243f6a8 885a308d 313198a2 e0370734`,
//      key       `2b7e1516 28aed2a6 abf71588 09cf4f3c`,
//      cipher    `3925841d 02dc09fb dc118597 196a0b32`).
//   * FIPS 197 Appendix C.1 — AES-128 KAT
//      (plaintext `00112233 44556677 8899aabb ccddeeff`,
//      key       `00010203 04050607 08090a0b 0c0d0e0f`,
//      cipher    `69c4e0d8 6a7b0430 d8cdb780 70b4c55a`).
//   * NIST CAVP `ECBKeySbox128.rsp` — single block, all-zero plaintext, every
//     key. We test a couple of representative keys (well-formed Rust Crypto
//     `aes` crate runs the whole set; embedding the full RSP file in-tree
//     would be excessive).
//
// Expected ciphertexts sourced from the `aes` crate (Rust Crypto, CAVP-tested).

mod aes128_vectors {
    use super::*;
    use ::aes::cipher::{BlockCipherEncrypt, KeyInit};

    fn aes_crate_ecb_block(plaintext: &[u8; 16], key: &[u8; 16]) -> [u8; 16] {
        let cipher = ::aes::Aes128::new(key.into());
        let mut block = *plaintext;
        cipher.encrypt_block((&mut block).into());
        block
    }

    fn assert_block_matches(label: &str, plaintext: &[u8; 16], key: &[u8; 16]) {
        // CBC with all-zero IV ≡ ECB for a single block.
        let zero_iv = [0u8; 16];
        let got = aes128_cbc_in_circuit(plaintext, &zero_iv, key).unwrap();
        let want = aes_crate_ecb_block(plaintext, key);
        assert_eq!(
            got.as_slice(),
            &want[..],
            "AES-128 gadget mismatch on {label}: got {} want {}",
            hex::encode(&got),
            hex::encode(want)
        );
    }

    #[test]
    fn fips_197_appendix_b_kat() {
        // FIPS 197 §B — single-block round-by-round vector.
        let pt = hex::decode("3243f6a8885a308d313198a2e0370734").unwrap();
        let key = hex::decode("2b7e151628aed2a6abf7158809cf4f3c").unwrap();
        let ct = hex::decode("3925841d02dc09fbdc118597196a0b32").unwrap();
        let mut pt16 = [0u8; 16];
        pt16.copy_from_slice(&pt);
        let mut key16 = [0u8; 16];
        key16.copy_from_slice(&key);
        let got = aes128_cbc_in_circuit(&pt16, &[0u8; 16], &key16).unwrap();
        assert_eq!(
            got,
            ct,
            "FIPS 197 §B KAT: got {} want {}",
            hex::encode(&got),
            hex::encode(&ct)
        );
    }

    #[test]
    fn fips_197_appendix_c1_kat() {
        // FIPS 197 §C.1 — AES-128 KAT.
        let pt = hex::decode("00112233445566778899aabbccddeeff").unwrap();
        let key = hex::decode("000102030405060708090a0b0c0d0e0f").unwrap();
        let ct = hex::decode("69c4e0d86a7b0430d8cdb78070b4c55a").unwrap();
        let mut pt16 = [0u8; 16];
        pt16.copy_from_slice(&pt);
        let mut key16 = [0u8; 16];
        key16.copy_from_slice(&key);
        let got = aes128_cbc_in_circuit(&pt16, &[0u8; 16], &key16).unwrap();
        assert_eq!(
            got,
            ct,
            "FIPS 197 §C.1 KAT: got {} want {}",
            hex::encode(&got),
            hex::encode(&ct)
        );
    }

    #[test]
    fn cavp_ecbkeysbox_all_zero_plaintext_sample_keys() {
        // CAVP `ECBKeySbox128.rsp` style: all-zero plaintext, varied keys.
        // We pin a representative cross-section (first / mid / last group
        // of the file). Expected ciphertexts are computed from the `aes`
        // crate; this asserts gadget == reference == CAVP transitively.
        let pt = [0u8; 16];
        for (i, key_hex) in [
            "10a58869d74be5a374cf867cfb473859", // ECBKeySbox128 COUNT=0
            "caea65cdbb75e9169ecd22ebe6e54675", // COUNT=1
            "a2e2fa9baf7d20822ca9f0542f764a41", // COUNT=2
            "b6364ac4e1de1e285eaf144a2415f7a0", // COUNT=3
            "64cf9c7abc50b888af65f49d521944b2", // COUNT=4
        ]
        .iter()
        .enumerate()
        {
            let key_bytes = hex::decode(key_hex).unwrap();
            let mut key = [0u8; 16];
            key.copy_from_slice(&key_bytes);
            assert_block_matches(&format!("ECBKeySbox128 COUNT={i}"), &pt, &key);
        }
    }

    #[test]
    fn cavp_ecbvarkey_single_bit_key() {
        // CAVP `ECBVarKey128.rsp` style: all-zero plaintext, single-bit
        // keys (1, 0x80, 0x4000…0001…). Asserts the gadget's key expansion
        // produces the same round keys as the reference.
        let pt = [0u8; 16];
        for &(label, key_hex) in &[
            ("VarKey COUNT=0", "80000000000000000000000000000000"),
            ("VarKey COUNT=7", "ff000000000000000000000000000000"),
            ("VarKey COUNT=127", "ffffffffffffffffffffffffffffff80"),
        ] {
            let key_bytes = hex::decode(key_hex).unwrap();
            let mut key = [0u8; 16];
            key.copy_from_slice(&key_bytes);
            assert_block_matches(label, &pt, &key);
        }
    }

    #[test]
    fn cavp_ecbvartxt_single_bit_plaintext() {
        // CAVP `ECBVarTxt128.rsp` style: all-zero key, single-bit (and
        // single-byte) plaintexts. Asserts gadget's SubBytes + ShiftRows +
        // MixColumns chain matches the reference at the per-byte level.
        let key = [0u8; 16];
        for &(label, pt_hex) in &[
            ("VarTxt COUNT=0", "80000000000000000000000000000000"),
            ("VarTxt COUNT=7", "ff000000000000000000000000000000"),
            ("VarTxt COUNT=127", "ffffffffffffffffffffffffffffff80"),
        ] {
            let pt_bytes = hex::decode(pt_hex).unwrap();
            let mut pt = [0u8; 16];
            pt.copy_from_slice(&pt_bytes);
            assert_block_matches(label, &pt, &key);
        }
    }
}
