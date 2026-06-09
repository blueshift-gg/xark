//! **Differential test: `alt_bn128` syscalls ↔ Arkworks fallback.**
//!
//! `solana-nostd-alt-bn128` dispatches between two implementations of the
//! BN254 group operations based on the build target:
//!
//! * On `target_os = "solana"` (or `target_arch = "bpf"`): the on-chain
//!   `sol_alt_bn128_group_op` syscall.
//! * Off-chain: Arkworks (`ark-bn254` / `ark-ec`) deserialise + native
//!   add/mul/pairing, then re-serialise.
//!
//! `crates/verifier/` uses this library for both paths. The Lean
//! verification chain (`Formal.EcdsaVerify`, `Formal.Secp256k1Group`, etc.)
//! does not reach into the syscall layer; the agreement between the two
//! paths is one of the trust assumptions flagged in `docs/audit-status.md`
//! under "Out-of-Lean trust".
//!
//! This file closes that gap with a *differential* assertion: for every
//! input in a fixed test set, the host path (Arkworks) and the on-chain
//! path (syscalls) must produce byte-identical results.
//!
//! ## Structure
//!
//! Each operation has:
//!
//! * A `pub const` array of `(input, expected)` tuples, where the
//!   `expected` byte sequence is the canonical EIP-197 / Arkworks output
//!   for that input (sourced from the EIP-197 test vectors and verified
//!   against `ark-bn254` at commit time);
//! * A `#[test] fn <op>_host_matches_golden` that runs the op via
//!   `solana_nostd_alt_bn128::<op>` (the Arkworks path on host) and
//!   asserts equality with the embedded golden;
//! * A `#[svm_test] fn <op>_onchain_matches_golden` that runs the same
//!   op via the syscall path on chain and asserts equality with the same
//!   golden.
//!
//! If both tests pass, the syscall and Arkworks implementations agree on
//! every input in the test set. If either fails, the disagreement is
//! immediately visible.
//!
//! The vectors are the standard EIP-197 reference set (`chfast1`,
//! `chfast2`, `cdetrio8`, `jeff1`) plus a few small algebraic identities
//! (`G + (-G) = 0`, etc.). This is a static differential — for broader
//! random-input fuzz coverage the same scaffolding can be extended with
//! more vectors (each new vector is a const array entry; no other
//! infrastructure changes).

use solana_nostd_alt_bn128::{G1Point, G1Scalar, G2Point, pairing};
use svm_unit_test::svm_test;

// 32 additional deterministically-generated vectors per op, computed
// offline by the small generator at `/tmp/gen_vectors/` (committed
// output in `alt_bn128_extra_vectors.rs.in`). Embedded as `pub const`
// so both the host `#[test]` and on-chain `#[svm_test]` runners can
// iterate them — extending the on-chain differential from 6 fixed
// goldens to 6 + 96 = 102 byte-level checks per CI run.
include!("alt_bn128_extra_vectors.rs.in");

// =============================================================================
// G1 add: 64+64 → 64 bytes.
// =============================================================================

/// `(A, B, expected A+B)` triples for G1 addition. Sourced from the
/// EIP-197 reference vectors (`chfast1`, `chfast2`, `cdetrio8`) — the same
/// set every consumer of `alt_bn128_addition` tests against — plus a
/// `G + (-G) = 0` identity that exercises the inverse path.
pub const G1_ADD_VECTORS: &[(G1Point, G1Point, G1Point)] = &[
    // chfast1: two random on-curve points + their sum.
    (
        G1Point([
            0xc9, 0x3d, 0x09, 0x4e, 0x03, 0x74, 0x3b, 0x5d, 0x0c, 0x61, 0x91, 0x46, 0x12, 0xdd,
            0x11, 0xb3, 0x85, 0x71, 0x8e, 0x36, 0x11, 0x54, 0xdb, 0x76, 0x02, 0xc3, 0xc2, 0xb4,
            0xcf, 0x8a, 0xb1, 0x18, 0x66, 0x72, 0xf3, 0x98, 0x81, 0x28, 0x0d, 0xfc, 0x2e, 0xd3,
            0x58, 0x96, 0x81, 0x96, 0x57, 0x75, 0x49, 0xa7, 0x9f, 0xf5, 0xb9, 0x4c, 0x13, 0xb5,
            0x0c, 0x84, 0x20, 0x47, 0x9c, 0x90, 0x3c, 0x06,
        ]),
        G1Point([
            0xed, 0x4e, 0x01, 0x6a, 0x7c, 0x9e, 0x01, 0x88, 0x3a, 0x96, 0x92, 0x2c, 0xff, 0x20,
            0x7f, 0x18, 0x1a, 0xbb, 0xc0, 0x2b, 0x9c, 0x0c, 0xf0, 0x45, 0x61, 0xbd, 0x84, 0x8a,
            0xf5, 0xb7, 0xc2, 0x07, 0xd7, 0x17, 0xfa, 0x78, 0x84, 0x78, 0xd6, 0x2b, 0x74, 0x5c,
            0x48, 0xa4, 0x06, 0x17, 0x36, 0xdf, 0x17, 0x9a, 0x4c, 0xf7, 0xa3, 0x0d, 0xd7, 0xf2,
            0x40, 0xe9, 0x47, 0xc1, 0x20, 0x4e, 0x61, 0x06,
        ]),
        G1Point([
            0x03, 0x97, 0x83, 0x02, 0xe2, 0xae, 0xee, 0xa1, 0x5f, 0xb6, 0xe6, 0x4c, 0x0a, 0x83,
            0x5e, 0xd8, 0x4d, 0xfe, 0xa3, 0x0c, 0xac, 0x45, 0x3c, 0x3d, 0x9c, 0x4b, 0xfd, 0x5e,
            0x5c, 0x52, 0x43, 0x22, 0x15, 0xc9, 0x95, 0xf1, 0x48, 0x7d, 0x5e, 0xae, 0xb9, 0x7d,
            0x53, 0x32, 0x75, 0xed, 0x0e, 0x18, 0x23, 0x47, 0x96, 0x35, 0xcc, 0x21, 0xdf, 0x09,
            0xe5, 0xa8, 0x6d, 0xbe, 0x33, 0x1d, 0x1d, 0x30,
        ]),
    ),
    // chfast2: (A+B) + A = different sum.
    (
        G1Point([
            0x03, 0x97, 0x83, 0x02, 0xe2, 0xae, 0xee, 0xa1, 0x5f, 0xb6, 0xe6, 0x4c, 0x0a, 0x83,
            0x5e, 0xd8, 0x4d, 0xfe, 0xa3, 0x0c, 0xac, 0x45, 0x3c, 0x3d, 0x9c, 0x4b, 0xfd, 0x5e,
            0x5c, 0x52, 0x43, 0x22, 0x15, 0xc9, 0x95, 0xf1, 0x48, 0x7d, 0x5e, 0xae, 0xb9, 0x7d,
            0x53, 0x32, 0x75, 0xed, 0x0e, 0x18, 0x23, 0x47, 0x96, 0x35, 0xcc, 0x21, 0xdf, 0x09,
            0xe5, 0xa8, 0x6d, 0xbe, 0x33, 0x1d, 0x1d, 0x30,
        ]),
        G1Point([
            0xc9, 0x3d, 0x09, 0x4e, 0x03, 0x74, 0x3b, 0x5d, 0x0c, 0x61, 0x91, 0x46, 0x12, 0xdd,
            0x11, 0xb3, 0x85, 0x71, 0x8e, 0x36, 0x11, 0x54, 0xdb, 0x76, 0x02, 0xc3, 0xc2, 0xb4,
            0xcf, 0x8a, 0xb1, 0x18, 0x66, 0x72, 0xf3, 0x98, 0x81, 0x28, 0x0d, 0xfc, 0x2e, 0xd3,
            0x58, 0x96, 0x81, 0x96, 0x57, 0x75, 0x49, 0xa7, 0x9f, 0xf5, 0xb9, 0x4c, 0x13, 0xb5,
            0x0c, 0x84, 0x20, 0x47, 0x9c, 0x90, 0x3c, 0x06,
        ]),
        G1Point([
            0xb7, 0x9f, 0x0a, 0x1a, 0x8b, 0x26, 0x02, 0x1d, 0xe6, 0x48, 0x56, 0xae, 0xd7, 0x03,
            0x47, 0x4c, 0xd5, 0xb9, 0xe5, 0x9c, 0xb4, 0xa7, 0x5c, 0x4f, 0x92, 0x42, 0xb1, 0xf3,
            0xd0, 0xe6, 0xd3, 0x2b, 0x04, 0xb2, 0xfd, 0xce, 0x66, 0xae, 0x0c, 0x39, 0xc8, 0x19,
            0x46, 0x4a, 0xad, 0xdf, 0x49, 0x2e, 0xce, 0x09, 0x09, 0x30, 0x70, 0x1d, 0x2f, 0x5e,
            0x91, 0x85, 0xaf, 0xa6, 0xe0, 0x1c, 0x61, 0x21,
        ]),
    ),
    // G + (-G) = 0 (algebraic identity — exercises the inverse path).
    (
        G1Point([
            0xc9, 0x3d, 0x09, 0x4e, 0x03, 0x74, 0x3b, 0x5d, 0x0c, 0x61, 0x91, 0x46, 0x12, 0xdd,
            0x11, 0xb3, 0x85, 0x71, 0x8e, 0x36, 0x11, 0x54, 0xdb, 0x76, 0x02, 0xc3, 0xc2, 0xb4,
            0xcf, 0x8a, 0xb1, 0x18, 0x66, 0x72, 0xf3, 0x98, 0x81, 0x28, 0x0d, 0xfc, 0x2e, 0xd3,
            0x58, 0x96, 0x81, 0x96, 0x57, 0x75, 0x49, 0xa7, 0x9f, 0xf5, 0xb9, 0x4c, 0x13, 0xb5,
            0x0c, 0x84, 0x20, 0x47, 0x9c, 0x90, 0x3c, 0x06,
        ]),
        // -G has the same x and `(p - y) mod p`. solana_nostd_alt_bn128
        // exposes `G1Point::negate()` as a const fn; we apply it here to
        // construct the negation without rolling out the field arithmetic
        // by hand.
        G1Point([
            0xc9, 0x3d, 0x09, 0x4e, 0x03, 0x74, 0x3b, 0x5d, 0x0c, 0x61, 0x91, 0x46, 0x12, 0xdd,
            0x11, 0xb3, 0x85, 0x71, 0x8e, 0x36, 0x11, 0x54, 0xdb, 0x76, 0x02, 0xc3, 0xc2, 0xb4,
            0xcf, 0x8a, 0xb1, 0x18, 0x66, 0x72, 0xf3, 0x98, 0x81, 0x28, 0x0d, 0xfc, 0x2e, 0xd3,
            0x58, 0x96, 0x81, 0x96, 0x57, 0x75, 0x49, 0xa7, 0x9f, 0xf5, 0xb9, 0x4c, 0x13, 0xb5,
            0x0c, 0x84, 0x20, 0x47, 0x9c, 0x90, 0x3c, 0x06,
        ])
        .negate(),
        G1Point([0u8; 64]),
    ),
];

// =============================================================================
// G1 scalar-mul: 64+32 → 64 bytes.
// =============================================================================

pub const G1_MUL_VECTORS: &[(G1Point, G1Scalar, G1Point)] = &[
    // EIP-197 `chfast1` scalar-mul vector: a random on-curve point ×
    // a small scalar.
    (
        G1Point([
            0xb7, 0x9f, 0x0a, 0x1a, 0x8b, 0x26, 0x02, 0x1d, 0xe6, 0x48, 0x56, 0xae, 0xd7, 0x03,
            0x47, 0x4c, 0xd5, 0xb9, 0xe5, 0x9c, 0xb4, 0xa7, 0x5c, 0x4f, 0x92, 0x42, 0xb1, 0xf3,
            0xd0, 0xe6, 0xd3, 0x2b, 0x04, 0xb2, 0xfd, 0xce, 0x66, 0xae, 0x0c, 0x39, 0xc8, 0x19,
            0x46, 0x4a, 0xad, 0xdf, 0x49, 0x2e, 0xce, 0x09, 0x09, 0x30, 0x70, 0x1d, 0x2f, 0x5e,
            0x91, 0x85, 0xaf, 0xa6, 0xe0, 0x1c, 0x61, 0x21,
        ]),
        [
            0xc2, 0x15, 0xfa, 0x50, 0xe7, 0x8c, 0x13, 0x11, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ],
        G1Point([
            0x5c, 0x1e, 0xc3, 0x13, 0x9c, 0x6c, 0x2a, 0xee, 0xa4, 0xf5, 0x53, 0xa0, 0x74, 0xb2,
            0x47, 0x8a, 0xef, 0xfa, 0xe8, 0x34, 0xd4, 0x29, 0xbe, 0xe4, 0xca, 0x53, 0x21, 0x98,
            0x6a, 0x8d, 0x0a, 0x07, 0xfc, 0x1a, 0x98, 0xc6, 0xce, 0xc3, 0x0e, 0x69, 0x15, 0xf3,
            0xf0, 0xf4, 0x4b, 0x07, 0x43, 0x19, 0xf0, 0xb0, 0xd5, 0xcd, 0xf9, 0x89, 0xb9, 0xff,
            0xa9, 0xa3, 0xeb, 0x14, 0xe9, 0x8c, 0x1b, 0x03,
        ]),
    ),
];

// =============================================================================
// G2 add: 128+128 → 128 bytes.
// =============================================================================

pub const G2_ADD_VECTORS: &[(G2Point, G2Point, G2Point)] = &[
    // EIP-197 `jeff1` pairing operands, summed.
    (
        G2Point([
            0x78, 0x16, 0xa4, 0x15, 0x63, 0x4b, 0xaf, 0x49, 0x40, 0xc0, 0x8a, 0x4c, 0x11, 0x60,
            0x59, 0x90, 0x28, 0x8d, 0x84, 0x61, 0x35, 0xb4, 0x34, 0x8b, 0xfa, 0x3b, 0x48, 0x01,
            0xca, 0x11, 0xbf, 0x04, 0xf7, 0x5b, 0xa3, 0x03, 0x20, 0x45, 0x4a, 0x6b, 0x39, 0x14,
            0x35, 0xc6, 0x36, 0x96, 0x32, 0xa7, 0x99, 0xcf, 0x93, 0x1a, 0xe5, 0x88, 0xd8, 0x4b,
            0x6c, 0xd4, 0xf5, 0xbf, 0x5e, 0xd1, 0x9d, 0x20, 0x50, 0x75, 0x87, 0xde, 0xe4, 0xe5,
            0x5f, 0x16, 0x48, 0xb0, 0x9b, 0x0c, 0x1f, 0xe6, 0xcc, 0xa2, 0x7e, 0xe0, 0x39, 0xfe,
            0xc6, 0x20, 0x5f, 0x84, 0xf9, 0x1b, 0x0c, 0xf3, 0x4c, 0x2a, 0x0a, 0x12, 0x4d, 0x34,
            0xbe, 0x51, 0x2a, 0x3c, 0x93, 0xbf, 0xad, 0x1f, 0xc4, 0x7a, 0xcd, 0x1a, 0xa7, 0xa2,
            0x0c, 0xfd, 0x5c, 0x44, 0x1a, 0xad, 0xa2, 0x37, 0x35, 0xc9, 0xcf, 0xf6, 0x4a, 0x32,
            0xb8, 0x2b,
        ]),
        G2Point([
            0xed, 0xf6, 0x92, 0xd9, 0x5c, 0xbd, 0xde, 0x46, 0xdd, 0xda, 0x5e, 0xf7, 0xd4, 0x22,
            0x43, 0x67, 0x79, 0x44, 0x5c, 0x5e, 0x66, 0x00, 0x6a, 0x42, 0x76, 0x1e, 0x1f, 0x12,
            0xef, 0xde, 0x00, 0x18, 0xc2, 0x12, 0xf3, 0xae, 0xb7, 0x85, 0xe4, 0x97, 0x12, 0xe7,
            0xa9, 0x35, 0x33, 0x49, 0xaa, 0xf1, 0x25, 0x5d, 0xfb, 0x31, 0xb7, 0xbf, 0x60, 0x72,
            0x3a, 0x48, 0x0d, 0x92, 0x93, 0x93, 0x8e, 0x19, 0xaa, 0x7d, 0xfa, 0x66, 0x01, 0xcc,
            0xe6, 0x4c, 0x7b, 0xd3, 0x43, 0x0c, 0x69, 0xe7, 0xd1, 0xe3, 0x8f, 0x40, 0xcb, 0x8d,
            0x80, 0x71, 0xab, 0x4a, 0xeb, 0x6d, 0x8c, 0xdb, 0xa5, 0x5e, 0xc8, 0x12, 0x5b, 0x97,
            0x22, 0xd1, 0xdc, 0xda, 0xac, 0x55, 0xf3, 0x8e, 0xb3, 0x70, 0x33, 0x31, 0x4b, 0xbc,
            0x95, 0x33, 0x0c, 0x69, 0xad, 0x99, 0x9e, 0xec, 0x75, 0xf0, 0x5f, 0x58, 0xd0, 0x89,
            0x06, 0x09,
        ]),
        // Captured from Arkworks output of `PAIR0_G2 + PAIR1_G2` (LE
        // uncompressed); used as the differential anchor for both the host
        // and on-chain runners.
        G2Point([
            244, 183, 65, 95, 123, 231, 190, 107, 39, 203, 3, 54, 253, 135, 227, 2, 90, 6, 1, 172,
            8, 206, 48, 39, 49, 194, 62, 152, 42, 92, 6, 23, 4, 166, 208, 0, 71, 148, 22, 132, 199,
            221, 29, 85, 6, 171, 225, 127, 72, 62, 65, 138, 67, 174, 62, 55, 223, 239, 154, 130,
            233, 223, 122, 9, 147, 191, 72, 209, 186, 87, 237, 234, 164, 71, 114, 146, 98, 228,
            251, 200, 64, 79, 55, 153, 88, 116, 99, 186, 30, 163, 104, 99, 120, 250, 159, 41, 80,
            56, 65, 179, 5, 100, 217, 47, 19, 170, 237, 217, 125, 224, 183, 171, 21, 197, 236, 29,
            108, 238, 225, 126, 65, 141, 129, 183, 102, 23, 167, 14,
        ]),
    ),
];

// =============================================================================
// Pairing: array of (G1, G2) pairs → 32-byte G1Scalar.
// =============================================================================

/// `jeff1` 2-pair vector: a product that lands at the GT identity, so the
/// syscall returns the little-endian scalar `1`. This is the standard
/// EIP-197 pairing-check ("`e(P0, Q0) · e(P1, Q1) = 1`"), which is the
/// shape every Groth16 verification call uses.
pub const PAIRING_2_VECTORS: &[([(G1Point, G2Point); 2], G1Scalar)] = &[(
    [
        (
            G1Point([
                0x59, 0x3f, 0xc4, 0x24, 0x60, 0xc1, 0x31, 0xdd, 0x64, 0xa6, 0xad, 0x76, 0xaa, 0xa7,
                0xff, 0x81, 0x33, 0x19, 0xa1, 0xbb, 0x7e, 0xd5, 0x41, 0x45, 0xb9, 0x4b, 0xef, 0x4d,
                0x6f, 0x47, 0x76, 0x1c, 0x41, 0xef, 0x6a, 0xa7, 0x03, 0x9b, 0x5c, 0xe4, 0x94, 0xd2,
                0xe9, 0xd3, 0x55, 0x9b, 0x81, 0xfc, 0x45, 0x87, 0x67, 0x1c, 0x81, 0xe2, 0xfe, 0x04,
                0xe2, 0x73, 0xf6, 0x20, 0x29, 0xdd, 0x34, 0x30,
            ]),
            G2Point([
                0x78, 0x16, 0xa4, 0x15, 0x63, 0x4b, 0xaf, 0x49, 0x40, 0xc0, 0x8a, 0x4c, 0x11, 0x60,
                0x59, 0x90, 0x28, 0x8d, 0x84, 0x61, 0x35, 0xb4, 0x34, 0x8b, 0xfa, 0x3b, 0x48, 0x01,
                0xca, 0x11, 0xbf, 0x04, 0xf7, 0x5b, 0xa3, 0x03, 0x20, 0x45, 0x4a, 0x6b, 0x39, 0x14,
                0x35, 0xc6, 0x36, 0x96, 0x32, 0xa7, 0x99, 0xcf, 0x93, 0x1a, 0xe5, 0x88, 0xd8, 0x4b,
                0x6c, 0xd4, 0xf5, 0xbf, 0x5e, 0xd1, 0x9d, 0x20, 0x50, 0x75, 0x87, 0xde, 0xe4, 0xe5,
                0x5f, 0x16, 0x48, 0xb0, 0x9b, 0x0c, 0x1f, 0xe6, 0xcc, 0xa2, 0x7e, 0xe0, 0x39, 0xfe,
                0xc6, 0x20, 0x5f, 0x84, 0xf9, 0x1b, 0x0c, 0xf3, 0x4c, 0x2a, 0x0a, 0x12, 0x4d, 0x34,
                0xbe, 0x51, 0x2a, 0x3c, 0x93, 0xbf, 0xad, 0x1f, 0xc4, 0x7a, 0xcd, 0x1a, 0xa7, 0xa2,
                0x0c, 0xfd, 0x5c, 0x44, 0x1a, 0xad, 0xa2, 0x37, 0x35, 0xc9, 0xcf, 0xf6, 0x4a, 0x32,
                0xb8, 0x2b,
            ]),
        ),
        (
            G1Point([
                0x7c, 0xdf, 0xb6, 0xd1, 0x49, 0xde, 0x22, 0xc3, 0xea, 0xcb, 0xf1, 0x6f, 0x3c, 0x02,
                0xa2, 0x5b, 0xfa, 0xcd, 0x0f, 0xc7, 0x4a, 0x1c, 0xd4, 0x10, 0x77, 0x09, 0xf1, 0x1c,
                0x9f, 0x12, 0x1e, 0x11, 0x11, 0xf4, 0x6b, 0x6a, 0xce, 0xfa, 0x53, 0x38, 0xa7, 0x70,
                0x38, 0xb9, 0x85, 0x35, 0x88, 0xa2, 0xfc, 0x42, 0xf2, 0x2b, 0x46, 0xe9, 0x6d, 0x28,
                0x17, 0x3c, 0x0e, 0x83, 0x1a, 0xc6, 0x32, 0x20,
            ]),
            G2Point([
                0xed, 0xf6, 0x92, 0xd9, 0x5c, 0xbd, 0xde, 0x46, 0xdd, 0xda, 0x5e, 0xf7, 0xd4, 0x22,
                0x43, 0x67, 0x79, 0x44, 0x5c, 0x5e, 0x66, 0x00, 0x6a, 0x42, 0x76, 0x1e, 0x1f, 0x12,
                0xef, 0xde, 0x00, 0x18, 0xc2, 0x12, 0xf3, 0xae, 0xb7, 0x85, 0xe4, 0x97, 0x12, 0xe7,
                0xa9, 0x35, 0x33, 0x49, 0xaa, 0xf1, 0x25, 0x5d, 0xfb, 0x31, 0xb7, 0xbf, 0x60, 0x72,
                0x3a, 0x48, 0x0d, 0x92, 0x93, 0x93, 0x8e, 0x19, 0xaa, 0x7d, 0xfa, 0x66, 0x01, 0xcc,
                0xe6, 0x4c, 0x7b, 0xd3, 0x43, 0x0c, 0x69, 0xe7, 0xd1, 0xe3, 0x8f, 0x40, 0xcb, 0x8d,
                0x80, 0x71, 0xab, 0x4a, 0xeb, 0x6d, 0x8c, 0xdb, 0xa5, 0x5e, 0xc8, 0x12, 0x5b, 0x97,
                0x22, 0xd1, 0xdc, 0xda, 0xac, 0x55, 0xf3, 0x8e, 0xb3, 0x70, 0x33, 0x31, 0x4b, 0xbc,
                0x95, 0x33, 0x0c, 0x69, 0xad, 0x99, 0x9e, 0xec, 0x75, 0xf0, 0x5f, 0x58, 0xd0, 0x89,
                0x06, 0x09,
            ]),
        ),
    ],
    {
        let mut e = [0u8; 32];
        e[0] = 1;
        e
    },
)];

// =============================================================================
// Host #[test] runners: exercise the Arkworks fallback path.
// =============================================================================

#[test]
fn g1_add_host_matches_golden() {
    for (a, b, expected) in G1_ADD_VECTORS {
        let got = (*a + *b).unwrap();
        assert_eq!(
            got.0, expected.0,
            "host (Arkworks) G1 add disagrees with golden"
        );
    }
}

#[test]
fn g1_mul_host_matches_golden() {
    for (p, s, expected) in G1_MUL_VECTORS {
        let got = (*p * *s).unwrap();
        assert_eq!(
            got.0, expected.0,
            "host (Arkworks) G1 mul disagrees with golden"
        );
    }
}

#[test]
fn g2_add_host_matches_golden() {
    for (a, b, expected) in G2_ADD_VECTORS {
        let got = (*a + *b).unwrap();
        assert_eq!(
            got.0, expected.0,
            "host (Arkworks) G2 add disagrees with golden"
        );
    }
}

#[test]
fn pairing_host_matches_golden() {
    for (pairs, expected) in PAIRING_2_VECTORS {
        let got = pairing(pairs).unwrap();
        assert_eq!(
            got, *expected,
            "host (Arkworks) pairing disagrees with golden"
        );
    }
}

// =============================================================================
// On-chain #[svm_test] runners: exercise the syscall path through Mollusk.
//
// Each body asserts equality with the same golden bytes the host
// `#[test]` runners check. If host and on-chain both pass, the syscall
// and Arkworks implementations agree on every input in the test set.
//
// The bodies use literal indexing (rather than a `for` loop) because
// `svm-unit-test` requires the body to be syntactically simple — every
// op is unfolded by hand. This is the same style as
// `solana-nostd-alt-bn128/tests/sbpf.rs::correctness`.
// =============================================================================

#[svm_test]
fn g1_add_onchain_matches_golden() {
    // Each `(a, b, expected)` triple must round-trip through the syscall.
    let (a0, b0, e0) = G1_ADD_VECTORS[0];
    assert!((a0 + b0).unwrap() == e0);
    let (a1, b1, e1) = G1_ADD_VECTORS[1];
    assert!((a1 + b1).unwrap() == e1);
    let (a2, b2, e2) = G1_ADD_VECTORS[2];
    assert!((a2 + b2).unwrap() == e2);
}

#[svm_test]
fn g1_mul_onchain_matches_golden() {
    let (p0, s0, e0) = G1_MUL_VECTORS[0];
    assert!((p0 * s0).unwrap() == e0);
}

#[svm_test]
fn g2_add_onchain_matches_golden() {
    let (a0, b0, e0) = G2_ADD_VECTORS[0];
    assert!((a0 + b0).unwrap() == e0);
}

#[svm_test]
fn pairing_onchain_matches_golden() {
    let (pairs0, e0) = PAIRING_2_VECTORS[0];
    assert!(pairing(&pairs0).unwrap() == e0);
}

// --- Extra-vector on-chain coverage. ----------------------------------------
// Each `_extra` svm_test iterates the 32 generated vectors and asserts
// syscall == embedded golden. The goldens were computed via ark-bn254
// at vector-generation time, so a green test means the syscall agrees
// with Arkworks on all 32 inputs of that op.

#[svm_test]
fn g1_add_onchain_extra_matches_golden() {
    let mut i = 0;
    while i < G1_ADD_VECTORS_EXTRA.len() {
        let (a, b, e) = G1_ADD_VECTORS_EXTRA[i];
        assert!((a + b).unwrap() == e);
        i += 1;
    }
}

#[svm_test]
fn g1_mul_onchain_extra_matches_golden() {
    let mut i = 0;
    while i < G1_MUL_VECTORS_EXTRA.len() {
        let (p, s, e) = G1_MUL_VECTORS_EXTRA[i];
        assert!((p * s).unwrap() == e);
        i += 1;
    }
}

#[svm_test]
fn g2_add_onchain_extra_matches_golden() {
    let mut i = 0;
    while i < G2_ADD_VECTORS_EXTRA.len() {
        let (a, b, e) = G2_ADD_VECTORS_EXTRA[i];
        assert!((a + b).unwrap() == e);
        i += 1;
    }
}

// --- Host coverage of the extras. -------------------------------------------
// Runs through `solana_nostd_alt_bn128`'s Arkworks dispatch.

#[test]
fn g1_add_host_extra_matches_golden() {
    for (a, b, e) in G1_ADD_VECTORS_EXTRA {
        assert_eq!((*a + *b).unwrap().0, e.0, "G1 add extra-vector mismatch");
    }
}

#[test]
fn g1_mul_host_extra_matches_golden() {
    for (p, s, e) in G1_MUL_VECTORS_EXTRA {
        assert_eq!((*p * *s).unwrap().0, e.0, "G1 mul extra-vector mismatch");
    }
}

#[test]
fn g2_add_host_extra_matches_golden() {
    for (a, b, e) in G2_ADD_VECTORS_EXTRA {
        assert_eq!((*a + *b).unwrap().0, e.0, "G2 add extra-vector mismatch");
    }
}

// =============================================================================
// Host-side seeded-random fuzz of the Arkworks dispatch.
//
// The svm_test runners above pin syscall == golden on a small fixed set
// (the EIP-197 / jeff vectors). Those goldens were originally derived
// from Arkworks, so syscall == golden == Arkworks-at-commit-time. The
// per-op host fuzz tests below extend the *host* (Arkworks) coverage
// from 6 fixed vectors to 256 random ones per op — driven by a fixed
// ChaCha20 seed so the test set is reproducible across runs.
//
// What these tests catch: drift between
// `solana_nostd_alt_bn128`'s host dispatch (which routes to Arkworks)
// and a direct `ark-bn254` reference path. Any divergence (a wrong
// endianness conversion, a wrong subgroup gate, etc.) surfaces over
// the seeded input set.
//
// What they do *not* catch (and intentionally so): on-chain syscall
// drift over the 256-input set. That requires either embedding 256
// goldens as `const` (committed as a follow-up) or a parameterized
// mollusk runner (out-of-scope for this scaffold). See the file
// header for the differential boundary.
// =============================================================================

#[cfg(not(any(target_os = "solana", target_arch = "bpf")))]
mod host_fuzz {
    use super::{G1Point, G1Scalar, G2Point};

    use ark_bn254::{Fr as ArkFr, G1Affine, G1Projective, G2Affine, G2Projective};
    use ark_ec::{AffineRepr, CurveGroup, PrimeGroup, pairing::Pairing};
    use ark_ff::UniformRand;
    use ark_serialize::CanonicalSerialize;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    /// Cardinality of each per-op fuzz set. 256 is a sweet spot — large
    /// enough that any byte-level dispatch bug surfaces with high
    /// probability, small enough that the test runs in well under a
    /// second.
    const FUZZ_ITERATIONS: usize = 256;

    /// Fixed seed so the test set is reproducible across runs and CI
    /// invocations. Changing this seed grows the input set without
    /// changing the differential property.
    const SEED: [u8; 32] = *b"xark differential alt_bn128 fuzz";

    fn g1_to_le_bytes(p: G1Affine) -> [u8; 64] {
        let mut out = [0u8; 64];
        p.x.serialize_uncompressed(&mut out[..32]).unwrap();
        p.y.serialize_uncompressed(&mut out[32..]).unwrap();
        out
    }

    fn g2_to_le_bytes(p: G2Affine) -> [u8; 128] {
        let mut out = [0u8; 128];
        p.x.serialize_uncompressed(&mut out[..64]).unwrap();
        p.y.serialize_uncompressed(&mut out[64..]).unwrap();
        out
    }

    fn scalar_to_le_bytes(s: ArkFr) -> G1Scalar {
        let mut out = [0u8; 32];
        s.serialize_uncompressed(&mut out[..]).unwrap();
        out
    }

    /// 256-iteration seeded fuzz: for each iteration, draw two random
    /// scalars, derive their `k·G` points via Arkworks, compute the sum
    /// via `solana_nostd_alt_bn128` (host = Arkworks dispatch), and
    /// assert it matches the direct Arkworks reference computation.
    #[test]
    fn g1_add_host_fuzz_matches_arkworks_reference() {
        let mut rng = ChaCha20Rng::from_seed(SEED);
        let g1_gen = G1Projective::generator();
        for iter in 0..FUZZ_ITERATIONS {
            let k1 = ArkFr::rand(&mut rng);
            let k2 = ArkFr::rand(&mut rng);
            let p1_aff: G1Affine = (g1_gen * k1).into_affine();
            let p2_aff: G1Affine = (g1_gen * k2).into_affine();
            // Reference: direct Arkworks sum.
            let ref_sum_aff: G1Affine = (p1_aff + p2_aff).into_affine();
            let ref_bytes = g1_to_le_bytes(ref_sum_aff);
            // Test path: through `solana_nostd_alt_bn128` (Arkworks host
            // dispatch).
            let p1 = G1Point(g1_to_le_bytes(p1_aff));
            let p2 = G1Point(g1_to_le_bytes(p2_aff));
            let got = (p1 + p2).expect("G1 add").0;
            assert_eq!(
                got, ref_bytes,
                "iter {iter}: solana_nostd_alt_bn128 G1 add diverges from ark-bn254 reference"
            );
        }
    }

    #[test]
    fn g1_mul_host_fuzz_matches_arkworks_reference() {
        let mut rng = ChaCha20Rng::from_seed(SEED);
        let g1_gen = G1Projective::generator();
        for iter in 0..FUZZ_ITERATIONS {
            let k_point = ArkFr::rand(&mut rng);
            let k_scalar = ArkFr::rand(&mut rng);
            let p_aff: G1Affine = (g1_gen * k_point).into_affine();
            let ref_aff: G1Affine = (p_aff * k_scalar).into_affine();
            let ref_bytes = g1_to_le_bytes(ref_aff);
            let p = G1Point(g1_to_le_bytes(p_aff));
            let s = scalar_to_le_bytes(k_scalar);
            let got = (p * s).expect("G1 mul").0;
            assert_eq!(
                got, ref_bytes,
                "iter {iter}: solana_nostd_alt_bn128 G1 mul diverges from ark-bn254 reference"
            );
        }
    }

    #[test]
    fn g2_add_host_fuzz_matches_arkworks_reference() {
        let mut rng = ChaCha20Rng::from_seed(SEED);
        let g2_gen = G2Projective::generator();
        for iter in 0..FUZZ_ITERATIONS {
            let k1 = ArkFr::rand(&mut rng);
            let k2 = ArkFr::rand(&mut rng);
            let p1_aff: G2Affine = (g2_gen * k1).into_affine();
            let p2_aff: G2Affine = (g2_gen * k2).into_affine();
            let ref_aff: G2Affine = (p1_aff + p2_aff).into_affine();
            let ref_bytes = g2_to_le_bytes(ref_aff);
            let p1 = G2Point(g2_to_le_bytes(p1_aff));
            let p2 = G2Point(g2_to_le_bytes(p2_aff));
            let got = (p1 + p2).expect("G2 add").0;
            assert_eq!(
                got, ref_bytes,
                "iter {iter}: solana_nostd_alt_bn128 G2 add diverges from ark-bn254 reference"
            );
        }
    }

    /// 2-pair pairing fuzz — the shape used by Groth16 verification.
    /// For each iteration, build a 2-pair input `(k·G, h·H), (k·G, -h·H)`
    /// whose product equals the GT identity (the canonical "verifier
    /// accepts" shape). Run via `solana_nostd_alt_bn128::pairing` and
    /// assert it returns the LE `1` scalar.
    #[test]
    fn pairing_host_fuzz_identity_2pair() {
        let mut rng = ChaCha20Rng::from_seed(SEED);
        let g1_gen = G1Projective::generator();
        let g2_gen = G2Projective::generator();
        for iter in 0..FUZZ_ITERATIONS {
            let k = ArkFr::rand(&mut rng);
            let h = ArkFr::rand(&mut rng);
            let p1_aff: G1Affine = (g1_gen * k).into_affine();
            let q1_aff: G2Affine = (g2_gen * h).into_affine();
            // Second pair has the same point pair but with G2 negated, so
            // `e(P, Q) · e(P, -Q) = 1` and the multi-pairing returns the
            // GT identity → LE scalar `[1, 0, …]`.
            let q1_neg_aff = (-q1_aff.into_group()).into_affine();
            let p1 = G1Point(g1_to_le_bytes(p1_aff));
            let q1 = G2Point(g2_to_le_bytes(q1_aff));
            let q1_neg = G2Point(g2_to_le_bytes(q1_neg_aff));
            let pairs = [(p1, q1), (p1, q1_neg)];
            let got = super::pairing(&pairs).expect("pairing").to_owned();
            let mut expected = [0u8; 32];
            expected[0] = 1;
            assert_eq!(
                got, expected,
                "iter {iter}: solana_nostd_alt_bn128 pairing identity check diverges"
            );
            // Sanity: the Arkworks reference pairing on the same operands
            // also returns the GT identity. (We don't byte-compare the
            // syscall output to a serialised GT result here — `pairing`
            // returns a boolean-encoded scalar, not an arbitrary GT
            // element — but this confirms the inputs themselves form a
            // valid identity pair.)
            let ref_e = <ark_bn254::Bn254 as Pairing>::multi_pairing(
                [p1_aff, p1_aff],
                [q1_aff, q1_neg_aff],
            );
            assert!(
                ref_e.0 == ark_bn254::Fq12::from(1u32),
                "iter {iter}: Arkworks reference pairing did not equal GT identity"
            );
        }
    }
}
