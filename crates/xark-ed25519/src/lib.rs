//! `xark-ed25519`: an Ed25519 (twisted-Edwards, `a = −1`) scalar-multiplication
//! and EdDSA signature-verification gadget, over the `xark` `Field` subset.
//!
//! Ed25519 lives over the base field `p = 2^255 − 19` with the curve equation
//! `−x² + y² = 1 + d·x²·y²` and group order `L`. Its ~255-bit coordinates are
//! foreign to the native BN254 proving field, so they use the shared 3 × 86-bit
//! non-native limb arithmetic in [`xark_ff`]. The whole group law, scalar-mul, and
//! constants are emitted by the shared [`xark_curve::edwards!`] macro — the
//! addition is **complete** (no exceptional cases), so unlike the secp256k1 ECDSA
//! gadget there is no offset accumulator.
//!
//! This crate adds the fixed base point `B` and the EdDSA verification equation
//! `[S]·B == R + [k]·A` (the algebraic core of Ed25519 verification; the SHA-512
//! challenge hash `k = H(R‖A‖M)` is out of scope — `k` is supplied as a witness).

#![no_std]

use xark::{assert_eq, Field};

// The Ed25519 curve: base field p = 2^255 − 19, scalar order L, constant d.
xark_curve::edwards! {
    base   = "57896044618658097711785492504343953926634992332820282019728792003956564819949",
    scalar = "7237005577332262213973186563042994240857116359379907606001950938285454250989",
    d      = "37095705934669439343138083508754565189542113879843219016388785533085940283555",
}

/// The Ed25519 base point `B` (its two coordinates as compile-time 86-bit limbs).
///   Bx = 15112221349535400772501151409588531511454012693041857206046113283949847762202
///   By = 46316835694926478169428394003475163141307993866256225615783033603165251855960
pub fn base() -> Point {
    Point::new(
        fp(45522188556658772877366554, 10615720421966981067801172, 2524463244633754693274190),
        fp(46422751473201760308717144, 30948500982134506872478105, 7737125245533626718119526),
    )
}

/// Fixed-base scalar multiplication `[k]·B`, where `k_bits` is the 256-bit
/// little-endian decomposition of the scalar (see [`xark_ff::scalar_to_bits`]).
pub fn mul_base(k_bits: [Field; 256]) -> Point {
    scalar_mul(k_bits, base())
}

/// Verify the Ed25519 signature equation `[S]·B == R + [k]·A`.
///
/// `a_pub` is the public key `A`, `r_sig` the signature's `R` point, `s_bits` the
/// 256-bit decomposition of the signature scalar `S`, and `k_bits` the 256-bit
/// decomposition of the challenge `k = H(R‖A‖M)` (supplied as a witness — the
/// hash itself is not constrained here). Fails (unsatisfiable) if the equation
/// does not hold.
pub fn eddsa_verify(a_pub: Point, r_sig: Point, s_bits: [Field; 256], k_bits: [Field; 256]) {
    // SOUNDNESS: the public-key coordinates are untrusted witnesses that feed the
    // non-native `mod_mul` in the group law. `mod_mul` only range-checks its
    // *outputs*; its no-wrap correctness assumes every operand limb is < 2^86.
    // Without pinning `a_pub`'s limbs a malicious prover can supply out-of-range
    // limbs so the schoolbook column products wrap `Fr`, break `a·b = q·m + r`,
    // and forge acceptance. Check here — BEFORE the `0 - a_pub.x` negation below,
    // which is itself a non-native op with the same precondition, so checking a
    // derived value later would be too late. `r_sig` needs no check: it is pinned
    // canonical by the final limb-wise `assert_eq(t, r_sig)`.
    a_pub.x.range_check();
    a_pub.y.range_check();
    // Rewrite `[S]·B == R + [k]·A` as `[S]·B + [k]·(−A) == R`, so the two scalar
    // multiplications share one windowed Strauss–Shamir pass. Twisted-Edwards
    // negation is `(−x, y)`.
    let neg_a = Point::new(fp(0, 0, 0) - a_pub.x, a_pub.y);
    let t = double_scalar_mul(s_bits, base(), k_bits, neg_a);
    // Assert t == R, coordinate-wise, limb-by-limb.
    let mut i = 0usize;
    while i < 3usize {
        assert_eq(t.x.limbs[i], r_sig.x.limbs[i]);
        assert_eq(t.y.limbs[i], r_sig.y.limbs[i]);
        i += 1;
    }
}
