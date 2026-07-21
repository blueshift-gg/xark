//! `xark-secp256r1`: NIST P-256 / secp256r1 ECDSA gadget over the `xark`
//! `Field` subset.
//!
//! P-256 is `y² = x³ − 3x + b` (short Weierstrass with **a = −3**) over the base
//! field `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, group order `n`. It shares all
//! non-native field arithmetic *and* the incomplete-affine **addition** law with
//! secp256k1 via [`xark_bignum`] (modulus-parameterized); only the curve constants
//! and the **doubling** slope differ.
//!
//! # Doubling with `a = −3`
//! The addition slope `λ = (y₂−y₁)/(x₂−x₁)` is `a`-independent, so it's identical
//! to secp256k1. Doubling isn't: `λ = (3x² + a)/2y`, so `a = −3` gives
//! `(3x² − 3)/2y` (an extra `− 3` in the numerator) versus secp256k1's `3x²/2y`.
//!
//! # Inputs
//! The public inputs are the transparent [`Point`] / [`Signature`] / [`Scalar`]
//! types, each a 256-bit value in the compact **2×128-bit half** form (2 public
//! field elements per value) — matching secp256k1. The 3×86-bit limbs the field
//! arithmetic uses are recomposed in-circuit by [`unpack`]; the affine curve
//! gadget (`Point`/`Fq`/`Fp`, emitted by [`xark_curve::weierstrass!`]) lives in
//! the [`affine`] submodule.

#![no_std]

/// The 3×86-bit incomplete-affine P-256 curve gadget (`Point`, `Fq`, `Fp`,
/// `double_scalar_mul_incomplete`, …), emitted by the shared
/// [`xark_curve::weierstrass!`] macro (`a = -3` selects the `3x² − 3` doubling
/// numerator). Kept in its own module because its `Point` / `Scalar` names would
/// otherwise collide with the compact 2×128 public-input types below; the
/// `ecdsa_verify` core unpacks the public inputs into these limb types.
pub mod affine {
    xark_curve::weierstrass! {
        base = "0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF",
        scalar = "0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551",
        a = -3,
        b = [23805269282153275520606283, 64478498050055519801623345, 6858709101169761702330043],
        generators = [
            [52227620040540588600771222, 33347259622618539004134583, 8091721874918813684698062, 59685082318776612195095029, 54599710628478995760242092, 6036146923926000695307902],
            [60574784517941929169033592, 38742641973200156549941727, 9440742814978962916680995, 50180633949907515547874257, 52108912657982010475124979, 564125721045731681407961],
            [55202213340089332766604652, 75352241312048865668270014, 7162618025266537839759230, 19003939109578686433415218, 32907397120494406415210721, 10215774641556159746766000],
            [26100211762158113520814162, 69619406642068213128195553, 17100660033962586070975197, 17982870448577553720334534, 69510469396798200300113868, 16996192830591725418421758],
        ],
        correction = [73008335506530070440987265, 52113507725237922464657843, 1975229404901465064722683, 4808832657966113361640839, 48622947606618793931251433, 9925785685835320508030124],
    }
}
#[cfg(not(xark))]
pub use affine::{order, reduce_scalar};

use xark::{require_eq, Field, Transparent};

/// A P-256 256-bit value (a scalar `r`/`s`/`e`, or a point coordinate) in the
/// compact **2×128-bit half** public-input form — `{ limbs: [Field; 2] }` =
/// `[lo128, hi128]` in-circuit (2 public field elements vs 3 raw 86-bit limbs),
/// `[u8; 32]` big-endian on the host. Recomposed to the internal 3×86 limbs by
/// [`unpack`]. `#[derive(Transparent)]` derives the host `NativeInput` (`[u8; 32]`
/// → `<name>.limbs[0..2]`) from this declaration.
#[derive(Clone, Copy, Transparent)]
#[transparent(bits = 128)]
pub struct Scalar {
    pub limbs: [Field; 2],
}

/// An affine P-256 public key as its two coordinates — compact uncompressed
/// `[u8; 64]` (`x ‖ y`, SEC1 minus the `0x04` tag) on the host, `{ x, y }`
/// (flattening to `<name>.x.limbs[i]` / `<name>.y.limbs[i]`) in-circuit. Verify a
/// signature against it with [`Point::verify`].
#[derive(Clone, Copy, Transparent)]
pub struct Point {
    pub x: Scalar,
    pub y: Scalar,
}

/// A P-256 ECDSA signature `(r, s)` — `[u8; 64]` (`r ‖ s`) on the host, `{ r, s }`
/// in-circuit. Pass it to [`Point::verify`] with the message digest.
#[derive(Clone, Copy, Transparent)]
pub struct Signature {
    pub r: Scalar,
    pub s: Scalar,
}

/// Everything to write a secp256r1-ECDSA circuit in one import:
/// `use xark_secp256r1::prelude::*;` re-exports the `xark` essentials (`circuit`,
/// `Public`, `Field`, `require_eq`, …) plus the transparent input types [`Point`],
/// [`Signature`], [`Scalar`]. Verify with `pubkey.verify(sig, digest)`.
pub mod prelude {
    pub use crate::{Point, Scalar, Signature};
    pub use xark::prelude::*;
}

/// Recompose a 256-bit value from its two **128-bit halves** `[lo, hi]` (the
/// compact public-input form) into the 3×86-bit limbs the P-256 field arithmetic
/// uses. Unlike secp256k1's 4×64 layout, the 86-bit boundaries do **not** align
/// with the 128-bit halves, so we cannot form `lo + hi·2¹²⁸` in-field (that is
/// `< 2²⁵⁶ ≈ 5.3·r`, which wraps `Fr` and would not pin the integer identity).
/// Instead each half is split at a **bit-aligned** boundary — every piece stays
/// `< 2¹²⁸ < r`, so nothing wraps — and the 3×86 limbs are reassembled from the
/// pieces:
///
/// ```text
/// lo (<2¹²⁸) = lo_lo86 + lo_hi42·2⁸⁶      (86 + 42 bits ⇒ lo < 2¹²⁸)
/// hi (<2¹²⁸) = hi_lo44 + hi_hi84·2⁴⁴      (44 + 84 bits ⇒ hi < 2¹²⁸)
/// l0 = lo_lo86                             (bits [0,86))
/// l1 = lo_hi42 + hi_lo44·2⁴²               (bits [86,172) — exactly 86 bits, < 2⁸⁶)
/// l2 = hi_hi84                             (bits [172,256) — < 2⁸⁴)
/// ```
///
/// The four range checks (86 + 42 + 44 + 84 = 256 bits) pin every piece, which
/// makes `(lo, hi)` the unique canonical 2×128 encoding and `[l0, l1, l2]` its
/// unique canonical 3×86 decomposition (`l1 < 2⁸⁶` holds by construction, so it
/// needs no separate check).
fn unpack(packed: [Field; 2]) -> [Field; 3] {
    let two86 = Field::from(1u128 << 86);
    let two44 = Field::from(1u128 << 44);
    let two42 = Field::from(1u128 << 42);
    let lo = packed[0];
    let hi = packed[1];

    // lo = lo_lo86 + lo_hi42·2⁸⁶ — the range checks force lo < 2¹²⁸.
    let dlo = Field::hint_div_rem(lo, two86); // [lo>>86, lo mod 2^86]
    let lo_hi42 = dlo[0];
    let lo_lo86 = dlo[1];
    xark_bignum::range_check_limbs::<1, 86>([lo_lo86]);
    xark_bignum::range_check_limbs::<1, 42>([lo_hi42]);
    require_eq(lo, lo_lo86 + lo_hi42 * two86);

    // hi = hi_lo44 + hi_hi84·2⁴⁴ — the range checks force hi < 2¹²⁸.
    let dhi = Field::hint_div_rem(hi, two44); // [hi>>44, hi mod 2^44]
    let hi_hi84 = dhi[0];
    let hi_lo44 = dhi[1];
    xark_bignum::range_check_limbs::<1, 44>([hi_lo44]);
    xark_bignum::range_check_limbs::<1, 84>([hi_hi84]);
    require_eq(hi, hi_lo44 + hi_hi84 * two44);

    [lo_lo86, lo_hi42 + hi_lo44 * two42, hi_hi84]
}

impl Point {
    /// Verify an ECDSA signature against this public key and message `digest`
    /// (`digest = int(hash(msg)) mod n`, a [`Scalar`]). The transparent-type entry
    /// point — the caller never touches limbs:
    ///
    /// ```ignore
    /// #[circuit]
    /// fn secp256r1_ecdsa(pubkey: Public<Point>, sig: Public<Signature>, digest: Public<Scalar>) {
    ///     pubkey.verify(sig, digest);
    /// }
    /// ```
    pub fn verify(self, sig: Signature, digest: Scalar) {
        ecdsa_verify(self, sig.r, sig.s, digest);
    }
}

/// P-256 ECDSA verification core (3×86-bit incomplete-affine path). P-256 has no
/// efficient endomorphism, so there's no GLV variant as on secp256k1. Each of
/// `q`, `r`, `s`, `e` is a 256-bit value in compact 2×128 form, [`unpack`]ed to the
/// 3×86 limbs the macro's shared primitives (`double_scalar_mul_incomplete`, `Fq`,
/// `Fp`, `Point`) operate on. Wrapped by [`Point::verify`] — callers use that.
pub fn ecdsa_verify(q: Point, r: Scalar, s: Scalar, e: Scalar) {
    let r = affine::Fq::new(unpack(r.limbs));
    let s = affine::Fq::new(unpack(s.limbs));
    let e = affine::Fq::new(unpack(e.limbs));
    let q = affine::Point::new(
        affine::Fp::new(unpack(q.x.limbs)),
        affine::Fp::new(unpack(q.y.limbs)),
    );

    // canonical `< n`, not just limb-bounded — a non-canonical `s`/`r` is malleability.
    r.assert_canonical();
    s.assert_canonical();
    e.assert_canonical();
    r.assert_nonzero(); // r ≠ 0 (s ≠ 0 is enforced by `s.inverse()` below)
    let s_inv = s.inverse();
    let u1 = e * s_inv;
    let u2 = r * s_inv;
    let rr = affine::double_scalar_mul_incomplete(
        xark_bignum::scalar_to_bits(u1.limbs),
        xark_bignum::scalar_to_bits(u2.limbs),
        q,
    );
    let rx_mod_n = affine::Fq::new(rr.x.limbs).reduce();
    let mut i = 0usize;
    while i < 3usize {
        require_eq(rx_mod_n.limbs[i], r.limbs[i]);
        i += 1;
    }
}
