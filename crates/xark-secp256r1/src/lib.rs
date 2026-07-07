//! `xark-secp256r1`: NIST P-256 / secp256r1 ECDSA gadget over the `xark`
//! `Field` subset.
//!
//! P-256 is `y² = x³ − 3x + b` (short Weierstrass with **a = −3**) over the base
//! field `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, group order `n`. It shares all
//! non-native field arithmetic *and* the incomplete-affine **addition** law with
//! secp256k1 via [`xark_ff`] (modulus-parameterized); only the curve constants
//! and the **doubling** slope differ.
//!
//! # Doubling with `a = −3`
//! The addition slope `λ = (y₂−y₁)/(x₂−x₁)` is `a`-independent, so it's identical
//! to secp256k1. Doubling isn't: `λ = (3x² + a)/2y`, so `a = −3` gives
//! `(3x² − 3)/2y` (an extra `− 3` in the numerator) versus secp256k1's `3x²/2y`.
//!
//! The gadget itself is emitted by the shared
//! [`xark_curve::weierstrass!`] macro (`a = -3` selects the
//! `3x² − 3` doubling numerator); this file only supplies P-256's moduli and
//! constant tables.

#![no_std]

xark_curve::weierstrass! {
    base = "0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF",
    scalar = "0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551",
    a = -3,
    generators = [
        [52227620040540588600771222, 33347259622618539004134583, 8091721874918813684698062, 59685082318776612195095029, 54599710628478995760242092, 6036146923926000695307902],
        [60574784517941929169033592, 38742641973200156549941727, 9440742814978962916680995, 50180633949907515547874257, 52108912657982010475124979, 564125721045731681407961],
        [55202213340089332766604652, 75352241312048865668270014, 7162618025266537839759230, 19003939109578686433415218, 32907397120494406415210721, 10215774641556159746766000],
        [26100211762158113520814162, 69619406642068213128195553, 17100660033962586070975197, 17982870448577553720334534, 69510469396798200300113868, 16996192830591725418421758],
    ],
    correction = [73008335506530070440987265, 52113507725237922464657843, 1975229404901465064722683, 4808832657966113361640839, 48622947606618793931251433, 9925785685835320508030124],
}
