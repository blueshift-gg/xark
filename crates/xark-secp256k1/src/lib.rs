//! `xark-secp256k1`: secp256k1 ECDSA gadget over the `xark` `Field` subset.
//!
//! secp256k1 is `y² = x³ + 7` (short Weierstrass with **a = 0**, j-invariant 0)
//! over the base field `p = 2^256 - 2^32 - 977`, group order `n`. 256-bit field
//! elements are 3 little-endian 86-bit limbs (86 is the multiply-optimal size
//! over BN254); the non-native field arithmetic lives in [`xark_ff`] (shared
//! with secp256r1, parameterized by modulus). This crate supplies the curve
//! constants and the incomplete-affine group law — with `a = 0` the doubling
//! slope is just `3x²/2y` (no `a` term).
//!
//! The whole gadget (`Fp`/`Fq`, `Point`, `ec_add_incomplete`,
//! `ec_double_incomplete`, `double_scalar_mul_incomplete`, `ecdsa_verify`) is
//! emitted by the shared [`xark_curve::weierstrass!`] macro — this
//! file is just the curve's constants. secp256r1 differs only in its moduli,
//! `a = -3`, and these tables.
//!
//! Every arithmetic building block is individually solver-validated; see the
//! `xark` compiler snapshot tests. `ecdsa_verify` composes them (structural
//! capstone; not solved end-to-end due to size).

#![no_std]

xark_curve::weierstrass! {
    base = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
    scalar = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
    a = 0,
    b = [7, 0, 0],
    generators = [
        [17117865558768631194064792, 12501176021340589225372855, 9198697782662356105779718, 6441780312434748884571320, 57953919405111227542741658, 5457536640262350763842127],
        [57105948487393027623526117, 2088890992725950981549619, 14961784698075395646489684, 46925586441427271765976362, 19820246243853867596485833, 2031033786214458435714136],
        [57545291876987742944507641, 75066192660561802595210765, 18828234277447069677687620, 2583640362791394057184882, 38197615293098406611150035, 4273588397735691711217203],
        [39240586505594730384248083, 43607737248441145767116859, 17270833250143069575414244, 74945151656403808399104290, 9851937081784665158242046, 6190313694369289866667054],
    ],
    correction = [50013525532261609533771622, 33977132216705809345294891, 6434814454533600219945686, 34870826494395841319973943, 37401083326380650972982394, 14538710286819613138477839],
}
