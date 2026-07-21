//! Operator syntax for non-native fields. `xark_bignum::fp!` defines a field-element
//! type from just its modulus (limbs / `m − 1` / complement derived), with
//! `core::ops` (`+`, `-`, `*`, unary `-`) on it and `.inverse()`/`.sub2()`/… on it.
//! Zero-cost: the operators forward to the width-generic free functions.
//!
//! Each `Private<El>` is a first-class **typed circuit input**: on the host it is a
//! single whole number (a decimal or `0x`-hex string), split into its 3 limbs
//! (`a.limbs[0..2]`) automatically by the `fp!`-generated `NativeInput` — the
//! caller never thinks in limbs.
#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};

// A concrete 256-bit prime field (3 × 86-bit limbs), defined by its modulus alone.
xark_bignum::fp!(El, "41904174945551648470736051755806485464313947085173149");

#[circuit]
pub fn bignum_ops(a: Private<El>, b: Private<El>, out: Public<Field>) {
    // Natural operator syntax on non-native field elements.
    let r = a * b + a - b;
    require_eq(r.limbs[0], out);
}

#[cfg(test)]
mod tests {
    use super::bignum_ops;

    #[test]
    fn accepts_valid() {
        // (2·3 + 2 − 3) mod M = 5; low limb = 5.
        bignum_ops("2".into(), "3".into(), "5".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(bignum_ops("2".into(), "3".into(), "6".into()).is_err());
    }
}
