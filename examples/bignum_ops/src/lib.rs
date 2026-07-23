//! Operator syntax for non-native fields. `xark_bignum::fp!` defines a field-element
//! type from just its modulus, with zero-cost `core::ops` (`+`, `-`, `*`, unary `-`)
//! and `.inverse()`/`.sub2()`/… forwarding to the width-generic free functions. Each
//! `Private<El>` is a typed circuit input — a single whole number on the host, split
//! into its 3 limbs automatically by the `fp!`-generated `NativeInput`.

use xark::prelude::*;

// A concrete 256-bit prime field (3 × 86-bit limbs), defined by its modulus alone.
xark_bignum::fp!(El, "41904174945551648470736051755806485464313947085173149");

#[circuit]
pub fn bignum_ops(a: Private<El>, b: Private<El>, out: Public<Field>) {
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
