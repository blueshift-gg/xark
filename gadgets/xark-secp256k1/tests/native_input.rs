//! Validate the `#[derive(Transparent)]`-generated host `NativeInput` for `Scalar`
//! (a 2×128 leaf) and `Point`/`Signature` (composites), against the exact leaf-name
//! / limb contract the compiler's structural flatten produces. This is what the
//! deleted hand-written `host_inputs` module used to guarantee by hand.
#![allow(unexpected_cfgs)]
#![cfg(not(xark))]

use xark::__private::NativeInput;
use xark_secp256k1::{Point, Scalar, Signature};

#[test]
fn scalar_splits_into_two_128bit_limbs() {
    // Big-endian 32-byte value = 2·2^128 + 3  → lo128 = 3, hi128 = 2.
    let mut native = [0u8; 32];
    native[15] = 2; // 256^(31-15) = 2^128
    native[31] = 3; // 256^0
    let leaves = <Scalar as NativeInput>::leaves(&native, "f");
    assert_eq!(
        leaves,
        vec![
            ("f.limbs[0]".to_string(), "3".to_string()),
            ("f.limbs[1]".to_string(), "2".to_string()),
        ]
    );
}

#[test]
fn point_recurses_into_x_then_y() {
    // x = 7 (low byte at index 31), y = 9 (low byte at index 63).
    let mut native = [0u8; 64];
    native[31] = 7;
    native[63] = 9;
    let leaves = <Point as NativeInput>::leaves(&native, "q");
    assert_eq!(
        leaves,
        vec![
            ("q.x.limbs[0]".to_string(), "7".to_string()),
            ("q.x.limbs[1]".to_string(), "0".to_string()),
            ("q.y.limbs[0]".to_string(), "9".to_string()),
            ("q.y.limbs[1]".to_string(), "0".to_string()),
        ]
    );
}

#[test]
fn signature_recurses_into_r_then_s() {
    let mut native = [0u8; 64];
    native[31] = 4; // r low
    native[63] = 6; // s low
    let leaves = <Signature as NativeInput>::leaves(&native, "sig");
    assert_eq!(
        leaves,
        vec![
            ("sig.r.limbs[0]".to_string(), "4".to_string()),
            ("sig.r.limbs[1]".to_string(), "0".to_string()),
            ("sig.s.limbs[0]".to_string(), "6".to_string()),
            ("sig.s.limbs[1]".to_string(), "0".to_string()),
        ]
    );
}
