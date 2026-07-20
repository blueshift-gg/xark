//! Exercises the sound non-native comparison-bit primitive `xark_bignum::is_lt`:
//! constrain `is_lt(a, b) == claim` for two 2×64-bit limb values. Used by
//! `xark-bignum`'s `compare` solve/analyzer test — a wrong `claim` is rejected,
//! and the derived comparison bit is fully pinned (analyzer-clean).
#![no_std]

use xark_bignum::prelude::*;

pub fn circuit(a: Public<[Field; 2]>, b: Public<[Field; 2]>, claim: Public<Field>) {
    assert_eq(is_lt::<2, 64>(a, b), claim);
}
