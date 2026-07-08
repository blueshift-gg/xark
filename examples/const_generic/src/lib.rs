//! Const-generic gadget support: a function generic over `const N: usize` is
//! monomorphized per instantiation, with `N` const-folded in loop bounds and
//! `[Field; N]` local arrays. This is the enabler for caller-chosen limb
//! widths (see the `Bignum` gadget).
#![no_std]
use xark::{assert_eq, Field, Private, Public};

/// Elementwise-double `N` limbs, then sum them.
fn double_and_sum<const N: usize>(a: [Field; N]) -> Field {
    let mut doubled = [Field::from(0u8); N];
    let mut i = 0usize;
    while i < N {
        doubled[i] = a[i] + a[i];
        i += 1;
    }
    let mut acc = Field::from(0u8);
    let mut j = 0usize;
    while j < N {
        acc = acc + doubled[j];
        j += 1;
    }
    acc
}

pub fn circuit(a: Private<Field>, b: Private<Field>, c: Private<Field>, out: Public<Field>) {
    // double_and_sum::<3> = 2(a+b+c); double_and_sum::<2> = 2(a+b)
    assert_eq(double_and_sum::<3>([a, b, c]) + double_and_sum::<2>([a, b]), out);
}
