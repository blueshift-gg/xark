//! Const-generic gadget support: a function generic over `const N: usize` is
//! monomorphized per instantiation, with `N` const-folded in loop bounds and
//! `[Field; N]` local arrays. This is the enabler for caller-chosen limb
//! widths (see the `Bignum` gadget).
#![cfg_attr(xark, no_std)]
use xark::{assert_eq, circuit, Field, Private, Public};

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

#[circuit]
pub fn const_generic(a: Private<Field>, b: Private<Field>, c: Private<Field>, out: Public<Field>) {
    // double_and_sum::<3> = 2(a+b+c); double_and_sum::<2> = 2(a+b)
    assert_eq(double_and_sum::<3>([a, b, c]) + double_and_sum::<2>([a, b]), out);
}

#[cfg(test)]
mod tests {
    use super::const_generic;

    #[test]
    fn accepts_valid() {
        // 2(1+2+3) + 2(1+2) = 12 + 6 = 18
        const_generic("1".into(), "2".into(), "3".into(), "18".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(const_generic("1".into(), "2".into(), "3".into(), "19".into()).is_err());
    }
}
