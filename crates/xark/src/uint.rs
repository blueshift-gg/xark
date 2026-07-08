//! Fixed-width unsigned integers for circuits: [`U<N>`].
//!
//! Carries the bit width in the type: the value is proven `∈ [0, 2^N)` once at
//! construction, so comparisons cost ~`N` constraints, not a full-field
//! (~253-bit) decomposition. Ordering on a bare [`Field`] is intentionally not a
//! circuit op. `is_zero`/`is_eq`/`is_positive` take the cheap inverse-hint path
//! (~2–3); `lt`/`le`/`gt`/`ge` cost ~`N + 2`. Every `U<N>` input (public too) is
//! range-proved in-circuit — `< 2^N` is not implied by Groth16's `< r` check.

use crate::lang::{__xark_eq, __xark_ult, Field};
use core::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

/// An unsigned `N`-bit integer: a [`Field`] proven `∈ [0, 2^N)`. `N` in `1..=253`.
#[derive(Clone, Copy)]
pub struct U<const N: usize> {
    value: Field,
}

impl<const N: usize> U<N> {
    /// Compile-time guard: `N` must be a sound width for BN254.
    const WIDTH_OK: () = assert!(
        N >= 1 && N <= 253,
        "U<N>: N must be in 1..=253 (BN254 field capacity)"
    );
    /// Compile-time guard for `mul`: the `2N`-bit product must not wrap `Fr`.
    const MUL_WIDTH_OK: () = assert!(N <= 126, "U<N>::mul requires 2N ≤ 252 to avoid field wrap");
    /// Comparison and checked add/sub need `N ≤ 252` (the `2^(N+1)` intermediate
    /// must stay below `r`).
    const CMP_ARITH_WIDTH_OK: () = assert!(
        N <= 252,
        "U<N>: comparison and checked add/sub require N ≤ 252 so 2^(N+1) ≤ BN254 field order"
    );

    /// Build a `U<N>` from a field value, proving in-circuit it is `∈ [0, 2^N)`.
    pub fn new(value: Field) -> Self {
        let () = Self::WIDTH_OK;
        // `to_bits::<N>` proves `value < 2^N`
        let _bits = value.to_bits::<N>();
        U { value }
    }

    /// The underlying field value (guaranteed `∈ [0, 2^N)`).
    pub fn value(self) -> Field {
        self.value
    }

    /// True iff the value is `0`.
    pub fn is_zero(self) -> bool {
        self.value.is_zero()
    }

    /// True iff the value is nonzero (i.e. `> 0` for an unsigned integer).
    pub fn is_positive(self) -> bool {
        !self.value.is_zero()
    }

    // --- comparison against a compile-time constant --------------------------
    // `C` is a const generic (never range-proved); boundary cases fold to a cheap
    // gadget or a constant. `C` must fit in `u128`.

    /// True iff `self == C`.
    pub fn eq_const<const C: u128>(self) -> bool {
        __xark_eq(self.value, Field::from(C))
    }

    /// True iff `self < C`.
    pub fn lt_const<const C: u128>(self) -> bool {
        __xark_ult::<N>(self.value, Field::from(C))
    }

    /// True iff `self <= C` (i.e. `!(C < self)`).
    pub fn le_const<const C: u128>(self) -> bool {
        !__xark_ult::<N>(Field::from(C), self.value)
    }

    /// True iff `self > C` (i.e. `C < self`).
    pub fn gt_const<const C: u128>(self) -> bool {
        __xark_ult::<N>(Field::from(C), self.value)
    }

    /// True iff `self >= C` (i.e. `!(self < C)`).
    pub fn ge_const<const C: u128>(self) -> bool {
        !__xark_ult::<N>(self.value, Field::from(C))
    }
}

/// `U<N>` equality and ordering are circuit operations returning a `bool` wire:
/// `==` `!=` `<` `<=` `>` `>=` all work naturally.
impl<const N: usize> PartialEq for U<N> {
    fn eq(&self, other: &U<N>) -> bool {
        __xark_eq(self.value, other.value)
    }
}
impl<const N: usize> PartialOrd for U<N> {
    fn partial_cmp(&self, _other: &U<N>) -> Option<core::cmp::Ordering> {
        // Never lowered: the operator methods below are overridden and lowered
        // directly by the compiler. A witness has no host value to order.
        unreachable!("U<N> has no host ordering")
    }
    fn lt(&self, other: &U<N>) -> bool {
        __xark_ult::<N>(self.value, other.value)
    }
    fn le(&self, other: &U<N>) -> bool {
        !__xark_ult::<N>(other.value, self.value)
    }
    fn gt(&self, other: &U<N>) -> bool {
        __xark_ult::<N>(other.value, self.value)
    }
    fn ge(&self, other: &U<N>) -> bool {
        !__xark_ult::<N>(self.value, other.value)
    }
}

/// Checked fixed-width `+`/`-`/`*`: each re-range-proves its result to `N` bits,
/// so overflow/underflow is unsatisfiable. `Add`/`Sub` need `N ≤ 252`, `Mul`
/// needs `2N ≤ 252`.
impl<const N: usize> Add for U<N> {
    type Output = U<N>;
    fn add(self, other: U<N>) -> U<N> {
        let () = Self::CMP_ARITH_WIDTH_OK;
        U::new(self.value + other.value)
    }
}
impl<const N: usize> Sub for U<N> {
    type Output = U<N>;
    fn sub(self, other: U<N>) -> U<N> {
        let () = Self::CMP_ARITH_WIDTH_OK;
        U::new(self.value - other.value)
    }
}
impl<const N: usize> Mul for U<N> {
    type Output = U<N>;
    fn mul(self, other: U<N>) -> U<N> {
        let () = Self::MUL_WIDTH_OK;
        U::new(self.value * other.value)
    }
}
impl<const N: usize> AddAssign for U<N> {
    fn add_assign(&mut self, other: U<N>) {
        *self = *self + other;
    }
}
impl<const N: usize> SubAssign for U<N> {
    fn sub_assign(&mut self, other: U<N>) {
        *self = *self - other;
    }
}
impl<const N: usize> MulAssign for U<N> {
    fn mul_assign(&mut self, other: U<N>) {
        *self = *self * other;
    }
}

/// `2^n` as a `Field` constant for a const-propagated `n` (zero constraints).
pub(crate) fn pow2_val(n: usize) -> Field {
    let mut p = Field::from(1u8);
    let mut i = 0usize;
    while i < n {
        p = p + p;
        i += 1;
    }
    p
}
