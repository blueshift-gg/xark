//! Fixed-width signed integers for circuits: [`I<N>`].
//!
//! The [`U<N>`](crate::uint::U) story extended to negatives. Holds a value in
//! `[−2^(N−1), 2^(N−1))` stored field-native (`−v` is `p − v`). Signedness is
//! proven by biasing: `v + 2^(N−1) ∈ [0, 2^N)`, whose top bit is the sign — so
//! `is_negative` is a cached free read and `is_positive` costs only `is_zero`.
//! `lt`/`le`/`gt`/`ge` reuse the `U<N>` comparison on the biased values (~`N + 2`).
//! `+`/`−`/unary `−` are checked (overflow is unsatisfiable); no signed `*` yet.

use crate::lang::{Bool, Field};
use crate::uint::{less_than, pow2_val};
use core::ops::{Add, AddAssign, Neg, Sub, SubAssign};

/// A signed `N`-bit integer: a field-native value proven `∈ [−2^(N−1), 2^(N−1))`,
/// carrying its cached sign. `N` in `2..=253`.
#[derive(Clone, Copy)]
pub struct I<const N: usize> {
    /// Field-native signed value (`−k` is `p − k`).
    value: Field,
    /// Cached sign: true iff `value < 0` (from the biased decomposition's top bit).
    negative: Bool,
}

impl<const N: usize> I<N> {
    /// Compile-time guard: `N` must be a sound signed width for BN254.
    const WIDTH_OK: () = assert!(
        N >= 2 && N <= 253,
        "I<N>: N must be in 2..=253 (one sign bit + magnitude, within BN254)"
    );

    /// Build an `I<N>` from a field value, proving in-circuit it is `∈ [−2^(N−1), 2^(N−1))`.
    pub fn new(value: Field) -> Self {
        let () = Self::WIDTH_OK;
        let biased = value + pow2_val(N - 1);
        // proves biased ∈ [0, 2^N), i.e. value ∈ [−2^(N−1), 2^(N−1))
        let bits = biased.to_bits::<N>();
        // top bit is `1` iff value ≥ 0; sign is its complement (a pinned {0,1} wire)
        let top = bits[N - 1];
        let negative = Bool::from_pinned(Field::from(1u8) - top);
        I { value, negative }
    }

    /// The underlying field-native signed value.
    pub fn value(self) -> Field {
        self.value
    }

    /// True iff the value is negative (`< 0`) — the cached sign bit.
    pub fn is_negative(self) -> Bool {
        self.negative
    }

    /// True iff the value is exactly `0`.
    pub fn is_zero(self) -> Bool {
        self.value.is_zero()
    }

    /// True iff the value is strictly positive (`> 0`).
    pub fn is_positive(self) -> Bool {
        self.is_zero().not().and(self.negative.not())
    }

    /// True iff `self == other`.
    pub fn is_eq(self, other: I<N>) -> Bool {
        self.value.is_eq(other.value)
    }

    /// True iff `self < other` (signed).
    pub fn lt(self, other: I<N>) -> Bool {
        // signed order == order of the biased values
        less_than::<N>(self.biased(), other.biased())
    }

    /// True iff `self <= other` (signed).
    pub fn le(self, other: I<N>) -> Bool {
        other.lt(self).not()
    }

    /// True iff `self > other` (signed).
    pub fn gt(self, other: I<N>) -> Bool {
        other.lt(self)
    }

    /// True iff `self >= other` (signed).
    pub fn ge(self, other: I<N>) -> Bool {
        self.lt(other).not()
    }

    /// The biased value `value + 2^(N−1) ∈ [0, 2^N)`.
    fn biased(self) -> Field {
        self.value + pow2_val(N - 1)
    }
}

/// Checked signed `+`/`-`/unary `-`: each re-proves its result is in
/// `[−2^(N−1), 2^(N−1))`, so overflow (including `−I::MIN`) is unsatisfiable.
impl<const N: usize> Add for I<N> {
    type Output = I<N>;
    fn add(self, other: I<N>) -> I<N> {
        I::new(self.value + other.value)
    }
}
impl<const N: usize> Sub for I<N> {
    type Output = I<N>;
    fn sub(self, other: I<N>) -> I<N> {
        I::new(self.value - other.value)
    }
}
impl<const N: usize> Neg for I<N> {
    type Output = I<N>;
    fn neg(self) -> I<N> {
        I::new(Field::from(0u8) - self.value)
    }
}
impl<const N: usize> AddAssign for I<N> {
    fn add_assign(&mut self, other: I<N>) {
        *self = *self + other;
    }
}
impl<const N: usize> SubAssign for I<N> {
    fn sub_assign(&mut self, other: I<N>) {
        *self = *self - other;
    }
}
