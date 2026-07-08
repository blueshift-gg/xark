//! Fixed-width unsigned integers for circuits: [`U<N>`].
//!
//! Carries the bit width in the type: the value is proven `∈ [0, 2^N)` once at
//! construction, so comparisons cost ~`N` constraints, not a full-field
//! (~253-bit) decomposition. Ordering on a bare [`Field`] is intentionally not a
//! circuit op. `is_zero`/`is_eq`/`is_positive` take the cheap inverse-hint path
//! (~2–3); `lt`/`le`/`gt`/`ge` cost ~`N + 2`. Every `U<N>` input (public too) is
//! range-proved in-circuit — `< 2^N` is not implied by Groth16's `< r` check.

use crate::lang::{Bool, Field};
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

    /// True iff the value is `0` (cheap inverse-hint path).
    pub fn is_zero(self) -> Bool {
        self.value.is_zero()
    }

    /// True iff the value is nonzero (i.e. `> 0` for an unsigned integer).
    pub fn is_positive(self) -> Bool {
        self.value.is_zero().not()
    }

    /// True iff `self == other`.
    pub fn is_eq(self, other: U<N>) -> Bool {
        self.value.is_eq(other.value)
    }

    /// True iff `self < other`. `le`/`gt`/`ge` route through this.
    pub fn lt(self, other: U<N>) -> Bool {
        less_than::<N>(self.value, other.value)
    }

    /// True iff `self <= other` (i.e. `!(other < self)`).
    pub fn le(self, other: U<N>) -> Bool {
        other.lt(self).not()
    }

    /// True iff `self > other`.
    pub fn gt(self, other: U<N>) -> Bool {
        other.lt(self)
    }

    /// True iff `self >= other`.
    pub fn ge(self, other: U<N>) -> Bool {
        self.lt(other).not()
    }

    // --- comparison against a compile-time constant --------------------------
    // `C` is a const generic (never range-proved); boundary cases fold to a cheap
    // gadget or a constant. `C` must fit in `u128`.

    /// True iff `self == C` (cheap: `self − C == 0`).
    pub fn eq_const<const C: u128>(self) -> Bool {
        (self.value - Field::from(C)).is_zero()
    }

    /// True iff `self < C`.
    pub fn lt_const<const C: u128>(self) -> Bool {
        if C == 0 {
            Bool::constant(false) // nothing < 0
        } else if N < 128 && C >= (1u128 << N) {
            Bool::constant(true) // every value < C
        } else {
            less_than::<N>(self.value, Field::from(C))
        }
    }

    /// True iff `self <= C`.
    pub fn le_const<const C: u128>(self) -> Bool {
        if N < 128 && C >= (1u128 << N) {
            Bool::constant(true)
        } else if C == 0 {
            self.value.is_zero() // `self <= 0` ⟺ `self == 0`
        } else {
            less_than::<N>(Field::from(C), self.value).not() // !(C < self)
        }
    }

    /// True iff `self > C`.
    pub fn gt_const<const C: u128>(self) -> Bool {
        if C == 0 {
            self.is_positive() // self > 0 ⟺ self ≠ 0
        } else if N < 128 && C >= (1u128 << N) {
            Bool::constant(false) // nothing exceeds C
        } else {
            less_than::<N>(Field::from(C), self.value) // C < self
        }
    }

    /// True iff `self >= C`.
    pub fn ge_const<const C: u128>(self) -> Bool {
        if C == 0 {
            Bool::constant(true) // every value >= 0
        } else if N < 128 && C >= (1u128 << N) {
            Bool::constant(false)
        } else {
            less_than::<N>(self.value, Field::from(C)).not() // !(self < C)
        }
    }
}

/// Checked fixed-width `+`/`-`/`*`: each re-range-proves its result to `N` bits,
/// so overflow/underflow is unsatisfiable. `Add`/`Sub` need `N ≤ 252`, `Mul`
/// needs `2N ≤ 252`. Ordering is not an operator — use `lt`/`le`/`gt`/`ge`.
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

/// `1` if `a < b`, else `0`, for `a, b ∈ [0, 2^N)`. Range-proves the remainder
/// `r` in `a - b + lt·2^N == r` to pin `lt`; needs `N ≤ 252`.
pub(crate) fn less_than<const N: usize>(a: Field, b: Field) -> Bool {
    // width guard for every comparison path (2^(N+1) must stay below r)
    const {
        assert!(
            N <= 252,
            "comparison requires N <= 252 so 2^(N+1) <= BN254 order"
        )
    };
    let two_pow_n = pow2::<N>();
    let top = Field::hint_bit(a - b + two_pow_n, N);
    top.assert_bool();
    let lt = Field::from(1u8) - top;
    let r = a - b + lt * two_pow_n;
    // range-prove r ∈ [0, 2^N), which pins `lt`
    let _bits = r.to_bits::<N>();
    Bool::from_pinned(lt)
}

/// `2^N` as a `Field` constant (folds to a constant, zero constraints).
fn pow2<const N: usize>() -> Field {
    let mut p = Field::from(1u8);
    let mut i = 0usize;
    while i < N {
        p = p + p;
        i += 1;
    }
    p
}

/// `2^n` as a `Field` constant for a const-propagated `n` — the value-argument
/// twin of [`pow2`] (zero constraints).
pub(crate) fn pow2_val(n: usize) -> Field {
    let mut p = Field::from(1u8);
    let mut i = 0usize;
    while i < n {
        p = p + p;
        i += 1;
    }
    p
}
