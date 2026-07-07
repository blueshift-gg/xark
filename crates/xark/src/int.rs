//! Fixed-width **signed** integers for circuits: [`I<N>`].
//!
//! The unsigned [`U<N>`](crate::uint::U) story, extended to negatives. An
//! `I<N>` holds a value in `[−2^(N−1), 2^(N−1))` — the same range as Rust's
//! `iN` — stored *field-native* (a negative `v` is the field element `p − |v|`,
//! so ordinary field `+`/`−` compute signed results directly).
//!
//! ## Representation and the cheap sign test
//!
//! Signedness is proven with a **bias**: `v ∈ [−2^(N−1), 2^(N−1))` iff the
//! biased value `v + 2^(N−1) ∈ [0, 2^N)`. Construction decomposes that biased
//! value into `N` bits (an `N`-bit range proof), and its top bit is the sign:
//! bit `N−1` is `1` exactly when `v ≥ 0`. That bit is a byproduct of the range
//! proof we already pay for, so it is **cached** — [`is_negative`](I::is_negative)
//! returns it for free, and [`is_positive`](I::is_positive) (`v > 0`, i.e.
//! `!is_zero & !is_negative`) costs only the ~2-constraint `is_zero`, never an
//! `N`-bit comparison.
//!
//! ## Cost model
//!
//! * `is_zero` / `is_eq` / `is_negative` / `is_positive`: ~2–3 constraints
//!   (`is_negative` is free — the cached sign bit).
//! * `lt` / `le` / `gt` / `ge`: ~`N + 2` constraints. Signed order equals the
//!   order of the biased values (a monotonic shift), so these reuse the same
//!   `N`-bit comparison as `U<N>`.
//! * `+` / `−` / unary `−`: *checked* — each re-proves its result is in signed
//!   range, so overflow (including `−I::MIN`) makes the circuit unsatisfiable
//!   rather than wrapping. Signed multiplication is intentionally not provided
//!   yet (its width/sign analysis wants its own review).

use crate::lang::{Bool, Field};
use crate::uint::{less_than, pow2_val};
use core::ops::{Add, AddAssign, Neg, Sub, SubAssign};

/// A signed `N`-bit integer: a field-native value proven to lie in
/// `[−2^(N−1), 2^(N−1))`, carrying its cached sign. `N` must be in `2..=253`
/// (a sign bit plus at least one magnitude bit, up to the BN254 field capacity).
#[derive(Clone, Copy)]
pub struct I<const N: usize> {
    /// Field-native signed value (`−k` is `p − k`).
    value: Field,
    /// Cached sign: true iff `value < 0`. Pinned at construction from the top
    /// bit of the biased decomposition, so it costs nothing to read.
    negative: Bool,
}

impl<const N: usize> I<N> {
    /// Compile-time guard: `N` must be a sound signed width for BN254.
    const WIDTH_OK: () = assert!(
        N >= 2 && N <= 253,
        "I<N>: N must be in 2..=253 (one sign bit + magnitude, within BN254)"
    );

    /// Build an `I<N>` from a field value, **proving in-circuit** that it lies in
    /// `[−2^(N−1), 2^(N−1))`. The biased value `value + 2^(N−1)` is decomposed to
    /// `N` bits (the range proof); its top bit is the sign, which is cached.
    pub fn new(value: Field) -> Self {
        let () = Self::WIDTH_OK;
        let biased = value + pow2_val(N - 1);
        // Proves `biased ∈ [0, 2^N)`, i.e. `value ∈ [−2^(N−1), 2^(N−1))`.
        let bits = biased.to_bits::<N>();
        // Bit `N−1` of the biased value is `1` iff `value ≥ 0`; the sign is its
        // complement. Each `to_bits` output is a pinned boolean, so `1 − top` is
        // a pinned `{0,1}` wire.
        let top = bits[N - 1];
        let negative = Bool::from_pinned(Field::from(1u8) - top);
        I { value, negative }
    }

    /// The underlying field-native signed value.
    pub fn value(self) -> Field {
        self.value
    }

    /// True iff the value is negative (`< 0`) — the cached sign bit, free.
    pub fn is_negative(self) -> Bool {
        self.negative
    }

    /// True iff the value is exactly `0`.
    pub fn is_zero(self) -> Bool {
        self.value.is_zero()
    }

    /// True iff the value is strictly positive (`> 0`), i.e. neither zero nor
    /// negative. Costs only the `is_zero` gadget — the sign bit is cached.
    pub fn is_positive(self) -> Bool {
        self.is_zero().not().and(self.negative.not())
    }

    /// True iff `self == other`.
    pub fn is_eq(self, other: I<N>) -> Bool {
        self.value.is_eq(other.value)
    }

    /// True iff `self < other` (signed).
    pub fn lt(self, other: I<N>) -> Bool {
        // Signed order equals the order of the biased values, both in `[0, 2^N)`.
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

    /// The biased value `value + 2^(N−1) ∈ [0, 2^N)` — a free linear form.
    fn biased(self) -> Field {
        self.value + pow2_val(N - 1)
    }
}

/// Signed fixed-width arithmetic via the standard operators, all *checked*: each
/// re-proves its result is in `[−2^(N−1), 2^(N−1))`, so overflow (including the
/// classic `−I::MIN`) makes the circuit unsatisfiable rather than wrapping.
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
