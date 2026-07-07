//! Fixed-width unsigned integers for circuits: [`U<N>`].
//!
//! A field element is a residue mod p with no meaningful order, and comparing
//! two of them naively would force a decomposition over the *whole* field
//! (~253 bits). [`U<N>`] carries the bit width in the type: its value is proven
//! to lie in `[0, 2^N)` once (at construction), and every comparison is then
//! bounded by `N`, not the field size. This is the circuit-native way to do
//! ordering — `<`, `>` on a bare [`Field`] are intentionally not circuit
//! operations (see [`Field`]).
//!
//! ## Cost model (this is where conventional logic doesn't apply)
//!
//! * `is_zero` / `is_eq` / `is_positive` are the cheap inverse-hint path
//!   (~2–3 constraints), **not** a bit decomposition. `x > 0` on an unsigned
//!   integer is just `!is_zero(x)`.
//! * `lt` / `le` / `gt` / `ge` cost ~`N + 2` constraints: one `N`-bit range
//!   proof of a remainder plus a boolean. See [`less_than`].
//!
//! ## Range checks: circuit vs. verifier
//!
//! Proving `x ∈ [0, 2^N)` costs ~`N` constraints in-circuit. Where that proof
//! lives is decided by how the value enters the circuit:
//!
//! Every `U<N>` *input* — `Private<U<N>>` or `Public<U<N>>` — is range-proved
//! in-circuit: the compiler injects the `N`-bit proof at the input boundary.
//! Public inputs are proved too, because `< 2^N` is **not** implied by Groth16's
//! `< r` public-input check, and the comparison gadget relies on the bound — an
//! unchecked public `U<N>` fed to `lt`/`gt` would let a prover force a wrong
//! result. (A verifier-side range check could reclaim the ~`N` rows for public
//! inputs, but only once the width is exported and enforced downstream; until
//! then, in-circuit is the sound default.) [`U::new`] is the same proof for a
//! `Field` computed inside the circuit.

use crate::lang::{Bool, Field};
use core::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

/// An unsigned `N`-bit integer: a [`Field`] whose value is guaranteed to lie in
/// `[0, 2^N)`. `N` must be in `1..=253` (the BN254 scalar field holds values
/// `< 2^253` uniquely, so wider ranges are not injective — see the `MAX_BITS`
/// discussion in `docs/security.md`).
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
    /// Compile-time guard for comparison and checked add/sub. These form an
    /// intermediate up to `2^(N+1)` (a borrow term `lt·2^N` added to a difference,
    /// or a two-operand sum), which must stay below the BN254 order `r < 2^254`
    /// for the range proof to bind over the integers — so `2^(N+1) ≤ r`, i.e.
    /// `N ≤ 252`. A bare `U::new` range proof needs only `2^N ≤ r` (`N ≤ 253`).
    const CMP_ARITH_WIDTH_OK: () = assert!(
        N <= 252,
        "U<N>: comparison and checked add/sub require N ≤ 252 so 2^(N+1) ≤ BN254 field order"
    );

    /// Build a `U<N>` from a field value, **proving in-circuit** that it lies in
    /// `[0, 2^N)` (an `N`-bit range proof). Use this for private witnesses.
    pub fn new(value: Field) -> Self {
        let () = Self::WIDTH_OK;
        // `to_bits::<N>` pins the `N` bits boolean and their recomposition to
        // `value`, which proves `value < 2^N`. The bits themselves are not
        // retained: comparisons range-prove their own remainder.
        let _bits = value.to_bits::<N>();
        U { value }
    }

    /// The underlying field value (guaranteed `∈ [0, 2^N)`).
    pub fn value(self) -> Field {
        self.value
    }

    /// True iff the value is `0` — the cheap inverse-hint path (~2–3
    /// constraints), not an `N`-bit decomposition.
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

    /// True iff `self < other`. `le`/`gt`/`ge` route through this, so the width
    /// guard here covers them too.
    pub fn lt(self, other: U<N>) -> Bool {
        let () = Self::CMP_ARITH_WIDTH_OK;
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
    //
    // Comparing against a literal via `self.gt(U::new(C))` would first *construct*
    // a `U<N>` for `C` — paying an `N`-bit range proof for a value already known
    // to be in range — and then compare (another ~`N`). These `*_const` methods
    // take `C` as a const generic instead: they never range-prove the constant,
    // and the boundary cases fold to a cheap gadget or a constant. In particular
    // `gt_const::<0>()` is `is_positive` (~2 constraints), not an `N`-bit compare.
    // `C` is a `u128`, so constants must fit in 128 bits (as with `Field::from`).

    /// True iff `self == C`. Cheap (~2 constraints) for every `C`: `self − C == 0`.
    pub fn eq_const<const C: u128>(self) -> Bool {
        (self.value - Field::from(C)).is_zero()
    }

    /// True iff `self < C`.
    pub fn lt_const<const C: u128>(self) -> Bool {
        if C == 0 {
            Bool::constant(false) // no unsigned value is below 0
        } else if N < 128 && C >= (1u128 << N) {
            Bool::constant(true) // every value in `[0, 2^N)` is below `C`
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
            self.is_positive() // `self > 0` ⟺ `self ≠ 0` — the cheap path
        } else if N < 128 && C >= (1u128 << N) {
            Bool::constant(false) // nothing in `[0, 2^N)` exceeds `C`
        } else {
            less_than::<N>(Field::from(C), self.value) // C < self
        }
    }

    /// True iff `self >= C`.
    pub fn ge_const<const C: u128>(self) -> Bool {
        if C == 0 {
            Bool::constant(true) // every unsigned value is `>= 0`
        } else if N < 128 && C >= (1u128 << N) {
            Bool::constant(false)
        } else {
            less_than::<N>(self.value, Field::from(C)).not() // !(self < C)
        }
    }
}

/// Fixed-width arithmetic uses the standard operators (`a + b`, `a - b`,
/// `a * b`) and is *checked*: each operation re-range-proves its result to `N`
/// bits, so overflow/underflow makes the circuit unsatisfiable rather than
/// silently wrapping the field. `Add`/`Sub` require `N ≤ 252` (`CMP_ARITH_WIDTH_OK`):
/// the two-operand sum, and the wrapped value of an underflowing difference, reach
/// `~2^(N+1)`, which must stay below `r` or an out-of-range result could wrap back
/// under `2^N` and pass the range proof. `Mul` requires the stricter `2N ≤ 252`
/// so the product cannot wrap `Fr` before the range check sees it.
///
/// Ordering is deliberately *not* an operator: `<`/`>` must return `bool`, but a
/// circuit comparison yields a [`Bool`] wire, so use `lt`/`le`/`gt`/`ge`.
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

/// `1` if `a < b`, else `0`, for `a, b ∈ [0, 2^N)`.
///
/// `lt ∈ {0,1}` with an `N`-bit remainder `r` and the linear identity
/// `a - b + lt·2^N == r`, `r ∈ [0, 2^N)`. The range proof on `r` uniquely
/// forces `lt`: if `a >= b`, only `lt = 0` keeps `r = a - b` in range; if
/// `a < b`, only `lt = 1` keeps `r = a - b + 2^N` in range. The intermediate
/// `d = a - b + 2^N` reaches `2^(N+1)`, which must stay below the BN254 order
/// `r` (note `r < 2^254`) for the identity to hold over the integers rather than
/// mod `r` — hence `2^(N+1) ≤ r`, i.e. `N ≤ 252` (enforced by `CMP_ARITH_WIDTH_OK`).
///
/// The honest prover needs a *value* for `lt`, so it is derived from a hint:
/// bit `N` of `d = a - b + 2^N` is `1` iff `a >= b` (since `d ∈ [2^N, 2^{N+1})`
/// there) and `0` iff `a < b` (`d ∈ (0, 2^N)`). That hint only supplies a
/// candidate — its correctness is enforced by the remainder range proof, so a
/// wrong hint merely makes the circuit unsatisfiable, never unsound.
pub(crate) fn less_than<const N: usize>(a: Field, b: Field) -> Bool {
    let two_pow_n = pow2::<N>();
    let top = Field::hint_bit(a - b + two_pow_n, N);
    top.assert_bool();
    let lt = Field::from(1u8) - top;
    let r = a - b + lt * two_pow_n;
    // Range-prove `r ∈ [0, 2^N)`; this is what pins `lt` to `{0,1}` and correct.
    let _bits = r.to_bits::<N>();
    Bool::from_pinned(lt)
}

/// `2^N` as a `Field` constant. Built by `N` doublings of `1`; every step folds
/// two constants during lowering, so this emits **zero** constraints — it is
/// just the constant `2^N`.
fn pow2<const N: usize>() -> Field {
    let mut p = Field::from(1u8);
    let mut i = 0usize;
    while i < N {
        p = p + p;
        i += 1;
    }
    p
}

/// `2^n` as a `Field` constant for a runtime (but compile-time-constant) `n` —
/// the value-argument twin of [`pow2`], for widths like `N-1` that can't be
/// written as a const-generic without `generic_const_exprs`. `n` is always
/// const-propagated at a call site, so the loop unrolls and folds to the
/// constant `2^n` — zero constraints.
pub(crate) fn pow2_val(n: usize) -> Field {
    let mut p = Field::from(1u8);
    let mut i = 0usize;
    while i < n {
        p = p + p;
        i += 1;
    }
    p
}
