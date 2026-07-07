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
//! Proving `x ∈ [0, 2^N)` costs ~`N` constraints in-circuit. For a **private
//! witness** that is unavoidable — the verifier can't see it — so use
//! [`U::new`]. For a **public input**, the on-chain program can range-check it
//! natively (a `u64` compare in BPF is far cheaper than `N` R1CS rows); in that
//! case use [`U::from_public_range_checked_by_verifier`], which skips the
//! in-circuit proof on the explicit contract that the program enforces the
//! bound before calling `verify`.

use crate::lang::{Bool, Field};

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

    /// Build a `U<N>` from a public input **without** the in-circuit range
    /// proof, on the explicit contract that the on-chain verifier range-checks
    /// the value to `[0, 2^N)` before calling `verify`.
    ///
    /// This saves ~`N` constraints, but is **unsound for a private witness** —
    /// the verifier never sees private witnesses, so nothing would enforce the
    /// bound. Only use it for a public input whose range the program checks.
    pub fn from_public_range_checked_by_verifier(value: Field) -> Self {
        let () = Self::WIDTH_OK;
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

    /// True iff `self < other`.
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

    /// Checked addition: `self + other`, proving the sum fits in `N` bits.
    /// The circuit is unsatisfiable on overflow (`self + other >= 2^N`) — the
    /// sum `< 2^(N+1)` is re-range-proved to `N` bits, which forbids the carry.
    pub fn add(self, other: U<N>) -> U<N> {
        U::new(self.value + other.value)
    }

    /// Checked subtraction: `self − other`, proving `self >= other`. The circuit
    /// is unsatisfiable on underflow (`other > self`): the field difference then
    /// wraps to `~p`, far above `2^N`, and the range proof rejects it.
    pub fn sub(self, other: U<N>) -> U<N> {
        U::new(self.value - other.value)
    }

    /// Checked multiplication: `self · other`, proving the product fits in `N`
    /// bits. Requires `2N ≤ 252` so the product cannot wrap the field before the
    /// range check sees it.
    pub fn mul(self, other: U<N>) -> U<N> {
        let () = Self::MUL_WIDTH_OK;
        U::new(self.value * other.value)
    }
}

/// `1` if `a < b`, else `0`, for `a, b ∈ [0, 2^N)`.
///
/// `lt ∈ {0,1}` with an `N`-bit remainder `r` and the linear identity
/// `a - b + lt·2^N == r`, `r ∈ [0, 2^N)`. The range proof on `r` uniquely
/// forces `lt`: if `a >= b`, only `lt = 0` keeps `r = a - b` in range; if
/// `a < b`, only `lt = 1` keeps `r = a - b + 2^N` in range. `2^N < 2^254 < p`
/// (guaranteed by `N <= 253`), so the identity holds over the integers, not
/// just mod p.
///
/// The honest prover needs a *value* for `lt`, so it is derived from a hint:
/// bit `N` of `d = a - b + 2^N` is `1` iff `a >= b` (since `d ∈ [2^N, 2^{N+1})`
/// there) and `0` iff `a < b` (`d ∈ (0, 2^N)`). That hint only supplies a
/// candidate — its correctness is enforced by the remainder range proof, so a
/// wrong hint merely makes the circuit unsatisfiable, never unsound.
fn less_than<const N: usize>(a: Field, b: Field) -> Bool {
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
