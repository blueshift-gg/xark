//! **Verify a compact Grumpkin IPA / folding accumulator claim inside a BN254
//! Groth16 circuit — natively.**
//!
//! ## Why this is efficient (the thesis)
//!
//! A BN254 Groth16 circuit is R1CS over `Fr_BN254`. Grumpkin is `y² = x³ − 17`
//! over `F_p` with **`p = Fr_BN254`**, so a Grumpkin point's coordinates are
//! ordinary circuit `Field`s and every group op (`ec_add`/`ec_double`) is a
//! handful of *native* constraints — no non-native limb emulation. That is the
//! whole point of the BN254↔Grumpkin 2-cycle, and it makes the compute-heavy
//! half of IPA/accumulation verification cheap.
//!
//! ## What this circuit verifies (the group half — stated honestly)
//!
//! The heart of a Halo-style IPA accumulator is the **deferred MSM** it stands
//! for: `Q = Σⱼ sⱼ·Gⱼ`. This circuit verifies exactly that relation over
//! Grumpkin, for `n = 4` generators, with **full-width** (`< p < 2^254`)
//! scalars. Verifying it *is* discharging the accumulator's defining claim.
//!
//! The cycle-of-curves boundary, stated plainly: Grumpkin's **scalar** field is
//! `Fq_BN254` (`p > r`), so scalar-field arithmetic (squaring/inverting Fiat–
//! Shamir challenges, the challenge→`sⱼ` products) **cannot be done soundly in
//! this circuit** — that is the companion curve's job in a real 2-cycle. Here
//! the scalars `sⱼ` enter as **bound witnesses** (as two 127-bit limbs), and the
//! circuit soundly pins the *group equation* relative to them. That is the
//! part the native-coordinate match makes efficient.
//!
//! ## Scalars wider than the field
//!
//! `Fr`'s `to_bits` tops out below `p`, and a single `Field` can't hold a scalar
//! `≥ r`. So each scalar is passed as two 127-bit limbs `s = lo + hi·2^127`
//! (both `< 2^127 < r`, injective), concatenated to 254 bits and run through a
//! wide offset-accumulator double-and-add — the gadget's 128-bit `scalar_mul`
//! widened to 254 bits with a regenerated `corr = −(2^254·O)` (validated
//! off-circuit against the gadget's own `corr₁₂₈`).

// Written in the `x = x + y` style (`+=` on `Field` works too).
#![allow(clippy::assign_op_pattern)]

use xark_grumpkin::prelude::*;

/// `Q = Σⱼ sⱼ·Gⱼ` over four generators, with full-width scalars.
#[circuit]
pub fn grumpkin_ipa(g: Public<[Affine; 4]>, s: Private<[WideScalar; 4]>, q: Public<Affine>) {
    let t: [Affine; 4] = core::array::from_fn(|j| wide_scalar_mul(s[j], g[j]));
    // Σⱼ sⱼ·Gⱼ via native incomplete affine addition (operands are distinct
    // random-looking points, off the incomplete-addition edge w.h.p.).
    let pt = |p: Affine| [p.x, p.y];
    let acc = ec_add(ec_add(pt(t[0]), pt(t[1])), ec_add(pt(t[2]), pt(t[3])));
    require_eq(acc[0], q.x);
    require_eq(acc[1], q.y);
}
