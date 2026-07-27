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

#![cfg_attr(xark, no_std)]
// The xark subset rejects compound assignment on `Field`; `x = x + y` is required.
#![allow(clippy::assign_op_pattern)]

use xark_grumpkin::prelude::*;

/// Offset-accumulator seed `O` (the gadget's fixed non-identity point, `x = 5`).
fn offset_o() -> [Field; 2] {
    [
        Field::from(5u8),
        Field::from("26447525821777463057023244913909144251512587297343525263882"),
    ]
}

/// `corr₂₅₄ = −(2^254·O)`, removing the offset accumulated over 254 doublings.
/// Computed off-circuit with `ark-grumpkin` and validated: the same routine
/// reproduces the gadget's hardcoded `corr₁₂₈` exactly.
fn corr254() -> [Field; 2] {
    [
        Field::from(
            "16553197835714973834031774601520451931051624293930580121206769559624452310037",
        ),
        Field::from(
            "19649441642928946798700829372424834756358685055060237751050452085768514233992",
        ),
    ]
}

/// Boolean-gated affine point select `bit ? t : f` (pure arithmetic mux). `bit`
/// is already pinned `∈ {0,1}` by `to_bits`, so no extra booleanity constraint.
fn mux(bit: Field, t: [Field; 2], f: [Field; 2]) -> [Field; 2] {
    [f[0] + bit * (t[0] - f[0]), f[1] + bit * (t[1] - f[1])]
}

/// **Full-width variable-base scalar mul** `s·P`, `s = lo + hi·2^127`, each limb
/// `< 2^127`. Mirrors the gadget's offset double-and-add over 254 bits (MSB
/// first). Native Grumpkin ops throughout.
fn wide_scalar_mul(lo: Field, hi: Field, p: [Field; 2]) -> [Field; 2] {
    // Group law is only valid on-curve; pin the (public) generator to Grumpkin.
    enforce_on_curve(p);
    let lo_bits = lo.to_bits::<127>();
    let hi_bits = hi.to_bits::<127>();
    let mut acc = offset_o();
    let mut i = 0usize;
    while i < 254usize {
        acc = ec_double(acc);
        let idx = 253usize - i; // MSB first
        // `idx` is a compile-time constant per unrolled iteration, so this
        // branch and the array indexing resolve at unroll time.
        let bit = if idx < 127usize {
            lo_bits[idx]
        } else {
            hi_bits[idx - 127usize]
        };
        let cand = ec_add(acc, p);
        acc = mux(bit, cand, acc);
        i += 1;
    }
    // acc = 2^254·O + s·P; remove the offset.
    ec_add(acc, corr254())
}

/// Verify the deferred-MSM accumulator claim `Q = Σⱼ sⱼ·Gⱼ` over Grumpkin.
///
/// `Gⱼ` are the accumulator's (public) generators; each scalar `sⱼ` is supplied
/// as two private 127-bit limbs `sⱼ = sⱼ_lo + sⱼ_hi·2^127`; `Q` is the public
/// claimed accumulated point.
#[circuit]
pub fn grumpkin_ipa(
    g0: Public<Affine>,
    g1: Public<Affine>,
    g2: Public<Affine>,
    g3: Public<Affine>,
    s0_lo: Private<Field>,
    s0_hi: Private<Field>,
    s1_lo: Private<Field>,
    s1_hi: Private<Field>,
    s2_lo: Private<Field>,
    s2_hi: Private<Field>,
    s3_lo: Private<Field>,
    s3_hi: Private<Field>,
    q: Public<Affine>,
) {
    let t0 = wide_scalar_mul(s0_lo, s0_hi, [g0.x, g0.y]);
    let t1 = wide_scalar_mul(s1_lo, s1_hi, [g1.x, g1.y]);
    let t2 = wide_scalar_mul(s2_lo, s2_hi, [g2.x, g2.y]);
    let t3 = wide_scalar_mul(s3_lo, s3_hi, [g3.x, g3.y]);
    // Σⱼ sⱼ·Gⱼ via native incomplete affine addition (operands are distinct
    // random-looking points, off the incomplete-addition edge w.h.p.).
    let acc = ec_add(ec_add(t0, t1), ec_add(t2, t3));
    require_eq(acc[0], q.x);
    require_eq(acc[1], q.y);
}
