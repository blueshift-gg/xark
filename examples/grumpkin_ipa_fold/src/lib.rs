//! **Verify a full Halo-style Grumpkin IPA reduction inside a BN254 Groth16
//! circuit — with an in-circuit Poseidon2 Fiat–Shamir transcript.** (Milestone 2,
//! building on the deferred-MSM of `grumpkin_ipa`.)
//!
//! For `n = 4` (`k = 2` folding rounds) the circuit checks the IPA group
//! relations, deriving the round challenges **in-circuit** from the transcript
//! so they are bound (not trusted inputs):
//!
//! ```text
//!   xᵢ   = low128( Poseidon2(seedᵢ, Lᵢ.x, Lᵢ.y, Rᵢ.x, Rᵢ.y) )   // native
//!   P₂   = x₁²·L₁ + (x₀²·L₀ + P + x₀⁻²·R₀) + x₁⁻²·R₁              // fold
//!   G*   = Σⱼ sⱼ·Gⱼ                                              // deferred MSM
//!   check  P₂ == a*·G* + c·U                                     // final IPA rel
//! ```
//!
//! `xᵢ²·Lᵢ` is two native 128-bit scalar-muls by the in-circuit `xᵢ`, so the
//! squaring needs no witness. The **only** honestly-deferred values are the
//! mod-`p` inverse `xᵢ⁻¹` and the challenge-product / final scalars
//! (`sⱼ, a*, c`) — the companion curve's job in a real 2-cycle — supplied as
//! bound 127-bit-limb witnesses; the circuit pins the *group* equations
//! relative to them. Poseidon2 here is the same permutation as the host
//! `poseidon2` crate (KAT-identical), so the in-circuit challenges match the
//! prover's transcript exactly.
//!
//! The Fiat–Shamir binding + native folding is the reusable core of a
//! Grumpkin-cycle folding *recursion* step's in-circuit verifier.

#![cfg_attr(xark, no_std)]
#![allow(clippy::assign_op_pattern)]

use xark_grumpkin::prelude::*;

fn offset_o() -> [Field; 2] {
    [
        Field::from(5u8),
        Field::from("26447525821777463057023244913909144251512587297343525263882"),
    ]
}

/// `corr₂₅₄ = −(2^254·O)` (validated against the gadget's `corr₁₂₈`).
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

fn mux(bit: Field, t: [Field; 2], f: [Field; 2]) -> [Field; 2] {
    [f[0] + bit * (t[0] - f[0]), f[1] + bit * (t[1] - f[1])]
}

/// Full-width (254-bit) variable-base scalar mul, `s = lo + hi·2^127`.
fn wide_scalar_mul(lo: Field, hi: Field, p: [Field; 2]) -> [Field; 2] {
    enforce_on_curve(p);
    let lo_bits = lo.to_bits::<127>();
    let hi_bits = hi.to_bits::<127>();
    let mut acc = offset_o();
    let mut i = 0usize;
    while i < 254usize {
        acc = ec_double(acc);
        let idx = 253usize - i;
        let bit = if idx < 127usize {
            lo_bits[idx]
        } else {
            hi_bits[idx - 127usize]
        };
        let cand = ec_add(acc, p);
        acc = mux(bit, cand, acc);
        i += 1;
    }
    ec_add(acc, corr254())
}

/// Little-endian bits of the BN254 scalar-field modulus `r` (bit 253 set, so a
/// uniform `Fr` element can be 254 bits — `to_bits::<253>` can't hold it).
const R_BITS: [u8; 254] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1,
    1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0,
    1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0,
    0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0,
    1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1,
    0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1,
    1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1,
    0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1,
];

/// Canonically decompose a full field element `h` into 254 little-endian bits:
/// boolean, recomposition-pinned to `h`, **and** enforced `< r` (bit-serial,
/// MSB-first, branch-free). Needed because a Poseidon output can be 254 bits, so
/// `to_bits::<253>` (which relies on `2^253 < r` for injectivity) can't hold it.
fn canonical_bits(h: Field) -> [Field; 254] {
    let mut bits = [Field::from(0u8); 254];
    let mut i = 0usize;
    while i < 254usize {
        bits[i] = Field::hint_bit(h, i);
        i += 1;
    }
    let mut i = 0usize;
    while i < 254usize {
        bits[i].require_bool();
        i += 1;
    }
    // recompose == h
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 254usize {
        acc = acc + bits[i] * pow;
        pow = pow + pow;
        i += 1;
    }
    require_eq(acc, h);
    // enforce value < r, MSB-first: `lt` flips to 1 at the first bit where the
    // value is 0 and r is 1 (equal prefix); a value-1/r-0 on the equal prefix is
    // forbidden. r's bits are Field constants, so there is no data-dependent branch.
    let mut undecided = Field::from(1u8);
    let mut lt = Field::from(0u8);
    let one = Field::from(1u8);
    let two = Field::from(2u8);
    let mut i = 0usize;
    while i < 254usize {
        let idx = 253usize - i;
        let vi = bits[idx];
        let ri = Field::from(R_BITS[idx]);
        lt = lt + undecided * (one - vi) * ri;
        require_eq(undecided * vi * (one - ri), Field::from(0u8));
        // undecided stays set only while vi == ri (XNOR)
        let agree = one - (vi + ri - two * vi * ri);
        undecided = undecided * agree;
        i += 1;
    }
    require_eq(lt, one);
    bits
}

/// Round challenge: the low 128 bits of `Poseidon2(seed, l.x, l.y, r.x, r.y)`
/// (Halo-style short challenge), returned as 128 little-endian bits ready for the
/// gadget's `scalar_mul`. The full output is canonically decomposed so the
/// challenge is a deterministic, uniquely-pinned function of the transcript.
fn challenge(seed: Field, l: [Field; 2], r: [Field; 2]) -> [Field; 128] {
    let h = xark_poseidon2::hash([seed, l[0], l[1], r[0], r[1]]);
    let bits = canonical_bits(h);
    let mut out = [Field::from(0u8); 128];
    let mut i = 0usize;
    while i < 128usize {
        out[i] = bits[i];
        i += 1;
    }
    out
}

/// `x²·P` as two native 128-bit scalar-muls by the in-circuit challenge `x`
/// (no witness square needed).
fn sq_mul(x_bits: [Field; 128], p: [Field; 2]) -> [Field; 2] {
    scalar_mul(x_bits, scalar_mul(x_bits, p))
}

/// `x⁻²·P` as two wide (254-bit) muls by the witness inverse `x⁻¹ = lo + hi·2^127`.
fn inv_sq_mul(inv_lo: Field, inv_hi: Field, p: [Field; 2]) -> [Field; 2] {
    wide_scalar_mul(inv_lo, inv_hi, wide_scalar_mul(inv_lo, inv_hi, p))
}

/// Verify the Halo IPA reduction for `n = 4` over Grumpkin. Public: generators
/// `Gⱼ`, `U`, and the commitment `P`. Witness: the transcript points `Lᵢ/Rᵢ`,
/// the mod-`p` inverses `xᵢ⁻¹`, the challenge-product scalars `sⱼ`, and the
/// final `a*` and `c = a*·b*` — all as 127-bit limb pairs.
#[circuit]
#[allow(clippy::too_many_arguments)]
pub fn grumpkin_ipa_fold(
    g0: Public<Affine>,
    g1: Public<Affine>,
    g2: Public<Affine>,
    g3: Public<Affine>,
    u: Public<Affine>,
    p: Public<Affine>,
    l0: Private<Affine>,
    r0: Private<Affine>,
    l1: Private<Affine>,
    r1: Private<Affine>,
    x0inv_lo: Private<Field>,
    x0inv_hi: Private<Field>,
    x1inv_lo: Private<Field>,
    x1inv_hi: Private<Field>,
    s0_lo: Private<Field>,
    s0_hi: Private<Field>,
    s1_lo: Private<Field>,
    s1_hi: Private<Field>,
    s2_lo: Private<Field>,
    s2_hi: Private<Field>,
    s3_lo: Private<Field>,
    s3_hi: Private<Field>,
    astar_lo: Private<Field>,
    astar_hi: Private<Field>,
    c_lo: Private<Field>,
    c_hi: Private<Field>,
) {
    // --- round 0: seed with P.x, fold P ---
    let x0 = challenge(p.x, [l0.x, l0.y], [r0.x, r0.y]);
    let p1 = ec_add(
        ec_add(sq_mul(x0, [l0.x, l0.y]), [p.x, p.y]),
        inv_sq_mul(x0inv_lo, x0inv_hi, [r0.x, r0.y]),
    );

    // --- round 1: seed with x0 (as a field element), fold again ---
    let x0_field = Field::from_bits::<128>(x0);
    let x1 = challenge(x0_field, [l1.x, l1.y], [r1.x, r1.y]);
    let p2 = ec_add(
        ec_add(sq_mul(x1, [l1.x, l1.y]), p1),
        inv_sq_mul(x1inv_lo, x1inv_hi, [r1.x, r1.y]),
    );

    // --- deferred MSM: G* = Σⱼ sⱼ·Gⱼ ---
    let g_final = ec_add(
        ec_add(
            wide_scalar_mul(s0_lo, s0_hi, [g0.x, g0.y]),
            wide_scalar_mul(s1_lo, s1_hi, [g1.x, g1.y]),
        ),
        ec_add(
            wide_scalar_mul(s2_lo, s2_hi, [g2.x, g2.y]),
            wide_scalar_mul(s3_lo, s3_hi, [g3.x, g3.y]),
        ),
    );

    // --- final IPA relation: P₂ == a*·G* + c·U ---
    let rhs = ec_add(
        wide_scalar_mul(astar_lo, astar_hi, g_final),
        wide_scalar_mul(c_lo, c_hi, [u.x, u.y]),
    );
    require_eq(p2[0], rhs[0]);
    require_eq(p2[1], rhs[1]);
}
