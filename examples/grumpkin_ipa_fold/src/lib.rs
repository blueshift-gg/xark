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

#![allow(clippy::assign_op_pattern)]

use xark_grumpkin::prelude::*;

/// Round challenge: the low 128 bits of `Poseidon2(seed, l.x, l.y, r.x, r.y)`
/// (Halo-style short challenge), returned as 128 little-endian bits ready for the
/// gadget's `scalar_mul` (`xark_poseidon2::challenge` decomposes the hash
/// canonically, so the challenge is a function of the transcript).
fn challenge(seed: Field, l: [Field; 2], r: [Field; 2]) -> [Field; 128] {
    xark_poseidon2::challenge::<5, 128>([seed, l[0], l[1], r[0], r[1]])
}

/// `x²·P` as two native 128-bit scalar-muls by the in-circuit challenge `x`
/// (no witness square needed).
fn sq_mul(x_bits: [Field; 128], p: [Field; 2]) -> [Field; 2] {
    scalar_mul(x_bits, scalar_mul(x_bits, p))
}

/// `x⁻²·P` as two wide (254-bit) muls by the witness inverse `x⁻¹`.
fn inv_sq_mul(inv: WideScalar, p: Affine) -> [Field; 2] {
    let q = wide_scalar_mul(inv, wide_scalar_mul(inv, p));
    [q.x, q.y]
}

/// One IPA round's transcript points: the cross commitments `L` and `R`.
#[input]
pub struct Round {
    pub l: Affine,
    pub r: Affine,
}

/// Verify the Halo IPA reduction for `n = 4` over Grumpkin. Public: generators
/// `Gⱼ`, `U`, and the commitment `P`. Witness: the transcript points `Lᵢ/Rᵢ`,
/// the mod-`p` inverses `xᵢ⁻¹`, the challenge-product scalars `sⱼ`, and the
/// final `a*` and `c = a*·b*` — all full-width scalars.
#[circuit]
pub fn grumpkin_ipa_fold(
    g: Public<[Affine; 4]>,
    u: Public<Affine>,
    p: Public<Affine>,
    rounds: Private<[Round; 2]>,
    x_inv: Private<[WideScalar; 2]>,
    s: Private<[WideScalar; 4]>,
    astar: Private<WideScalar>,
    c: Private<WideScalar>,
) {
    let pt = |q: Affine| [q.x, q.y];
    // --- round 0: seed with P.x, fold P ---
    let [r0, r1] = rounds;
    let x0 = challenge(p.x, pt(r0.l), pt(r0.r));
    let p1 = ec_add(
        ec_add(sq_mul(x0, pt(r0.l)), pt(p)),
        inv_sq_mul(x_inv[0], r0.r),
    );

    // --- round 1: seed with x0 (as a field element), fold again ---
    let x0_field = Field::from_bits::<128>(x0);
    let x1 = challenge(x0_field, pt(r1.l), pt(r1.r));
    let p2 = ec_add(ec_add(sq_mul(x1, pt(r1.l)), p1), inv_sq_mul(x_inv[1], r1.r));

    // --- deferred MSM: G* = Σⱼ sⱼ·Gⱼ ---
    let t: [Affine; 4] = core::array::from_fn(|j| wide_scalar_mul(s[j], g[j]));
    let g_final = ec_add(ec_add(pt(t[0]), pt(t[1])), ec_add(pt(t[2]), pt(t[3])));

    // --- final IPA relation: P₂ == a*·G* + c·U ---
    let g_final = Affine {
        x: g_final[0],
        y: g_final[1],
    };
    let rhs = ec_add(
        pt(wide_scalar_mul(astar, g_final)),
        pt(wide_scalar_mul(c, u)),
    );
    require_eq(p2[0], rhs[0]);
    require_eq(p2[1], rhs[1]);
}
