//! **A minimal end-to-end folding IVC, verified in a BN254 Groth16 circuit.**
//!
//! Two recursion steps: a computation `z_{i+1} = F(z_i)` (`F(z) = z² + 5`) run
//! twice, alongside a folding accumulator that folds one committed instance per
//! step. Both chains are checked in one circuit and bound together — each fold's
//! Fiat–Shamir challenge commits to the step's computation output `z_{i+1}`, so
//! the accumulator can't be folded against a different computation.
//!
//! ```text
//!   z0 --F--> z1 --F--> z2                       (computation chain)
//!   U0 --fold(s0,T0)--> U1 --fold(s1,T1)--> U2   (accumulator chain)
//!         r0=H(U0,s0,T0,z1)   r1=H(U1,s1,T1,z2)   (FS ties them together)
//! ```
//!
//! Each fold is the native Grumpkin Nova step (`comm_W += r·comm_W2`,
//! `comm_E += r·comm_T + r²·comm_E2`, `u,x += r··`) with the challenge derived
//! in-circuit via Poseidon2. The final accumulator `U2` and the endpoints
//! `z0,z2` are the public statement; one Groth16 proof attests the whole 2-step
//! run. This is the folding-recursion loop; the production form replaces the
//! per-step *fresh instances* with the augmented step circuit's own folded
//! instance (true self-referential Nova) — the verifier core is identical.

#![cfg_attr(xark, no_std)]
#![allow(clippy::assign_op_pattern)]

use xark_grumpkin::prelude::*;

/// Little-endian bits of the BN254 scalar-field modulus `r` (bit 253 set).
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

/// Canonical 254-bit decomposition: boolean, recompose-pinned, and enforced
/// `< r` (branch-free) — a Poseidon output can be 254 bits.
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
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 254usize {
        acc = acc + bits[i] * pow;
        pow = pow + pow;
        i += 1;
    }
    require_eq(acc, h);
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
        let agree = one - (vi + ri - two * vi * ri);
        undecided = undecided * agree;
        i += 1;
    }
    require_eq(lt, one);
    bits
}

/// `r = low128(Poseidon2(transcript))` as 128 little-endian bits.
fn challenge(t: [Field; 15]) -> [Field; 128] {
    let h = xark_poseidon2::hash(t);
    let bits = canonical_bits(h);
    let mut out = [Field::from(0u8); 128];
    let mut i = 0usize;
    while i < 128usize {
        out[i] = bits[i];
        i += 1;
    }
    out
}

/// One Nova folding step, challenge bound to `z_next`. Returns the folded
/// instance flattened as `[cw.x, cw.y, ce.x, ce.y, u, x]`.
#[allow(clippy::too_many_arguments)]
fn fold_step(
    a_cw: [Field; 2],
    a_ce: [Field; 2],
    a_u: Field,
    a_x: Field,
    b_cw: [Field; 2],
    b_ce: [Field; 2],
    b_u: Field,
    b_x: Field,
    t: [Field; 2],
    z_next: Field,
) -> [Field; 6] {
    let r_bits = challenge([
        a_cw[0], a_cw[1], a_ce[0], a_ce[1], a_u, a_x, b_cw[0], b_cw[1], b_ce[0], b_ce[1], b_u, b_x,
        t[0], t[1], z_next,
    ]);
    let r_fr = Field::from_bits::<128>(r_bits);
    let cw = ec_add(a_cw, scalar_mul(r_bits, b_cw));
    let r_t = scalar_mul(r_bits, t);
    let r2_e2 = scalar_mul(r_bits, scalar_mul(r_bits, b_ce));
    let ce = ec_add(ec_add(a_ce, r_t), r2_e2);
    let u = a_u + r_fr * b_u;
    let x = a_x + r_fr * b_x;
    [cw[0], cw[1], ce[0], ce[1], u, x]
}

/// Verify a 2-step folding IVC: the computation `z0 →F z1 →F z2` and the
/// accumulator `U0 →fold U1 →fold U2`, tied together through the FS transcript.
#[circuit]
#[allow(clippy::too_many_arguments)]
pub fn grumpkin_ivc(
    u0_cw: Public<Affine>,
    u0_ce: Public<Affine>,
    u0_u: Public<Field>,
    u0_x: Public<Field>,
    s0_cw: Public<Affine>,
    s0_ce: Public<Affine>,
    s0_u: Public<Field>,
    s0_x: Public<Field>,
    t0: Public<Affine>,
    s1_cw: Public<Affine>,
    s1_ce: Public<Affine>,
    s1_u: Public<Field>,
    s1_x: Public<Field>,
    t1: Public<Affine>,
    u2_cw: Public<Affine>,
    u2_ce: Public<Affine>,
    u2_u: Public<Field>,
    u2_x: Public<Field>,
    z0: Public<Field>,
    z2: Public<Field>,
) {
    // computation chain: z1 = F(z0), z2 = F(z1), F(z) = z² + 5
    let five = Field::from(5u8);
    let z1 = z0 * z0 + five;
    let z2c = z1 * z1 + five;
    require_eq(z2c, z2);

    // accumulator chain: U1 = fold(U0, s0, T0; z1), U2 = fold(U1, s1, T1; z2)
    let u1 = fold_step(
        [u0_cw.x, u0_cw.y],
        [u0_ce.x, u0_ce.y],
        u0_u,
        u0_x,
        [s0_cw.x, s0_cw.y],
        [s0_ce.x, s0_ce.y],
        s0_u,
        s0_x,
        [t0.x, t0.y],
        z1,
    );
    let u2 = fold_step(
        [u1[0], u1[1]],
        [u1[2], u1[3]],
        u1[4],
        u1[5],
        [s1_cw.x, s1_cw.y],
        [s1_ce.x, s1_ce.y],
        s1_u,
        s1_x,
        [t1.x, t1.y],
        z2,
    );

    require_eq(u2[0], u2_cw.x);
    require_eq(u2[1], u2_cw.y);
    require_eq(u2[2], u2_ce.x);
    require_eq(u2[3], u2_ce.y);
    require_eq(u2[4], u2_u);
    require_eq(u2[5], u2_x);
}
