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

/// One Nova folding step `a ⊕ r·b` with cross-term `t`, the challenge
/// `r = low128(Poseidon2(a, b, t, z_next))` bound to `z_next`.
fn fold_step(a: Instance, b: Instance, t: Affine, z_next: Field) -> Instance {
    let (a6, b6) = (a.to_fields(), b.to_fields());
    let mut tr = [Field::from(0u8); 15];
    let mut i = 0usize;
    while i < 6usize {
        tr[i] = a6[i];
        tr[6 + i] = b6[i];
        i += 1;
    }
    tr[12] = t.x;
    tr[13] = t.y;
    tr[14] = z_next;
    let r_bits = challenge(tr);
    let r_fr = Field::from_bits::<128>(r_bits);
    let pt = |p: Affine| [p.x, p.y];
    let cw = ec_add(pt(a.cw), scalar_mul(r_bits, pt(b.cw)));
    let r_t = scalar_mul(r_bits, pt(t));
    let r2_e2 = scalar_mul(r_bits, scalar_mul(r_bits, pt(b.ce)));
    let ce = ec_add(ec_add(pt(a.ce), r_t), r2_e2);
    Instance {
        cw: Affine { x: cw[0], y: cw[1] },
        ce: Affine { x: ce[0], y: ce[1] },
        u: a.u + r_fr * b.u,
        x: a.x + r_fr * b.x,
    }
}

/// Verify a 2-step folding IVC: the computation `z0 →F z1 →F z2` and the
/// accumulator `U0 →fold U1 →fold U2` (folding the fresh instances `s0`, `s1` with
/// cross-terms `t0`, `t1`), tied together through the FS transcript.
#[circuit]
#[allow(clippy::too_many_arguments)]
pub fn grumpkin_ivc(
    u0: Public<Instance>,
    s0: Public<Instance>,
    t0: Public<Affine>,
    s1: Public<Instance>,
    t1: Public<Affine>,
    u2: Public<Instance>,
    z0: Public<Field>,
    z2: Public<Field>,
) {
    // computation chain: z1 = F(z0), z2 = F(z1), F(z) = z² + 5
    let five = Field::from(5u8);
    let z1 = z0 * z0 + five;
    let z2c = z1 * z1 + five;
    require_eq(z2c, z2);

    // accumulator chain: U1 = fold(U0, s0, T0; z1), U2 = fold(U1, s1, T1; z2)
    let u1 = fold_step(u0, s0, t0, z1);
    let folded = fold_step(u1, s1, t1, z2);
    require_eq(folded.to_fields(), u2.to_fields());
}
