//! **The Nova/CycleFold folding *step* verified inside a BN254 Groth16 circuit —
//! natively over Grumpkin.** The atomic operation of folding-based recursion
//! (IVC): fold two committed relaxed-R1CS instances `(comm_W, comm_E, u, x)`
//! with a Poseidon2 Fiat–Shamir challenge `r`:
//!
//! ```text
//!   comm_W = comm_W1 + r·comm_W2
//!   comm_E = comm_E1 + r·comm_T + r²·comm_E2
//!   u      = u1 + r·u2
//!   x      = x1 + r·x2
//! ```
//!
//! Commitments are Grumpkin points (native coords), so the point folds are
//! native `ec_add`/`scalar_mul`. The fold uses only **positive** powers of `r`
//! (no inverse), so it is **fully self-contained** — no bound-witness scalars at
//! all. `r` is derived in-circuit as `low128(Poseidon2(transcript))` (KAT-matched
//! to the host `poseidon2`), and used both as a Grumpkin scalar (point folds) and
//! an `Fr` element (`u`,`x` folds) — the same 128-bit integer, canonical in both.
//!
//! This is the in-circuit verifier a folding-recursion step runs each iteration;
//! the remaining IVC scaffolding (augmented step circuit, IO hashing, driver) is
//! systems assembly around this verified core.

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

/// Canonical 254-bit decomposition of a full field element: boolean,
/// recompose-pinned, and enforced `< r` (branch-free bit-serial). Needed because
/// a Poseidon output can be 254 bits (so `to_bits::<253>` can't hold it).
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
fn challenge(t: [Field; 14]) -> [Field; 128] {
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

/// Verify one Nova folding step: given two committed relaxed-R1CS instances, the
/// cross-term commitment `comm_T`, and the claimed folded instance, check the
/// fold is correct with the in-circuit Fiat–Shamir challenge `r`.
#[circuit]
#[allow(clippy::too_many_arguments)]
pub fn grumpkin_nova_fold(
    cw1: Public<Affine>,
    ce1: Public<Affine>,
    cw2: Public<Affine>,
    ce2: Public<Affine>,
    ct: Public<Affine>,
    u1: Public<Field>,
    x1: Public<Field>,
    u2: Public<Field>,
    x2: Public<Field>,
    cw: Public<Affine>,
    ce: Public<Affine>,
    u: Public<Field>,
    x: Public<Field>,
) {
    // r = low128(Poseidon2(transcript)) — same order as the host reference.
    let r_bits = challenge([
        cw1.x, cw1.y, ce1.x, ce1.y, u1, x1, cw2.x, cw2.y, ce2.x, ce2.y, u2, x2, ct.x, ct.y,
    ]);
    let r_fr = Field::from_bits::<128>(r_bits);

    // comm_W = comm_W1 + r·comm_W2
    let cw_c = ec_add([cw1.x, cw1.y], scalar_mul(r_bits, [cw2.x, cw2.y]));
    // comm_E = comm_E1 + r·comm_T + r²·comm_E2
    let r_t = scalar_mul(r_bits, [ct.x, ct.y]);
    let r2_e2 = scalar_mul(r_bits, scalar_mul(r_bits, [ce2.x, ce2.y]));
    let ce_c = ec_add(ec_add([ce1.x, ce1.y], r_t), r2_e2);
    // u = u1 + r·u2 ; x = x1 + r·x2  (native Fr)
    let u_c = u1 + r_fr * u2;
    let x_c = x1 + r_fr * x2;

    require_eq(cw_c[0], cw.x);
    require_eq(cw_c[1], cw.y);
    require_eq(ce_c[0], ce.x);
    require_eq(ce_c[1], ce.y);
    require_eq(u_c, u);
    require_eq(x_c, x);
}
