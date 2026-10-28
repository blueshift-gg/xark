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
/// One Nova fold, `folded = a ⊕ r·b` with cross-term `t`, the challenge
/// `r = low128(Poseidon2(a, b, t))` (the host reference's transcript order).
#[circuit]
pub fn grumpkin_nova_fold(
    a: Public<Instance>,
    b: Public<Instance>,
    t: Public<Affine>,
    folded: Public<Instance>,
) {
    let (a6, b6) = (a.to_fields(), b.to_fields());
    let mut tr = [Field::from(0u8); 14];
    let mut i = 0usize;
    while i < 6usize {
        tr[i] = a6[i];
        tr[6 + i] = b6[i];
        i += 1;
    }
    tr[12] = t.x;
    tr[13] = t.y;
    let r_bits = challenge(tr);
    let r_fr = Field::from_bits::<128>(r_bits);

    let pt = |p: Affine| [p.x, p.y];
    // comm_W = comm_W1 + r·comm_W2
    let cw = ec_add(pt(a.cw), scalar_mul(r_bits, pt(b.cw)));
    // comm_E = comm_E1 + r·comm_T + r²·comm_E2
    let r_t = scalar_mul(r_bits, pt(t));
    let r2_e2 = scalar_mul(r_bits, scalar_mul(r_bits, pt(b.ce)));
    let ce = ec_add(ec_add(pt(a.ce), r_t), r2_e2);
    // u = u1 + r·u2 ; x = x1 + r·x2  (native Fr)
    let want = Instance {
        cw: Affine { x: cw[0], y: cw[1] },
        ce: Affine { x: ce[0], y: ce[1] },
        u: a.u + r_fr * b.u,
        x: a.x + r_fr * b.x,
    };
    require_eq(want.to_fields(), folded.to_fields());
}
