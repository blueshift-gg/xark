//! **A Nova augmented step circuit `F'` with Poseidon2 IO compression** — the
//! per-step circuit of folding-recursion IVC, on the `Fr` (BN254) side.
//!
//! One step does three things and exposes only two public field elements
//! (`io_in`, `io_out`), the Nova `O(1)` recursion interface:
//! 1. **bind input**: `io_in == Poseidon2(i, z0, z_i, U_i)`;
//! 2. **compute**: `z_{i+1} = F(z_i)` with `F(z) = z² + 5`;
//! 3. **fold**: `U_{i+1} = fold(U_i, s_i, T; r)` (native Grumpkin, in-circuit FS);
//! 4. **bind output**: `io_out == Poseidon2(i+1, z0, z_{i+1}, U_{i+1})`.
//!
//! Chaining this circuit (each step's `io_out` becoming the next step's `io_in`)
//! is a folding IVC. The one thing this circuit does NOT close is the
//! *self-reference*: the fresh instance `s_i` is an input here, whereas in a full
//! Nova prover it is `F'`'s **own** committed instance from the previous step —
//! and, per `docs/folding-recursion.md`, that witness commitment + its fold live
//! on the companion (CycleFold) curve over `Fq`, which Xark (`Fr`-native) can't
//! yet compile. The verifier core here is complete.

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

/// Canonical 254-bit decomposition (`< r`, branch-free) — a Poseidon output can
/// be 254 bits, so `to_bits::<253>` can't hold it.
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

/// Fold challenge `r = low128(Poseidon2(transcript))` (15 elements, bound to `z_next`).
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

/// The IVC IO hash `Poseidon2(i, z0, z, comm_W.x, comm_W.y, comm_E.x, comm_E.y, u, x)`.
#[allow(clippy::too_many_arguments)]
fn io_hash(i: Field, z0: Field, z: Field, cw: [Field; 2], ce: [Field; 2], u: Field, x: Field) -> Field {
    xark_poseidon2::hash([i, z0, z, cw[0], cw[1], ce[0], ce[1], u, x])
}

/// One augmented Nova step. Public interface: `io_in`, `io_out`.
#[circuit]
#[allow(clippy::too_many_arguments)]
pub fn grumpkin_augmented_step(
    io_in: Public<Field>,
    io_out: Public<Field>,
    i: Private<Field>,
    z0: Private<Field>,
    zi: Private<Field>,
    ui_cw: Private<Affine>,
    ui_ce: Private<Affine>,
    ui_u: Private<Field>,
    ui_x: Private<Field>,
    s_cw: Private<Affine>,
    s_ce: Private<Affine>,
    s_u: Private<Field>,
    s_x: Private<Field>,
    t: Private<Affine>,
) {
    // 1. bind the input state to io_in.
    require_eq(
        io_in,
        io_hash(i, z0, zi, [ui_cw.x, ui_cw.y], [ui_ce.x, ui_ce.y], ui_u, ui_x),
    );

    // 2. computation step z_{i+1} = F(z_i).
    let z_next = zi * zi + Field::from(5u8);

    // 3. fold U_i with the fresh instance s into U_{i+1} (challenge bound to z_next).
    let r_bits = challenge([
        ui_cw.x, ui_cw.y, ui_ce.x, ui_ce.y, ui_u, ui_x, s_cw.x, s_cw.y, s_ce.x, s_ce.y, s_u, s_x,
        t.x, t.y, z_next,
    ]);
    let r_fr = Field::from_bits::<128>(r_bits);
    let cw_next = ec_add([ui_cw.x, ui_cw.y], scalar_mul(r_bits, [s_cw.x, s_cw.y]));
    let r_t = scalar_mul(r_bits, [t.x, t.y]);
    let r2_e2 = scalar_mul(r_bits, scalar_mul(r_bits, [s_ce.x, s_ce.y]));
    let ce_next = ec_add(ec_add([ui_ce.x, ui_ce.y], r_t), r2_e2);
    let u_next = ui_u + r_fr * s_u;
    let x_next = ui_x + r_fr * s_x;

    // 4. bind the output state to io_out.
    let i_next = i + Field::from(1u8);
    require_eq(
        io_out,
        io_hash(i_next, z0, z_next, cw_next, ce_next, u_next, x_next),
    );
}
