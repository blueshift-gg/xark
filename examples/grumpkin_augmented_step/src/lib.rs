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

/// The IVC IO hash `Poseidon2(i, z0, z, U)`, the instance `U` as
/// `comm_W.x, comm_W.y, comm_E.x, comm_E.y, u, x`.
fn io_hash(i: Field, z0: Field, z: Field, u: Instance) -> Field {
    let f = u.to_fields();
    xark_poseidon2::hash([i, z0, z, f[0], f[1], f[2], f[3], f[4], f[5]])
}

/// One augmented Nova step. Public interface: `io_in`, `io_out`; the running
/// instance `ui`, the fresh instance `s` and the cross-term `t` are witnesses.
#[circuit]
pub fn grumpkin_augmented_step(
    io_in: Public<Field>,
    io_out: Public<Field>,
    i: Private<Field>,
    z0: Private<Field>,
    zi: Private<Field>,
    ui: Private<Instance>,
    s: Private<Instance>,
    t: Private<Affine>,
) {
    // 1. bind the input state to io_in.
    require_eq(io_in, io_hash(i, z0, zi, ui));

    // 2. computation step z_{i+1} = F(z_i).
    let z_next = zi * zi + Field::from(5u8);

    // 3. fold U_i with the fresh instance s into U_{i+1} (challenge bound to z_next).
    let (u6, s6) = (ui.to_fields(), s.to_fields());
    let mut tr = [Field::from(0u8); 15];
    let mut k = 0usize;
    while k < 6usize {
        tr[k] = u6[k];
        tr[6 + k] = s6[k];
        k += 1;
    }
    tr[12] = t.x;
    tr[13] = t.y;
    tr[14] = z_next;
    let r_bits = challenge(tr);
    let r_fr = Field::from_bits::<128>(r_bits);
    let pt = |p: Affine| [p.x, p.y];
    let cw = ec_add(pt(ui.cw), scalar_mul(r_bits, pt(s.cw)));
    let r_t = scalar_mul(r_bits, pt(t));
    let r2_e2 = scalar_mul(r_bits, scalar_mul(r_bits, pt(s.ce)));
    let ce = ec_add(ec_add(pt(ui.ce), r_t), r2_e2);
    let next = Instance {
        cw: Affine { x: cw[0], y: cw[1] },
        ce: Affine { x: ce[0], y: ce[1] },
        u: ui.u + r_fr * s.u,
        x: ui.x + r_fr * s.x,
    };

    // 4. bind the output state to io_out.
    require_eq(io_out, io_hash(i + Field::from(1u8), z0, z_next, next));
}
