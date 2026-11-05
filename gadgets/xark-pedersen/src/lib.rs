//! `xark-pedersen`: a native-field Pedersen hash on the Grumpkin curve, in the
//! `xark` `Field` subset.
//!
//! Grumpkin and BN254 form a 2-cycle: Grumpkin's base field is exactly BN254's
//! scalar field `r`, which is `xark`'s native `Field`. So Grumpkin point
//! coordinates are ordinary `Field` values and all EC arithmetic is native
//! `Field` `+ - *` — no non-native limbs. Grumpkin form: `y² = x³ - 17` (`a = 0`),
//! prime order `q` (BN254's base field modulus).
//!
//! Pedersen hash of `K = 2` scalars `mᵢ ∈ [1, 2^128)` against fixed generators `Gᵢ`:
//!
//! ```text
//!   H = m₀·G₀ + m₁·G₁
//! ```
//!
//! ## Fixed-base windows
//!
//! Each `mᵢ·Gᵢ` is a fixed-base multiplication with no doublings: `mᵢ`'s 128 bits
//! are split into 3-bit windows `k_w` (the last one has 2 bits), and window `w`
//! adds the constant `(k_w + 2)·8^w·Gᵢ` read from a table (`tables.rs`). The `+2`
//! offsets make the partial sum after window `w` the multiple
//! `Σ_{j≤w} (k_j + 2)·8^j` of `Gᵢ`, which is nonzero and smaller than the next
//! window's entry, so no two points an add meets are equal or opposite and the
//! cheap incomplete add is exact. A final add of the constant
//! `CORR = −(Σ_w 2·8^w)·Gᵢ` removes the offsets; its only exceptional input is
//! `mᵢ = 0`, which its slope row rejects. Per 3 bits: 3 booleanity rows, 3 lookup
//! rows (bellman `lookup3_xy`) and 3 add rows, against ≈36 for double-and-add.
//!
//! References: halo2 fixed-base scalar multiplication and its offsets
//! (zcash/halo2 book `fixed-base-scalar-mul.md` @ 3442dd3), proven for Pallas in
//! zksecurity/clean-orchard `Orchard/Ecc/MulFixed.lean` L199-298 and
//! `MulFixed/FullWidth.lean` L245 @ b5b93ee; zcash/sapling-crypto
//! `fixed_base_multiplication` (`src/circuit/ecc.rs` L28-75 @ c5e596c, the commit
//! Zellic audited) with bellman `lookup3_xy` (`src/gadgets/lookup.rs` L29-118 @
//! b726862; bellpepper @ 7275595).
//!
//! ## Soundness / completeness
//!
//! `formal/Formal/PedersenHash.lean` proves, over the R1CS one call emits
//! (`cargo xtask lean-export pedersen_hash`), that every satisfying assignment has
//! `mᵢ ∈ [1, 2^128)` and outputs the affine coordinates of `m₀·G₀ + m₁·G₁`. The last
//! add is incomplete: it pins `x₁ ≠ x₂` with an inverse, so `m₀·G₀ = ±m₁·G₁` is
//! rejected, never forged (soundness, not completeness: no Lean theorem says the
//! hints satisfy the rows). Its table entries are checked in Lean as multiples of
//! `Gᵢ`, and `Gᵢ`'s order as `q`.
//!
//! ## Generators (nothing-up-my-sleeve)
//!
//! `Gᵢ = try-and-increment from x = SHA256("xark-pedersen:generator:i")` on
//! Grumpkin, taking the smaller `y`. This fixed, domain-separated derivation gives
//! generators with no known discrete-log relation (the Pedersen security
//! requirement). Their coordinates are in `examples/grumpkin_reference`
//! (`pedersen_tables`), which derives the window tables from them with
//! `ark-grumpkin`.

#![no_std]

mod tables;

use tables::{CORR, TABLES};
use xark::{Field, gadget, require_eq, witness_begin, witness_end};

/// Scalar bit-length: `2^128 < r`, so the decomposition is unique.
const N_BITS: usize = 128;

/// 3-bit windows per scalar; the last holds bits 126 and 127.
const WINDOWS: usize = 43;

// Every decomposed bit is read by a window, and the recomposition stays below `r`.
const _: () = assert!(N_BITS == 3 * (WINDOWS - 1) + 2 && N_BITS <= 253);

/// Incomplete affine addition `p + q` in 3 rows: `λ·(x₂ − x₁) = y₂ − y₁`,
/// `λ² = x₃ + x₁ + x₂`, `λ·(x₁ − x₃) = y₃ + y₁`. Exact when `x₁ ≠ x₂`; at
/// `x₁ = x₂` the first row rejects `p = −q` and leaves `λ` free for `p = q`, which
/// the callers exclude (window offsets, or an inverse of `x₂ − x₁`).
fn add(p: [Field; 2], q: [Field; 2]) -> [Field; 2] {
    let dx = q[0] - p[0];
    let dy = q[1] - p[1];
    // The textbook values as witness-only scratch. `λ`, `x₃`, `y₃` are then fresh
    // variables with no row of their own (the three rows below pin them): each is
    // the inverse of its scratch inverse, since `(v⁻¹)⁻¹ = v`, also at `0`, where the
    // inverse-or-zero hint gives `0`. xark has no plain "copy" hint.
    witness_begin();
    let l = dy * Field::hint_inverse_or_zero(dx);
    let x = l * l - p[0] - q[0];
    let y = l * (p[0] - x) - p[1];
    let inv = [l, x, y].map(Field::hint_inverse_or_zero);
    witness_end();
    let [lam, x3, y3] = inv.map(Field::hint_inverse_or_zero);
    require_eq(lam * dx, dy);
    require_eq(lam * lam, x3 + p[0] + q[0]);
    require_eq(lam * (p[0] - x3), y3 + p[1]);
    [x3, y3]
}

/// bellman `lookup3_xy`: `t[b₀ + 2b₁ + 4b₂]` for bits `b`, in 3 rows (`b₁·b₂` and
/// one `b₀·(…)` per coordinate), by multilinear interpolation of the constants.
fn lookup3(b: [Field; 3], t: [[Field; 2]; 8]) -> [Field; 2] {
    let b12 = b[1] * b[2];
    let mut out = [Field::zero(); 2];
    let mut c = 0;
    while c < 2 {
        let v = [
            t[0][c], t[1][c], t[2][c], t[3][c], t[4][c], t[5][c], t[6][c], t[7][c],
        ];
        let low =
            v[0] + (v[2] - v[0]) * b[1] + (v[4] - v[0]) * b[2] + (v[6] - v[4] - v[2] + v[0]) * b12;
        let high = (v[1] - v[0])
            + (v[3] - v[2] - v[1] + v[0]) * b[1]
            + (v[5] - v[4] - v[1] + v[0]) * b[2]
            + (v[7] - v[6] - v[5] + v[4] - v[3] + v[2] + v[1] - v[0]) * b12;
        out[c] = low + b[0] * high;
        c += 1;
    }
    out
}

/// `t[b₀ + 2b₁]` for bits `b`, in 1 row (`b₀·b₁`).
fn lookup2(b: [Field; 2], t: [[Field; 2]; 8]) -> [Field; 2] {
    let b01 = b[0] * b[1];
    let mut out = [Field::zero(); 2];
    let mut c = 0;
    while c < 2 {
        let v = [t[0][c], t[1][c], t[2][c], t[3][c]];
        out[c] =
            v[0] + (v[1] - v[0]) * b[0] + (v[2] - v[0]) * b[1] + (v[3] - v[2] - v[1] + v[0]) * b01;
        c += 1;
    }
    out
}

/// `x`'s 128 little-endian bits: booleanity rows and the recomposition
/// `Σ bᵢ·2ⁱ = x`, which also proves `x < 2^128`.
fn decompose(x: Field) -> [Field; N_BITS] {
    let mut bits = [Field::zero(); N_BITS];
    let mut i = 0;
    while i < N_BITS {
        bits[i] = Field::hint_bit(x, i);
        i += 1;
    }
    let mut i = 0;
    while i < N_BITS {
        bits[i].require_bool();
        i += 1;
    }
    let mut acc = Field::zero();
    let mut pow = Field::one();
    let mut i = 0;
    while i < N_BITS {
        acc += bits[i] * pow;
        pow = pow + pow;
        i += 1;
    }
    require_eq(acc, x);
    bits
}

/// `m·Gᵢ` for the scalar `m` with bits `bits`, `m ≠ 0`: the windows' table
/// entries summed, then the offsets removed.
fn mul_fixed(bits: [Field; N_BITS], i: usize) -> [Field; 2] {
    let t = &TABLES[i];
    let mut acc = lookup3([bits[0], bits[1], bits[2]], t[0]);
    let mut w = 1;
    while w < WINDOWS - 1 {
        let b = [bits[3 * w], bits[3 * w + 1], bits[3 * w + 2]];
        acc = add(acc, lookup3(b, t[w]));
        w += 1;
    }
    let last = WINDOWS - 1;
    acc = add(acc, lookup2([bits[3 * last], bits[3 * last + 1]], t[last]));
    add(acc, CORR[i])
}

/// Pedersen hash `H = m₀·G₀ + m₁·G₁` of two scalars `mᵢ ∈ [1, 2^128)`, as the
/// affine point `[x, y]`. Other inputs, and inputs with `m₀·G₀ = ±m₁·G₁`, leave the
/// circuit unsatisfiable.
#[gadget]
pub fn pedersen_hash(inputs: [Field; 2]) -> [Field; 2] {
    let p0 = mul_fixed(decompose(inputs[0]), 0);
    let p1 = mul_fixed(decompose(inputs[1]), 1);
    // The terms' discrete logs are unknown, so `x₁ ≠ x₂` is pinned here.
    require_eq(
        (p1[0] - p0[0]) * Field::hint_inverse(p1[0] - p0[0]),
        Field::one(),
    );
    add(p0, p1)
}

/// Bring the gadget's public API into scope alongside the xark circuit
/// essentials (`Field`, `Public`/`Private`, `require_eq`, `#[circuit]`), so a
/// circuit crate needs a single `use xark_pedersen::prelude::*;`.
pub mod prelude {
    pub use crate::*;
    pub use xark::prelude::*;
}
