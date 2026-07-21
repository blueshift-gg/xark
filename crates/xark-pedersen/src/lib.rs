//! `xark-pedersen`: a **native-field Pedersen hash** on the Grumpkin curve,
//! written entirely in the `xark` `Field` subset.
//!
//! ## Why Grumpkin is native (the key insight)
//!
//! Grumpkin and BN254 form a 2-cycle: Grumpkin's **base field** is exactly
//! BN254's **scalar field**
//! `r = 21888242871839275222246405745257275088548364400416034343698204186575808495617`,
//! which is precisely `xark`'s native `Field`. So a Grumpkin point's
//! coordinates are ordinary `Field` values and **all elliptic-curve arithmetic
//! is native `Field` `+ - *`** — no non-native limbs, no `mod_mul`, no
//! `xark-bignum`. This makes the whole gadget dramatically simpler (and cheaper)
//! than the secp256k1 gadget, which lives over a foreign 256-bit field.
//!
//! Grumpkin short-Weierstrass form: `y² = x³ - 17`  (`a = 0`, `b = -17`).
//!
//! ## Construction
//!
//! Pedersen hash of `K` scalars `mᵢ` against `K` fixed generators `Gᵢ`:
//!
//! ```text
//!   H = Σ_i  mᵢ · Gᵢ
//! ```
//!
//! Each `mᵢ · Gᵢ` is a fixed-base scalar multiplication. We use an **offset
//! (double-and-add) accumulator** so that every intermediate point stays off the
//! point at infinity (which incomplete affine addition cannot represent):
//!
//! ```text
//!   acc = O                              // O: fixed non-identity offset point
//!   for i in 0..N  (MSB first):
//!       acc = 2·acc
//!       acc = bit_i ? acc + G : acc      // arithmetic point-mux, never a branch
//!   result = acc - 2^N·O                 // remove the accumulated offset
//! ```
//!
//! After the loop `acc = 2^N·O + m·G`, so subtracting the compile-time constant
//! `2^N·O` yields `m·G`. Because `O` and `G` are **constants**, `2^N·O` (and its
//! negation, the correction point [`corr`]) are compile-time constants too.
//!
//! ## Soundness / completeness
//!
//! Every division uses `Field::hint_inverse`, PINNED by `denom · inv == 1`. At an
//! exceptional case (`acc.x == G.x`, `acc.y == 0`, or `x1 == x2` in a subtract)
//! the denominator is `0`, so `0 · inv == 1` is **unsatisfiable** — a malicious
//! prover can never forge a result at an edge (soundness holds). An honest prover
//! only fails on the negligible fraction of inputs that land exactly on an edge
//! (the standard incomplete-addition completeness gap). Concretely this gadget
//! requires each scalar `mᵢ` to be **nonzero** (`0·G` is the identity, which the
//! affine representation cannot express).
//!
//! ## Scalar range / bit-length
//!
//! `N_BITS = 128`: each message scalar is decomposed into 128 pinned little-
//! endian bits, so this gadget hashes 128-bit messages. Because
//! `2^128 < r`, the bit decomposition is *injective* — the bits are uniquely
//! determined by the scalar (analyzer-clean, no non-canonical-decomposition
//! malleability). Raising `N_BITS` toward 252 (full-field messages) is a
//! one-line change plus regenerating the single `corr` constant (`corr` depends
//! on `N_BITS`); the generators are unchanged. It costs ~`12·N_BITS` gates per
//! scalar.
//!
//! ## Generators (nothing-up-my-sleeve)
//!
//! The generators `Gᵢ` are derived by hash-to-curve — `Gᵢ = try-and-increment from
//! x = SHA256("xark-pedersen:generator:i")` on Grumpkin (`y² = x³ - 17`), taking
//! the smaller `y`. This fixed, reproducible, domain-separated derivation gives
//! generators with no known discrete-log relation, which is the security
//! requirement a Pedersen hash needs. `examples/pedersen` reproduces the exact
//! derivation with `ark-grumpkin` and checks the circuit output equals
//! `m0·G0 + m1·G1` (see also `tests/vec.rs`).
//!
//! The offset seed `O` is an internal device (it makes the incomplete-addition
//! accumulator non-degenerate and is corrected out of the result), so it does not
//! affect the hash value or its security and can be any fixed non-identity point.

#![no_std]
// Circuit-lowered gadget code: the xark compiler rejects compound assignment on
// `Field` (`+=`/`-=`/`*=`), so `x = x + y` is required — not a clippy oversight.
#![allow(clippy::assign_op_pattern)]

use xark::{require_eq, Field};

/// Scalar bit-length (see module docs). Kept in sync with the `128usize` loop
/// literals below (loop bounds must be integer literals in the subset).
const N_BITS: usize = 128;

/// Number of message scalars hashed (number of generators).
const K: usize = 2;

// ===========================================================================
// Curve constants (nothing-up-my-sleeve Grumpkin generators; see module docs).
// ===========================================================================

/// Generators `G[0..K]`, one per message scalar. **Nothing-up-my-sleeve**: each
/// `Gᵢ = hash_to_curve("xark-pedersen:generator:i")` — try-and-increment from
/// `x = SHA256(domain)` on Grumpkin, taking the smaller `y`. This fixed,
/// reproducible derivation gives generators with no known discrete-log relation
/// (the security requirement a Pedersen hash needs); `examples/pedersen`
/// reproduces it with `ark-grumpkin` and checks the output matches `M0·G0 + M1·G1`.
fn generators() -> [[Field; 2]; K] {
    [
        // G0 = hash_to_curve("xark-pedersen:generator:0")
        [
            Field::from(
                "5083206013960444200279950714875343028998509784402499812888938851520740463864",
            ),
            Field::from(
                "2865765882798453005924934609198434488689574281003992091311004806791329233019",
            ),
        ],
        // G1 = hash_to_curve("xark-pedersen:generator:1")
        [
            Field::from(
                "6702321717701145156728393535503061021609887341049508944231879352606054294317",
            ),
            Field::from(
                "6805153572597533704290353269906054575543118937636820472181004119224603304535",
            ),
        ],
    ]
}

/// Offset-accumulator seed `O` (fixed non-identity point, `x = 5`).
fn offset() -> [Field; 2] {
    [
        Field::from(5u8),
        Field::from("26447525821777463057023244913909144251512587297343525263882"),
    ]
}

/// Offset correction `corr = -(2^N_BITS · O)`, subtracted at the end of each
/// scalar-mul to remove the accumulated offset. Compile-time constant because
/// `O` and `N_BITS` are.
fn corr() -> [Field; 2] {
    [
        Field::from(
            "15091588220200540439587434062098309947749547413125795808386331904279218024383",
        ),
        Field::from("9700730252355689723080387012214398702149611734773390356605491655538683087420"),
    ]
}

// ===========================================================================
// Native Grumpkin affine EC ops (a = 0). Incomplete: assume non-identity,
// non-colliding inputs (guaranteed by the offset accumulator + nonzero scalars).
// ===========================================================================

/// Incomplete affine point addition `P + Q` (`P ≠ ±Q`, neither `∞`).
/// `λ = (y2 - y1)/(x2 - x1)`, `x3 = λ² - x1 - x2`, `y3 = λ(x1 - x3) - y1`.
pub fn ec_add(p: [Field; 2], q: [Field; 2]) -> [Field; 2] {
    let one = Field::from(1u8);
    let dx = q[0] - p[0];
    let inv = Field::hint_inverse(dx); // witness-gen: inv = 1/dx
    require_eq(dx * inv, one); // pins dx ≠ 0 (edge ⇒ unsatisfiable)
    let lam = (q[1] - p[1]) * inv;
    let x3 = lam * lam - p[0] - q[0];
    let y3 = lam * (p[0] - x3) - p[1];
    [x3, y3]
}

/// Incomplete affine point doubling `2·P` (`P ≠ ∞`, `y ≠ 0`, `a = 0`).
/// `λ = 3x²/(2y)`, `x3 = λ² - 2x`, `y3 = λ(x - x3) - y`.
pub fn ec_double(p: [Field; 2]) -> [Field; 2] {
    let one = Field::from(1u8);
    let two = Field::from(2u8);
    let three = Field::from(3u8);
    let x = p[0];
    let y = p[1];
    let two_y = two * y;
    let inv = Field::hint_inverse(two_y); // witness-gen: inv = 1/(2y)
    require_eq(two_y * inv, one); // pins 2y ≠ 0 (edge ⇒ unsatisfiable)
    let lam = three * x * x * inv;
    let x3 = lam * lam - two * x;
    let y3 = lam * (x - x3) - y;
    [x3, y3]
}

/// Boolean-gated select between two affine points: `bit ? if_true : if_false`.
/// Pure arithmetic mux `sel·(a - b) + b` — never a data-dependent branch.
fn point_select(bit: Field, if_true: [Field; 2], if_false: [Field; 2]) -> [Field; 2] {
    bit.require_bool();
    [
        if_false[0] + bit * (if_true[0] - if_false[0]),
        if_false[1] + bit * (if_true[1] - if_false[1]),
    ]
}

// ===========================================================================
// Scalar decomposition + fixed-base scalar multiplication.
// ===========================================================================

/// Decompose `x` into `N_BITS` little-endian bits, boolean-constrained and
/// pinned to `x` by recomposition (`Σ bits[i]·2^i == x`). Because
/// `2^N_BITS < r`, this uniquely determines the bits (injective), so a cheating
/// prover cannot supply a non-canonical decomposition.
fn decompose(x: Field) -> [Field; N_BITS] {
    let mut bits = [Field::from(0u8); N_BITS];
    let mut i = 0usize;
    while i < 128usize {
        bits[i] = Field::hint_bit(x, i); // witness-gen: bits[i] = bit(x, i)
        i += 1;
    }
    let mut i = 0usize;
    while i < 128usize {
        bits[i].require_bool();
        i += 1;
    }
    let mut acc = Field::from(0u8);
    let mut pow = Field::from(1u8);
    let mut i = 0usize;
    while i < 128usize {
        acc = acc + bits[i] * pow;
        pow = pow + pow; // double: stays a compile-time constant (no gate)
        i += 1;
    }
    require_eq(acc, x);
    bits
}

/// Fixed-base scalar multiplication `m · gen` via the offset (double-and-add)
/// accumulator. `bits` is the little-endian decomposition of `m`; processed
/// MSB-first. Returns the affine point `m · gen`. Requires `m ≠ 0`.
pub fn scalar_mul(bits: [Field; N_BITS], gen: [Field; 2]) -> [Field; 2] {
    let mut acc = offset();
    let mut i = 0usize;
    while i < 128usize {
        acc = ec_double(acc);
        let bit = bits[127 - i]; // MSB first
        let cand = ec_add(acc, gen);
        acc = point_select(bit, cand, acc);
        i += 1;
    }
    // acc = 2^N·O + m·gen ; remove the offset by adding corr = -(2^N·O).
    ec_add(acc, corr())
}

/// Pedersen hash `H = Σ_i mᵢ · Gᵢ` over `K` message scalars against the fixed
/// generator set. Returns the resulting Grumpkin point `[x, y]`. Each `mᵢ` must
/// be a nonzero `< 2^N_BITS` scalar.
pub fn pedersen_hash(inputs: [Field; K]) -> [Field; 2] {
    let gens = generators();
    let mut acc = scalar_mul(decompose(inputs[0]), gens[0]);
    let mut i = 1usize;
    while i < 2usize {
        let term = scalar_mul(decompose(inputs[i]), gens[i]);
        acc = ec_add(acc, term);
        i += 1;
    }
    acc
}
/// Bring the gadget's public API into scope alongside the xark circuit
/// essentials (`Field`, `Public`/`Private`, `require_eq`, `#[circuit]`), so a
/// circuit crate needs a single `use xark_pedersen::prelude::*;`.
pub mod prelude {
    pub use crate::*;
    pub use xark::prelude::*;
}
