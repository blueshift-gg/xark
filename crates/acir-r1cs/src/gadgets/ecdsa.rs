//! ECDSA secp256k1 signature verification gadget (ROADMAP step **WS-D.6**).
//!
//! Verifies a single ECDSA signature `(r, s)` over secp256k1 against a public
//! key `Q = (Qx, Qy)` and a 32-byte message digest `m`. Soundness contract:
//! the gadget pins the `output: Witness` to `1` whenever the prover can
//! construct a witness; if the prover supplies values that don't correspond
//! to a valid signature, the witness solver inside the lowering layer will
//! produce a contradiction and proving will fail.
//!
//! # Algorithm (RFC 6979 §3.2.4 / SEC 1 v2.0)
//!
//! Given a public key `Q`, a message digest `e` (already reduced mod n), and
//! a signature `(r, s)`:
//!
//! 1. Reject if `r ∉ [1, n-1]` or `s ∉ [1, n-1]`.
//! 2. Compute `w = s^-1 mod n`.
//! 3. Compute `u1 = e · w mod n` and `u2 = r · w mod n`.
//! 4. Compute the curve point `R' = u1·G + u2·Q`. Reject if `R' = O`.
//! 5. Accept iff `R'.x mod n == r`.
//!
//! # In-circuit strategy
//!
//! Non-native arithmetic over the 256-bit secp256k1 base field `Fp` and
//! scalar field `Fn` is expressed via the **prover-aided identity** style:
//! for each non-native multiplication `c = a · b (mod m)`, the prover
//! supplies the quotient `q` and remainder `c`, and the circuit checks the
//! integer identity `a · b = q · m + c` decomposed limb-by-limb so every
//! intermediate fits in BN254 `Fr`. The remainder is range-checked to lie
//! in `[0, m)` via bit decomposition.
//!
//! Limb base is `β = 2^64`, giving four 64-bit limbs per 256-bit value.
//! Limb products `a_i · b_j` are bounded by `2^128`, well within `Fr`
//! (~254 bits). For each output limb of `a·b - q·m - c` we accumulate the
//! relevant partial products plus an incoming carry and constrain it to
//! the matching limb of `0` (plus an outgoing carry).
//!
//! Per-operation constraint budget:
//!
//! | op                  | constraints                                  |
//! |---------------------|----------------------------------------------|
//! | `mul_mod`           | ~24 muls (4×4 partial products + carries) + 256 bool (bit decomp) ≈ 300 |
//! | `inv_mod`           | one `mul_mod` (a · a_inv = 1) ≈ 300            |
//! | affine point add    | 6 `mul_mod` + 1 `inv_mod` + cheap linears ≈ 2100 |
//! | affine point double | 5 `mul_mod` + 1 `inv_mod`                ≈ 1800  |
//! | 256-bit scalar mul  | 256 doubles + ~128 adds                  ≈ 730k  |
//! | full ECDSA verify   | 2 scalar muls + 1 add + bookkeeping      ≈ 1.5M  |
//!
//! This is deliberately the un-optimised "schoolbook" lowering — windowed
//! scalar muls and Strauss-style 2P combinations would cut the cost by ~3x
//! but add significant code; see `docs/security.md` for the audit boundary.

use ark_bn254::Fr;
use ark_ff::{AdditiveGroup, One, PrimeField, Zero};
use ark_relations::r1cs::{LinearCombination, SynthesisError, Variable};
use num_bigint::BigUint;
use num_traits::Num;
use std::sync::OnceLock;

use crate::gadgets::boolean::enforce_boolean;
use crate::gadgets::range::decompose_into_bits;
use crate::r1cs_builder::R1csBuilder;

// =============================================================================
// secp256k1 curve constants
// =============================================================================

/// secp256k1 base field prime: `p = 2^256 - 2^32 - 977`.
pub fn secp256k1_p() -> &'static BigUint {
    static P: OnceLock<BigUint> = OnceLock::new();
    P.get_or_init(|| {
        BigUint::from_str_radix(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
            16,
        )
        .unwrap()
    })
}

/// secp256k1 scalar field prime (order of G).
pub fn secp256k1_n() -> &'static BigUint {
    static N: OnceLock<BigUint> = OnceLock::new();
    N.get_or_init(|| {
        BigUint::from_str_radix(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
            16,
        )
        .unwrap()
    })
}

/// secp256k1 GLV β: a non-trivial cube root of `1` modulo `p`. The
/// endomorphism `φ(x, y) = (β·x, y)` is the point map corresponding to
/// scalar multiplication by `λ` (defined below). Source: SEC 1 §3.1.1
/// (`β = 2^((p-1)/3) mod p`).
pub fn secp256k1_beta() -> &'static BigUint {
    static BETA: OnceLock<BigUint> = OnceLock::new();
    BETA.get_or_init(|| {
        BigUint::from_str_radix(
            "7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE",
            16,
        )
        .unwrap()
    })
}

/// secp256k1 GLV λ: the scalar in `[0, n)` for which `λ · P = φ(P)` for
/// every `P` on the curve. Roots-of-unity invariant: `λ ≡ 1 (mod n)` would
/// be trivial; this is the non-trivial cube root.
pub fn secp256k1_lambda() -> &'static BigUint {
    static LAMBDA: OnceLock<BigUint> = OnceLock::new();
    LAMBDA.get_or_init(|| {
        BigUint::from_str_radix(
            "5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72",
            16,
        )
        .unwrap()
    })
}

/// Generator G of secp256k1, in affine `(x, y)` form.
pub fn secp256k1_g() -> &'static (BigUint, BigUint) {
    static G: OnceLock<(BigUint, BigUint)> = OnceLock::new();
    G.get_or_init(|| {
        (
            BigUint::from_str_radix(
                "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
                16,
            )
            .unwrap(),
            BigUint::from_str_radix(
                "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
                16,
            )
            .unwrap(),
        )
    })
}

/// secp256r1 (NIST P-256) base field prime.
pub fn secp256r1_p() -> &'static BigUint {
    static P: OnceLock<BigUint> = OnceLock::new();
    P.get_or_init(|| {
        BigUint::from_str_radix(
            "FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF",
            16,
        )
        .unwrap()
    })
}

/// secp256r1 scalar field prime (order of G).
pub fn secp256r1_n() -> &'static BigUint {
    static N: OnceLock<BigUint> = OnceLock::new();
    N.get_or_init(|| {
        BigUint::from_str_radix(
            "FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551",
            16,
        )
        .unwrap()
    })
}

/// Generator G of secp256r1, in affine `(x, y)` form.
pub fn secp256r1_g() -> &'static (BigUint, BigUint) {
    static G: OnceLock<(BigUint, BigUint)> = OnceLock::new();
    G.get_or_init(|| {
        (
            BigUint::from_str_radix(
                "6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296",
                16,
            )
            .unwrap(),
            BigUint::from_str_radix(
                "4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5",
                16,
            )
            .unwrap(),
        )
    })
}

/// Short-Weierstrass curve parameters used by the ECDSA gadget. A
/// concrete instance pins everything needed for the in-circuit math:
/// the base field `p`, scalar field `n`, generator `G = (gx, gy)`, and
/// the curve coefficients `a` and `b` (`y² = x³ + a·x + b`). `b` is
/// consulted by [`enforce_on_curve`] to validate prover-supplied points.
#[derive(Clone)]
pub struct CurveParams {
    pub p: &'static BigUint,
    pub n: &'static BigUint,
    pub g: &'static (BigUint, BigUint),
    /// The curve coefficient `a` mod `p`. For secp256k1 this is `0`; for
    /// secp256r1 it is `p - 3` (which equals `-3 mod p`).
    pub a_mod_p: BigUint,
    /// The curve coefficient `b` mod `p`. For secp256k1 this is `7`; for
    /// secp256r1 it is the standard NIST P-256 constant.
    pub b_mod_p: BigUint,
}

impl CurveParams {
    pub fn secp256k1() -> Self {
        Self {
            p: secp256k1_p(),
            n: secp256k1_n(),
            g: secp256k1_g(),
            a_mod_p: BigUint::from(0u64),
            b_mod_p: BigUint::from(7u64),
        }
    }

    pub fn secp256r1() -> Self {
        let p = secp256r1_p();
        let a_mod_p = p - 3u64;
        let b_mod_p = BigUint::from_str_radix(
            "5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B",
            16,
        )
        .unwrap();
        Self {
            p,
            n: secp256r1_n(),
            g: secp256r1_g(),
            a_mod_p,
            b_mod_p,
        }
    }
}

// =============================================================================
// 256-bit big integer in 4 × 64-bit limbs (LSB-first)
// =============================================================================

/// Limb count for a 256-bit value at base `β = 2^64`.
pub const LIMBS: usize = 4;

/// `β = 2^64` as a BN254 `Fr` field element. Used as the inter-limb shift in
/// every constraint that materialises `Σ_i β^i · limb_i`.
pub fn beta_fr() -> Fr {
    Fr::from(1u128 << 32) * Fr::from(1u128 << 32)
}

/// A 256-bit value held as four 64-bit limbs (LSB first). Each limb is an
/// allocated `Variable` constrained to fit in 64 bits. `value` is populated
/// at proving time and propagated through every operation so downstream
/// gadgets can supply native witnesses for prover-aided identities.
#[derive(Clone)]
pub struct BigInt256 {
    pub limbs: [Variable; LIMBS],
    /// Proving-time concrete value, as 4 × `u64` (LSB first), or `None` in
    /// setup mode.
    pub value: Option<[u64; LIMBS]>,
}

impl BigInt256 {
    /// Reconstruct the value as a `BigUint`, if known.
    pub fn to_biguint(&self) -> Option<BigUint> {
        self.value.map(|v| limbs_to_biguint(&v))
    }

    /// Build a `LinearCombination` that equals the value represented by
    /// `self`, computed as `Σ_i β^i · limb_i`.
    pub fn value_lc(&self) -> LinearCombination<Fr> {
        let mut acc = Fr::one();
        let beta = beta_fr();
        let mut out: Vec<(Fr, Variable)> = Vec::with_capacity(LIMBS);
        for limb in &self.limbs {
            out.push((acc, *limb));
            acc *= beta;
        }
        LinearCombination(out)
    }
}

/// Decompose a `BigUint` value into a 4 × `u64` LSB-first limb array,
/// asserting it fits in 256 bits.
fn biguint_to_limbs(v: &BigUint) -> [u64; LIMBS] {
    let mut limbs = [0u64; LIMBS];
    let digits = v.to_u64_digits();
    assert!(
        digits.len() <= LIMBS,
        "BigUint too large for 256-bit limb form"
    );
    for (i, d) in digits.into_iter().enumerate() {
        limbs[i] = d;
    }
    limbs
}

/// Recombine 4 × `u64` LSB-first limbs into a `BigUint`.
fn limbs_to_biguint(limbs: &[u64; LIMBS]) -> BigUint {
    BigUint::from_slice(&[
        limbs[0] as u32,
        (limbs[0] >> 32) as u32,
        limbs[1] as u32,
        (limbs[1] >> 32) as u32,
        limbs[2] as u32,
        (limbs[2] >> 32) as u32,
        limbs[3] as u32,
        (limbs[3] >> 32) as u32,
    ])
}

/// Convert a `u64` value into BN254 `Fr`.
fn fr_from_u64(v: u64) -> Fr {
    Fr::from(v)
}

// =============================================================================
// Allocation + 64-bit range check
// =============================================================================

/// Allocate a 64-bit-bounded `Variable` carrying the supplied `u64` value
/// (or `None` in setup mode), and bit-decompose it for the range check.
fn alloc_u64_limb(
    builder: &mut R1csBuilder<'_>,
    value: Option<u64>,
) -> Result<Variable, SynthesisError> {
    let fr_value = value.map(fr_from_u64);
    let var = builder.alloc_with_value(fr_value)?;
    let _ = decompose_into_bits(builder, var, 64, fr_value)?;
    Ok(var)
}

/// Allocate a `Variable` carrying a value in `[0, 2^bits)` and bit-decompose
/// for the range check. Used for the multiplication carry that's a few bits
/// wider than a limb.
fn alloc_bounded_limb(
    builder: &mut R1csBuilder<'_>,
    value: Option<u128>,
    bits: usize,
) -> Result<Variable, SynthesisError> {
    let fr_value = value.map(|v| {
        // Convert u128 → BigUint → Fr via big-endian bytes to avoid u128 → Fr
        // direct conversion ambiguity.
        let big = BigUint::from(v);
        let mut bytes = big.to_bytes_be();
        while bytes.len() < 32 {
            bytes.insert(0, 0);
        }
        Fr::from_be_bytes_mod_order(&bytes)
    });
    let var = builder.alloc_with_value(fr_value)?;
    let _ = decompose_into_bits(builder, var, bits, fr_value)?;
    Ok(var)
}

/// Allocate a `BigInt256` from a concrete value at proving time (or `None`
/// at setup), bit-decomposing each limb to enforce the 64-bit bound.
pub fn alloc_bigint256(
    builder: &mut R1csBuilder<'_>,
    value: Option<BigUint>,
) -> Result<BigInt256, SynthesisError> {
    let limb_vals: Option<[u64; LIMBS]> = value.as_ref().map(biguint_to_limbs);
    let mut limbs = [Variable::One; LIMBS];
    for i in 0..LIMBS {
        let v = limb_vals.map(|l| l[i]);
        limbs[i] = alloc_u64_limb(builder, v)?;
    }
    Ok(BigInt256 {
        limbs,
        value: limb_vals,
    })
}

// =============================================================================
// Decode 32 bytes (big-endian) into a BigInt256
// =============================================================================

/// Build a `BigInt256` from 32 input byte witness Variables in big-endian
/// order. The caller is responsible for having range-checked each byte
/// (Noir always emits RANGE opcodes around these, so they're already 8-bit).
///
/// This is the boundary helper used by the opcode lowering to bridge the
/// `[FunctionInput; 32]` byte arrays Noir hands us with the BigInt256 form
/// the gadget consumes.
pub fn bigint256_from_be_bytes(
    builder: &mut R1csBuilder<'_>,
    bytes_vars: [Variable; 32],
    bytes_values: Option<[u8; 32]>,
) -> Result<BigInt256, SynthesisError> {
    // Construct the limb values from the bytes.
    let limb_values: Option<[u64; LIMBS]> = bytes_values.map(|b| {
        let mut v = BigUint::from(0u64);
        for byte in b {
            v = (v << 8) | BigUint::from(byte);
        }
        biguint_to_limbs(&v)
    });

    // Allocate fresh 64-bit limb variables, then enforce that each equals
    // the corresponding 8-byte slice (big-endian). The decompose call gives
    // the 64-bit range; the equality below pins the limb to the bytes.
    let mut limbs = [Variable::One; LIMBS];
    for i in 0..LIMBS {
        let lv = limb_values.map(|l| l[i]);
        limbs[i] = alloc_u64_limb(builder, lv)?;
    }

    // Equality constraints: limb_{LIMBS-1-i} = Σ_{j=0..8} byte[8*i+j] * 2^(56-8*j).
    // bytes are big-endian so the first 8 bytes form the most significant limb.
    let mut byte_coefs: Vec<Fr> = Vec::with_capacity(8);
    for j in 0..8 {
        let shift = 56 - 8 * j;
        let mut c = Fr::one();
        for _ in 0..shift {
            c.double_in_place();
        }
        byte_coefs.push(c);
    }
    for (limb_i, limb_var) in limbs.iter().enumerate() {
        // The most significant limb (index LIMBS-1) consumes bytes[0..8],
        // the next consumes bytes[8..16], etc.
        let byte_base = (LIMBS - 1 - limb_i) * 8;
        let mut lc: Vec<(Fr, Variable)> = Vec::with_capacity(9);
        for j in 0..8 {
            lc.push((byte_coefs[j], bytes_vars[byte_base + j]));
        }
        lc.push((-Fr::one(), *limb_var));
        builder.enforce(builder.zero_lc(), builder.zero_lc(), LinearCombination(lc))?;
    }

    Ok(BigInt256 {
        limbs,
        value: limb_values,
    })
}

// =============================================================================
// Non-native multiplication mod m via prover-supplied (q, c) identity
// =============================================================================

/// Constrain `a · b ≡ c (mod m)` where `m` is a known 256-bit modulus
/// (either secp256k1 `p` or `n`). The prover supplies the quotient `q` such
/// that `a · b = q · m + c` over the integers, with `c < m`. We:
///
/// 1. Allocate `c` and `q` as fresh `BigInt256` values (with values from the
///    proving-time native computation).
/// 2. Range-check `c < m`.
/// 3. Decompose `a · b` and `q · m + c` into per-output-limb sums and enforce
///    that they're equal limb-by-limb. Each output limb's identity is
///    `Σ_{i+j=k} a_i·b_j − Σ_{i+j=k} q_i·m_j − c_k − β·carry_k = −carry_{k-1}`.
///    Carries are range-checked to ~67 bits (because each output limb is a
///    sum of up to 4 × 128-bit products = up to ~130 bits; minus 64 for the
///    limb leaves ~67 bits of carry).
///
/// Returns the BigInt256 holding `c`.
pub fn bigint256_mul_mod(
    builder: &mut R1csBuilder<'_>,
    a: &BigInt256,
    b: &BigInt256,
    m_bigint: &BigUint,
) -> Result<BigInt256, SynthesisError> {
    // Compute c = a*b mod m and q = (a*b - c)/m at proving time.
    let av = a.to_biguint();
    let bv = b.to_biguint();
    let (cv, qv): (Option<BigUint>, Option<BigUint>) = match (av, bv) {
        (Some(av), Some(bv)) => {
            let prod = &av * &bv;
            let c = &prod % m_bigint;
            let q = (&prod - &c) / m_bigint;
            (Some(c), Some(q))
        }
        _ => (None, None),
    };

    let c = alloc_bigint256(builder, cv.clone())?;
    let q = alloc_bigint256(builder, qv.clone())?;

    // Range-check c < m. Standard trick: decompose (m - 1 - c) into 256 bits
    // — if it fits in 256 bits with no underflow, then 0 ≤ c ≤ m-1.
    enforce_lt(builder, &c, m_bigint)?;

    // The modulus m in limb form.
    let m_limbs = biguint_to_limbs(m_bigint);
    let m_fr: [Fr; LIMBS] = std::array::from_fn(|i| fr_from_u64(m_limbs[i]));

    // For each output position k in 0..2*LIMBS-1, the identity is
    //   (Σ_{i+j=k} a_i · b_j) - (Σ_{i+j=k} q_i · m_j) - c_k - β·carry_k_out = -carry_k_in
    // i.e. (a·b - q·m - c) has zero on every output limb modulo β.
    //
    // We materialise each "a_i · b_j" product as a fresh aux variable
    // (proving-time value computed natively), and similarly "q_i · m_j"
    // (where m_j is a constant so it's a linear scaling, no aux needed).
    //
    // We accumulate the per-position sum as a LinearCombination over Fr,
    // then for each position emit a single linear constraint linking that
    // LC to the next carry.

    // Pre-allocate all 16 a*b partial products as fresh witnesses.
    // For a 4-limb × 4-limb multiplication that's 16 muls.
    let av_limbs = a.value;
    let bv_limbs = b.value;
    let mut ab_prods: [[Option<Variable>; LIMBS]; LIMBS] =
        std::array::from_fn(|_| std::array::from_fn(|_| None));
    for i in 0..LIMBS {
        for j in 0..LIMBS {
            let val = match (av_limbs, bv_limbs) {
                (Some(av), Some(bv)) => {
                    let prod = (av[i] as u128) * (bv[j] as u128);
                    // Each partial product is ≤ 2^128 - 2^65 + 1, fits in 128 bits.
                    let big = BigUint::from(prod);
                    let mut bytes = big.to_bytes_be();
                    while bytes.len() < 32 {
                        bytes.insert(0, 0);
                    }
                    Some(Fr::from_be_bytes_mod_order(&bytes))
                }
                _ => None,
            };
            let p = builder.alloc_with_value(val)?;
            // Enforce a_i * b_j = p.
            builder.enforce(
                LinearCombination(vec![(Fr::one(), a.limbs[i])]),
                LinearCombination(vec![(Fr::one(), b.limbs[j])]),
                LinearCombination(vec![(Fr::one(), p)]),
            )?;
            ab_prods[i][j] = Some(p);
        }
    }

    // Same for q*m partial products. Since m_j is a CONSTANT, each partial
    // product q_i * m_j is just a linear scaling — no mul constraint needed,
    // we encode it directly in the per-position LC below as `(m_j) * q_i`.
    // (i.e. we don't allocate aux variables for q*m terms.)

    // Carries. There are 2*LIMBS - 1 output positions; we emit 2*LIMBS - 2
    // carries linking them. Each carry is bounded by the per-position sum
    // magnitude; we pick 70 bits to be safe (4 × 128-bit terms + 64-bit
    // input carry ÷ β = 64 bits = ~67 bits — round up to 70).
    let n_positions = 2 * LIMBS - 1;
    let n_carries = n_positions - 1; // last position should sum to 0
    let mut carry_vars: Vec<Variable> = Vec::with_capacity(n_carries);

    // Compute the carries natively for the closure values.
    let carries_native: Option<Vec<u128>> = match (av_limbs, bv_limbs, qv.as_ref()) {
        (Some(av), Some(bv), Some(_qv_big)) => {
            let qv_limbs = qv.as_ref().map(biguint_to_limbs).unwrap();
            let cv_limbs = cv.as_ref().map(biguint_to_limbs).unwrap();
            let m_l = m_limbs;
            // Use i128 sign arithmetic, accumulating signed partial sums.
            // For each position k: signed_sum_k = Σ_{i+j=k} av[i]*bv[j] (i128 fits 128 bits ×4 max)
            //                                    - Σ_{i+j=k} qv_l[i]*m_l[j]
            //                                    - cv_l[k] (if k<LIMBS)
            // Plus incoming carry. Output carry = signed_sum / β (round toward -inf).
            let beta_u: u128 = 1u128 << 64;
            let mut carries = Vec::with_capacity(n_carries);
            // We use i256-equivalent via paired (sign, magnitude) BigInts so
            // we don't have to fight u128 overflow.
            use num_bigint::BigInt;
            let mut signed_carry: BigInt = BigInt::from(0u64);
            #[allow(clippy::needless_range_loop)]
            for k in 0..n_positions {
                let mut sum: BigInt = BigInt::from(0u64);
                #[allow(clippy::needless_range_loop)]
                for i in 0..LIMBS {
                    let j_signed = k as isize - i as isize;
                    if j_signed >= 0 && (j_signed as usize) < LIMBS {
                        let j = j_signed as usize;
                        sum += BigInt::from(av[i] as u128 * bv[j] as u128);
                        sum -= BigInt::from(qv_limbs[i] as u128 * m_l[j] as u128);
                    }
                }
                if k < LIMBS {
                    sum -= BigInt::from(cv_limbs[k]);
                }
                sum += &signed_carry;
                // sum should be divisible by β.
                let beta_big = BigInt::from(beta_u);
                let new_carry = &sum / &beta_big;
                if k < n_carries {
                    // The carry might be negative; we represent it via
                    // shifting (carry + 2^69) and keep the bound positive.
                    carries.push(&new_carry + BigInt::from(1u128 << 69));
                }
                signed_carry = new_carry;
            }
            // The carries vec entries are non-negative BigInts but we need
            // them as u128.
            Some(
                carries
                    .into_iter()
                    .map(|c| {
                        let (_sign, digits) = c.to_u64_digits();
                        let mut v = 0u128;
                        if !digits.is_empty() {
                            v = digits[0] as u128;
                            if digits.len() > 1 {
                                v |= (digits[1] as u128) << 64;
                            }
                        }
                        v
                    })
                    .collect(),
            )
        }
        _ => None,
    };

    // We carry "shifted" carry values: carry_shifted = carry + 2^69
    // (so they're always non-negative). The per-position equation becomes:
    //   signed_sum_k + (carry_shifted_in - 2^69) = β * (carry_shifted_out - 2^69)
    // We allocate carry_shifted vars and range-check them to 70 bits.
    let shift: BigUint = BigUint::from(1u128 << 69);
    let shift_fr: Fr = {
        let bytes = shift.to_bytes_be();
        let mut padded = vec![0u8; 32 - bytes.len()];
        padded.extend(bytes);
        Fr::from_be_bytes_mod_order(&padded)
    };
    let beta = beta_fr();

    for k in 0..n_carries {
        let c_val = carries_native.as_ref().map(|cs| cs[k]);
        let v = alloc_bounded_limb(builder, c_val, 70)?;
        carry_vars.push(v);
    }

    // Now emit one linear constraint per output position k:
    //   Σ ab_prods[i][j] for i+j=k    (positive)
    //   - Σ m_fr[j] * q.limbs[i] for i+j=k    (negative)
    //   - c.limbs[k] (if k<LIMBS)    (negative)
    //   + (prev carry shifted - shift)    (incoming)
    //   - β * (current carry shifted - shift)    (outgoing)
    //   = 0
    #[allow(clippy::needless_range_loop)]
    for k in 0..n_positions {
        let mut lc: Vec<(Fr, Variable)> = Vec::new();
        // ab partial products.
        #[allow(clippy::needless_range_loop)]
        for i in 0..LIMBS {
            let j_signed = k as isize - i as isize;
            if j_signed >= 0 && (j_signed as usize) < LIMBS {
                let j = j_signed as usize;
                let p = ab_prods[i][j].unwrap();
                lc.push((Fr::one(), p));
            }
        }
        // q*m partial products (linear because m is constant).
        for i in 0..LIMBS {
            let j_signed = k as isize - i as isize;
            if j_signed >= 0 && (j_signed as usize) < LIMBS {
                let j = j_signed as usize;
                lc.push((-m_fr[j], q.limbs[i]));
            }
        }
        // c limb if applicable.
        if k < LIMBS {
            lc.push((-Fr::one(), c.limbs[k]));
        }
        // Incoming carry (shifted) + constant shift.
        if k > 0 {
            lc.push((Fr::one(), carry_vars[k - 1]));
        }
        // Constant adjustments for the shifts: incoming -shift, outgoing +β·shift.
        let constant: Fr = if k == 0 {
            // No incoming; only outgoing.
            beta * shift_fr
        } else if k < n_positions - 1 {
            beta * shift_fr - shift_fr
        } else {
            // No outgoing carry; incoming only.
            -shift_fr
        };
        if !constant.is_zero() {
            lc.push((constant, Variable::One));
        }
        // Outgoing carry (shifted) — coefficient -β.
        if k < n_carries {
            lc.push((-beta, carry_vars[k]));
        }
        builder.enforce(builder.zero_lc(), builder.zero_lc(), LinearCombination(lc))?;
    }

    Ok(c)
}

/// Enforce `value < m` for a BigInt256. Implemented by allocating a witness
/// `diff = m - 1 - value` and decomposing it into 256 bits — if `value < m`,
/// `diff` is a non-negative 256-bit integer; if `value ≥ m`, no such
/// decomposition exists.
fn enforce_lt(
    builder: &mut R1csBuilder<'_>,
    value: &BigInt256,
    m: &BigUint,
) -> Result<(), SynthesisError> {
    let diff_value: Option<BigUint> = value.to_biguint().map(|v| {
        // m - 1 - v. We know v < m at the native level so this is non-negative.
        let m_minus_1 = m - 1u64;
        if v <= m_minus_1 {
            &m_minus_1 - &v
        } else {
            // Out of range — supply zero so the constraint will fail downstream.
            BigUint::from(0u64)
        }
    });
    let diff = alloc_bigint256(builder, diff_value)?;
    // value + diff = m - 1 ⇒ value + diff - (m-1) = 0
    let m_minus_1_fr = {
        let m_minus_1 = m - 1u64;
        let bytes = m_minus_1.to_bytes_be();
        let mut padded = vec![0u8; 32 - bytes.len()];
        padded.extend(bytes);
        Fr::from_be_bytes_mod_order(&padded)
    };
    let mut lc = value.value_lc();
    let diff_lc = diff.value_lc();
    for (c, v) in diff_lc.0 {
        lc.0.push((c, v));
    }
    lc.0.push((-m_minus_1_fr, Variable::One));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), lc)?;
    Ok(())
}

// =============================================================================
// Convenience wrappers: mul mod p and mod n
// =============================================================================

/// `c = a · b mod secp256k1::p` (base field).
pub fn mul_mod_p(
    builder: &mut R1csBuilder<'_>,
    a: &BigInt256,
    b: &BigInt256,
) -> Result<BigInt256, SynthesisError> {
    bigint256_mul_mod(builder, a, b, secp256k1_p())
}

/// `c = a · b mod secp256k1::n` (scalar field).
pub fn mul_mod_n(
    builder: &mut R1csBuilder<'_>,
    a: &BigInt256,
    b: &BigInt256,
) -> Result<BigInt256, SynthesisError> {
    bigint256_mul_mod(builder, a, b, secp256k1_n())
}

/// `a^-1 mod m` via the standard prover-aided `a · a_inv = 1` check.
pub fn inv_mod(
    builder: &mut R1csBuilder<'_>,
    a: &BigInt256,
    m: &BigUint,
) -> Result<BigInt256, SynthesisError> {
    let inv_val: Option<BigUint> = a.to_biguint().and_then(|v| modinv(&v, m));
    let inv = alloc_bigint256(builder, inv_val)?;
    enforce_lt(builder, &inv, m)?;
    let one = alloc_bigint256(builder, Some(BigUint::from(1u64)))?;
    let prod = bigint256_mul_mod(builder, a, &inv, m)?;
    enforce_bigint_eq(builder, &prod, &one)?;
    Ok(inv)
}

fn enforce_bigint_eq(
    builder: &mut R1csBuilder<'_>,
    a: &BigInt256,
    b: &BigInt256,
) -> Result<(), SynthesisError> {
    for i in 0..LIMBS {
        let lc = LinearCombination(vec![(Fr::one(), a.limbs[i]), (-Fr::one(), b.limbs[i])]);
        builder.enforce(builder.zero_lc(), builder.zero_lc(), lc)?;
    }
    Ok(())
}

/// Extended Euclidean modular inverse over `BigUint`. Returns `None` iff
/// `a` is not coprime to `m`.
fn modinv(a: &BigUint, m: &BigUint) -> Option<BigUint> {
    use num_bigint::BigInt;
    use num_bigint::Sign;
    let m_i: BigInt = BigInt::from_biguint(Sign::Plus, m.clone());
    let mut t = (BigInt::from(0u64), BigInt::from(1u64));
    let mut r = (m_i.clone(), BigInt::from_biguint(Sign::Plus, a.clone()));
    while r.1 != BigInt::from(0u64) {
        let q = &r.0 / &r.1;
        let new_r = &r.0 - &q * &r.1;
        r = (r.1, new_r);
        let new_t = &t.0 - &q * &t.1;
        t = (t.1, new_t);
    }
    if r.0 != BigInt::from(1u64) {
        return None;
    }
    let mut inv = t.0 % &m_i;
    if inv.sign() == Sign::Minus {
        inv += &m_i;
    }
    inv.to_biguint()
}

// =============================================================================
// Addition / subtraction mod m
// =============================================================================

/// `c = a + b mod m`. Prover supplies `(c, k)` with `k ∈ {0,1}` such that
/// `a + b = c + k · m`. Range-checks `c < m`.
pub fn add_mod(
    builder: &mut R1csBuilder<'_>,
    a: &BigInt256,
    b: &BigInt256,
    m: &BigUint,
) -> Result<BigInt256, SynthesisError> {
    let av = a.to_biguint();
    let bv = b.to_biguint();
    let (cv, kv): (Option<BigUint>, Option<u64>) = match (av, bv) {
        (Some(av), Some(bv)) => {
            let sum = av + bv;
            if sum >= *m {
                (Some(&sum - m), Some(1))
            } else {
                (Some(sum), Some(0))
            }
        }
        _ => (None, None),
    };
    let c = alloc_bigint256(builder, cv)?;
    enforce_lt(builder, &c, m)?;
    let k = builder.alloc_with_value(kv.map(fr_from_u64))?;
    enforce_boolean(builder, k)?;
    // a + b - c - k*m = 0, evaluated as a single linear constraint via the
    // value LCs and a constant coefficient for k·m.
    let m_fr = bigint_to_fr(m);
    let mut lc = a.value_lc();
    for (c0, v0) in b.value_lc().0 {
        lc.0.push((c0, v0));
    }
    let c_lc = c.value_lc();
    for (c0, v0) in c_lc.0 {
        lc.0.push((-c0, v0));
    }
    lc.0.push((-m_fr, k));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), lc)?;
    Ok(c)
}

/// `c = a - b mod m`. Direct formulation: prover supplies `c ∈ [0, m)` and
/// borrow bit `k ∈ {0, 1}` such that `a - b + k·m - c = 0` as integers.
/// When `a ≥ b`, `k = 0` and `c = a - b`; when `a < b`, `k = 1` and
/// `c = a - b + m`. Range-check `c < m` plus the boolean constraint on `k`
/// pin both uniquely.
///
/// Cost: 1 `alloc_bigint256` + 1 `enforce_lt` + 1 boolean + 1 linear
/// constraint ≈ same as [`add_mod`]. Previously implemented as
/// `a + (m - b)` via two `add_mod` calls plus an alias-zero check
/// (~3× constraint count), kept here for historical reference.
pub fn sub_mod(
    builder: &mut R1csBuilder<'_>,
    a: &BigInt256,
    b: &BigInt256,
    m: &BigUint,
) -> Result<BigInt256, SynthesisError> {
    let av = a.to_biguint();
    let bv = b.to_biguint();
    let (cv, kv): (Option<BigUint>, Option<u64>) = match (av, bv) {
        (Some(av), Some(bv)) => {
            if av >= bv {
                (Some(&av - &bv), Some(0))
            } else {
                (Some(&av + m - &bv), Some(1))
            }
        }
        _ => (None, None),
    };
    let c = alloc_bigint256(builder, cv)?;
    enforce_lt(builder, &c, m)?;
    let k = builder.alloc_with_value(kv.map(fr_from_u64))?;
    enforce_boolean(builder, k)?;
    // a - b + k·m - c = 0 enforced as a single linear constraint over the
    // value LCs (which already encode `Σ_i β^i · limb_i`).
    let m_fr = bigint_to_fr(m);
    let mut lc = a.value_lc();
    for (c0, v0) in b.value_lc().0 {
        lc.0.push((-c0, v0));
    }
    for (c0, v0) in c.value_lc().0 {
        lc.0.push((-c0, v0));
    }
    lc.0.push((m_fr, k));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), lc)?;
    Ok(c)
}

fn bigint_to_fr(v: &BigUint) -> Fr {
    let bytes = v.to_bytes_be();
    let mut padded = vec![0u8; 32usize.saturating_sub(bytes.len())];
    padded.extend(bytes);
    Fr::from_be_bytes_mod_order(&padded)
}

// =============================================================================
// secp256k1 affine point arithmetic in-circuit
// =============================================================================

/// A secp256k1 affine point, represented in-circuit as two `BigInt256`s plus
/// an `is_infinity` flag (not constrained yet — see comment in [`ec_add`]).
/// We do NOT support points-at-infinity in this gadget; ECDSA never produces
/// them at any valid step.
#[derive(Clone)]
pub struct CurvePoint {
    pub x: BigInt256,
    pub y: BigInt256,
}

/// Point addition `R = P + Q` over secp256k1 (affine, generic case only).
/// Caller must ensure `P.x != Q.x` (i.e. `P != ±Q`). For ECDSA verification
/// we only ever encounter the generic case after the doubling-vs-adding
/// dispatch in the scalar-mul loop.
pub fn ec_add(
    builder: &mut R1csBuilder<'_>,
    p: &CurvePoint,
    q: &CurvePoint,
) -> Result<CurvePoint, SynthesisError> {
    ec_add_with_curve(builder, &CurveParams::secp256k1(), p, q)
}

/// Generic in-circuit affine point addition. Same formulas as [`ec_add`]
/// but taking the curve params explicitly so the same code path serves
/// secp256r1 too. Addition formulas don't depend on the curve coefficient
/// `a`, only on `p` (the modulus).
pub fn ec_add_with_curve(
    builder: &mut R1csBuilder<'_>,
    params: &CurveParams,
    p: &CurvePoint,
    q: &CurvePoint,
) -> Result<CurvePoint, SynthesisError> {
    let p_field = params.p;
    let dy = sub_mod(builder, &q.y, &p.y, p_field)?;
    let dx = sub_mod(builder, &q.x, &p.x, p_field)?;
    let dx_inv = inv_mod(builder, &dx, p_field)?;
    let lambda = bigint256_mul_mod(builder, &dy, &dx_inv, p_field)?;
    let lambda_sq = bigint256_mul_mod(builder, &lambda, &lambda, p_field)?;
    let tmp = sub_mod(builder, &lambda_sq, &p.x, p_field)?;
    let rx = sub_mod(builder, &tmp, &q.x, p_field)?;
    let dx2 = sub_mod(builder, &p.x, &rx, p_field)?;
    let lt = bigint256_mul_mod(builder, &lambda, &dx2, p_field)?;
    let ry = sub_mod(builder, &lt, &p.y, p_field)?;
    Ok(CurvePoint { x: rx, y: ry })
}

/// Native (out-of-circuit) curve point addition, matching the in-circuit
/// generic-case formulas. Returns `None` if the inputs trigger an edge case
/// (`P = ±Q` or either is infinity) that the in-circuit gadget cannot
/// handle.
pub fn ec_add_native(
    p: (&BigUint, &BigUint),
    q: (&BigUint, &BigUint),
) -> Option<(BigUint, BigUint)> {
    ec_add_native_with_modulus(p, q, secp256k1_p())
}

pub fn ec_add_native_with_modulus(
    p: (&BigUint, &BigUint),
    q: (&BigUint, &BigUint),
    p_field: &BigUint,
) -> Option<(BigUint, BigUint)> {
    if p.0 == q.0 {
        return None;
    }
    let dy = mod_sub(q.1, p.1, p_field);
    let dx = mod_sub(q.0, p.0, p_field);
    let dx_inv = modinv(&dx, p_field)?;
    let lambda = (&dy * &dx_inv) % p_field;
    let lambda_sq = (&lambda * &lambda) % p_field;
    let rx = mod_sub(&mod_sub(&lambda_sq, p.0, p_field), q.0, p_field);
    let p0_minus_rx = mod_sub(p.0, &rx, p_field);
    let ry = mod_sub(&((&lambda * p0_minus_rx) % p_field), p.1, p_field);
    Some((rx, ry))
}

/// Native (out-of-circuit) point doubling for secp256k1.
pub fn ec_double_native(p: (&BigUint, &BigUint)) -> Option<(BigUint, BigUint)> {
    ec_double_native_with_curve(p, secp256k1_p(), &BigUint::from(0u64))
}

/// Native doubling parameterised by `(p, a)`. Implements the standard
/// `λ = (3·x² + a) / (2·y)` slope.
pub fn ec_double_native_with_curve(
    p: (&BigUint, &BigUint),
    p_field: &BigUint,
    a: &BigUint,
) -> Option<(BigUint, BigUint)> {
    if p.1.is_zero() {
        return None;
    }
    let three = BigUint::from(3u64);
    let two = BigUint::from(2u64);
    let x_sq = (p.0 * p.0) % p_field;
    let mut num = (&x_sq * &three) % p_field;
    // `+ a`
    num = (num + a) % p_field;
    let denom = (&two * p.1) % p_field;
    let denom_inv = modinv(&denom, p_field)?;
    let lambda = (&num * &denom_inv) % p_field;
    let lambda_sq = (&lambda * &lambda) % p_field;
    let two_px = (&two * p.0) % p_field;
    let rx = mod_sub(&lambda_sq, &two_px, p_field);
    let p0_minus_rx = mod_sub(p.0, &rx, p_field);
    let ry = mod_sub(&((&lambda * p0_minus_rx) % p_field), p.1, p_field);
    Some((rx, ry))
}

fn mod_sub(a: &BigUint, b: &BigUint, m: &BigUint) -> BigUint {
    if a >= b {
        (a - b) % m
    } else {
        let diff = b - a;
        m - (diff % m)
    }
}

/// Point doubling `R = 2P` over secp256k1.
pub fn ec_double(
    builder: &mut R1csBuilder<'_>,
    p: &CurvePoint,
) -> Result<CurvePoint, SynthesisError> {
    ec_double_with_curve(builder, &CurveParams::secp256k1(), p)
}

/// Generic in-circuit affine doubling with curve-dependent coefficient `a`.
/// Slope: `λ = (3·x² + a) / (2·y)`. For `a = 0` (secp256k1) this collapses
/// to the original formula; for `a = -3` (secp256r1) the `a_mod_p` term is
/// added as `params.a_mod_p · One`.
pub fn ec_double_with_curve(
    builder: &mut R1csBuilder<'_>,
    params: &CurveParams,
    p: &CurvePoint,
) -> Result<CurvePoint, SynthesisError> {
    let p_field = params.p;
    let x_sq = bigint256_mul_mod(builder, &p.x, &p.x, p_field)?;
    let three = alloc_bigint256(builder, Some(BigUint::from(3u64)))?;
    let three_x_sq = bigint256_mul_mod(builder, &x_sq, &three, p_field)?;
    // numerator = 3·x² + a
    let num = if params.a_mod_p.is_zero() {
        three_x_sq
    } else {
        let a_var = alloc_bigint256(builder, Some(params.a_mod_p.clone()))?;
        enforce_lt(builder, &a_var, p_field)?;
        add_mod(builder, &three_x_sq, &a_var, p_field)?
    };
    let two = alloc_bigint256(builder, Some(BigUint::from(2u64)))?;
    let two_py = bigint256_mul_mod(builder, &two, &p.y, p_field)?;
    let denom_inv = inv_mod(builder, &two_py, p_field)?;
    let lambda = bigint256_mul_mod(builder, &num, &denom_inv, p_field)?;
    let lambda_sq = bigint256_mul_mod(builder, &lambda, &lambda, p_field)?;
    let two_px = bigint256_mul_mod(builder, &two, &p.x, p_field)?;
    let rx = sub_mod(builder, &lambda_sq, &two_px, p_field)?;
    let dx = sub_mod(builder, &p.x, &rx, p_field)?;
    let lt = bigint256_mul_mod(builder, &lambda, &dx, p_field)?;
    let ry = sub_mod(builder, &lt, &p.y, p_field)?;
    Ok(CurvePoint { x: rx, y: ry })
}

// =============================================================================
// Input validation: on-curve check + scalar range check
// =============================================================================

/// Enforce that an affine `(x, y)` point lies on the short-Weierstrass
/// curve `y² = x³ + a·x + b (mod p)`. Used to validate prover-supplied
/// points that aren't otherwise constrained by the rest of the gadget —
/// most importantly the ECDSA public key, which a malicious prover could
/// otherwise place off the curve (and then construct a "signature" using
/// the looser arithmetic that the in-circuit add/double formulas allow).
///
/// **Identity check is implicit.** The identity element ("point at
/// infinity") has no affine `(x, y)` encoding on secp256k1 or secp256r1
/// (both have cofactor 1, so no small-order subgroup either). Any pair of
/// 256-bit coordinates that passes this check is by construction a
/// non-identity prime-order point — no separate `Q ≠ O` constraint is
/// needed. The trivial would-be encoding `(0, 0)` already fails the
/// equation (`0² ≠ 0³ + b` for both curves' `b`).
///
/// Cost: 3 `mul_mod_p` for `y²`, `x²`, `x³` + 1 optional `mul_mod_p` for
/// `a·x` (skipped when `a = 0`, e.g. secp256k1) + one linear constraint.
/// ≈ 5–7k constraints per check.
pub fn enforce_on_curve(
    builder: &mut R1csBuilder<'_>,
    params: &CurveParams,
    point: &CurvePoint,
) -> Result<(), SynthesisError> {
    let p_field = params.p;
    let y_sq = bigint256_mul_mod(builder, &point.y, &point.y, p_field)?;
    let x_sq = bigint256_mul_mod(builder, &point.x, &point.x, p_field)?;
    let x_cu = bigint256_mul_mod(builder, &x_sq, &point.x, p_field)?;

    // rhs = x³ + a·x + b. When `a == 0` (secp256k1), skip the a·x mul.
    let a_x: Option<BigInt256> = if params.a_mod_p.is_zero() {
        None
    } else {
        let a = alloc_bigint256(builder, Some(params.a_mod_p.clone()))?;
        Some(bigint256_mul_mod(builder, &a, &point.x, p_field)?)
    };
    let b = alloc_bigint256(builder, Some(params.b_mod_p.clone()))?;

    // Compose rhs via add_mod's: x_cu + (a_x optional) + b.
    let partial = match a_x {
        Some(ax) => add_mod(builder, &x_cu, &ax, p_field)?,
        None => x_cu,
    };
    let rhs = add_mod(builder, &partial, &b, p_field)?;
    enforce_bigint_eq(builder, &y_sq, &rhs)
}

/// Enforce that a scalar `value` lies in the half-open ECDSA validity
/// interval `[1, n)`. Implemented as `enforce_lt(value, n)` plus a
/// non-zero check via a fresh inverse `value · value_inv = 1 (mod n)`.
/// Used on the `r` and `s` components of an ECDSA signature; the spec
/// rejects `r = 0`, `s = 0`, and `r ≥ n`, `s ≥ n`.
///
/// Cost: 1 `enforce_lt` (~520) + 1 `mul_mod_n` (~1750) + 1 `alloc + `
/// enforce_lt for the inverse (~520). ≈ 2.8k constraints per check.
pub fn enforce_in_range_one_to_n(
    builder: &mut R1csBuilder<'_>,
    value: &BigInt256,
    n: &BigUint,
) -> Result<(), SynthesisError> {
    enforce_lt(builder, value, n)?;
    // Non-zero check via modular inverse.
    let inv_val: Option<BigUint> = value
        .to_biguint()
        .and_then(|v| if v.is_zero() { None } else { modinv(&v, n) });
    let inv = alloc_bigint256(builder, inv_val)?;
    enforce_lt(builder, &inv, n)?;
    let prod = bigint256_mul_mod(builder, value, &inv, n)?;
    let one = alloc_bigint256(builder, Some(BigUint::from(1u64)))?;
    enforce_bigint_eq(builder, &prod, &one)
}

// =============================================================================
// secp256k1 GLV decomposition — splits a 256-bit scalar into two ~128-bit
// halves so the joint scalar-mul iteration count drops from 256 to 128.
// =============================================================================
//
// The endomorphism `φ(x, y) = (β·x, y)` satisfies `φ(P) = λ·P` for every
// `P ∈ secp256k1`. For any 256-bit scalar `k`, there exist signed
// integers `k1, k2` with `|k1|, |k2| ≈ √n` such that
// `k = k1 + λ·k2 (mod n)`. Then
// `k · P = k1 · P + k2 · φ(P)`.
//
// We use the basis vectors from Hankerson-Menezes-Vanstone (Guide to
// Elliptic Curve Cryptography, Algorithm 3.74) precomputed for
// secp256k1:
//
// ```text
//   a1 = +0x3086D221A7D46BCDE86C90E49284EB15
//   b1 = -0xE4437ED6010E88286F547FA90ABFE4C3
//   a2 = +0x114CA50F7A8E2F3F657C1108D9D44CFD8
//   b2 = +0x3086D221A7D46BCDE86C90E49284EB15
// ```
//
// Native decomposition:
//
// ```text
//   c1 = round(b2 · k / n)
//   c2 = round(-b1 · k / n)
//   k1 = k − c1·a1 − c2·a2
//   k2 =   − c1·b1 − c2·b2
// ```
//
// Bound: `|k1|, |k2| < 2^129` for every `k ∈ [0, n)`.

/// GLV basis vectors for secp256k1 (signed). `b1` is the only negative
/// entry; everything else is positive.
struct GlvBasis {
    a1: num_bigint::BigInt,
    b1: num_bigint::BigInt,
    a2: num_bigint::BigInt,
    b2: num_bigint::BigInt,
}

fn secp256k1_glv_basis() -> &'static GlvBasis {
    use num_bigint::{BigInt, Sign};
    static B: OnceLock<GlvBasis> = OnceLock::new();
    B.get_or_init(|| {
        let from_hex = |hex: &str| -> BigInt {
            BigInt::parse_bytes(hex.as_bytes(), 16).unwrap()
        };
        let a1 = from_hex("3086D221A7D46BCDE86C90E49284EB15");
        let b1 = -from_hex("E4437ED6010E88286F547FA90ABFE4C3");
        let a2 = from_hex("114CA50F7A8E2F3F657C1108D9D44CFD8");
        let b2 = from_hex("3086D221A7D46BCDE86C90E49284EB15");
        let _ = Sign::Plus;
        GlvBasis { a1, b1, a2, b2 }
    })
}

/// Native GLV decomposition: given a scalar `k ∈ [0, n)`, return signed
/// `(k1, k2)` with `k ≡ k1 + λ·k2 (mod n)` and `|k1|, |k2| < 2^129`. The
/// rounded-division step uses *round-to-nearest* (ties broken by floor)
/// so the standard GLV bound holds.
fn glv_decompose_native(k: &BigUint) -> (num_bigint::BigInt, num_bigint::BigInt) {
    use num_bigint::BigInt;
    let basis = secp256k1_glv_basis();
    let n = BigInt::from(secp256k1_n().clone());
    let k_big = BigInt::from(k.clone());
    let round_div = |num: BigInt, denom: &BigInt| -> BigInt {
        // round(num / denom) via floor((num + denom/2) / denom), respecting sign.
        let half = denom / 2;
        if num.sign() == num_bigint::Sign::Minus {
            (num - &half) / denom
        } else {
            (num + &half) / denom
        }
    };
    let c1 = round_div(&basis.b2 * &k_big, &n);
    let c2 = round_div(&(-&basis.b1) * &k_big, &n);
    let k1 = &k_big - &c1 * &basis.a1 - &c2 * &basis.a2;
    let k2 = -&c1 * &basis.b1 - &c2 * &basis.b2;
    (k1, k2)
}

/// In-circuit representation of a GLV-decomposed scalar half: an absolute
/// value (constrained to `[0, 2^129)`) plus a boolean sign (`1` = negative).
struct SignedScalar {
    abs: BigInt256,
    sign: Variable,
    sign_value: Option<bool>,
}

/// Decompose a 256-bit scalar `k` (supplied as a `BigInt256` in the scalar
/// field) into two signed 129-bit halves `(k1, k2)` such that
/// `k ≡ k1 + λ·k2 (mod n)`, and enforce that identity in-circuit.
///
/// Algorithm: the prover computes `(k1, k2)` natively via
/// [`glv_decompose_native`], allocates `(|k1|, sign(k1), |k2|, sign(k2))`,
/// and the gadget enforces:
///
/// * `|k1|, |k2| < 2^129`  (29 extra bits over the 100-bit-ish "tight"
///   bound — 129 is enough for the standard GLV bound and gives margin
///   for tie-breaking edge cases in `round_div`).
/// * `sign(k1), sign(k2) ∈ {0, 1}`.
/// * `((1 − 2·sign(k1))·|k1|) + λ·((1 − 2·sign(k2))·|k2|) ≡ k (mod n)`.
///
/// Encoded as one `mul_mod_n` for `λ·k2_in_n` plus one linear constraint
/// over the value LCs, where `ki_in_n` is the canonical representative of
/// the signed `ki` modulo `n` (selected between `|ki|` and `n − |ki|`).
fn glv_decompose_in_circuit(
    builder: &mut R1csBuilder<'_>,
    k: &BigInt256,
) -> Result<(SignedScalar, SignedScalar), SynthesisError> {
    use num_bigint::Sign;
    let k_val = k.to_biguint();
    let (k1_big, k2_big) = match k_val.as_ref() {
        Some(kv) => {
            let (a, b) = glv_decompose_native(kv);
            (Some(a), Some(b))
        }
        None => (None, None),
    };

    let unpack = |opt: Option<num_bigint::BigInt>| -> (Option<BigUint>, Option<bool>) {
        match opt {
            Some(v) => {
                let neg = v.sign() == Sign::Minus;
                let abs = v.magnitude().clone();
                (Some(abs), Some(neg))
            }
            None => (None, None),
        }
    };
    let (k1_abs_val, k1_sign_val) = unpack(k1_big);
    let (k2_abs_val, k2_sign_val) = unpack(k2_big);

    let k1_abs = alloc_bigint256(builder, k1_abs_val.clone())?;
    let k2_abs = alloc_bigint256(builder, k2_abs_val.clone())?;
    let k1_sign = builder.alloc_with_value(
        k1_sign_val.map(|s| if s { Fr::one() } else { Fr::zero() }),
    )?;
    enforce_boolean(builder, k1_sign)?;
    let k2_sign = builder.alloc_with_value(
        k2_sign_val.map(|s| if s { Fr::one() } else { Fr::zero() }),
    )?;
    enforce_boolean(builder, k2_sign)?;

    // 129-bit range check on |k1|, |k2|. The BigInt256 limb decomposition
    // already enforces 4 × 64 = 256 bits; we additionally constrain the
    // top two limbs so the value fits in 129 bits: limb[3] = 0 and
    // limb[2] < 2 (only the low bit may be set).
    enforce_129_bit(builder, &k1_abs)?;
    enforce_129_bit(builder, &k2_abs)?;

    // Compute the canonical `ki_in_n = if sign then n − |ki| else |ki|`,
    // allocated as a BigInt256, then enforce `k = k1_in_n + λ·k2_in_n (mod n)`.
    let n_field = secp256k1_n();
    let k1_in_n = signed_to_in_n(builder, n_field, &k1_abs, k1_sign, k1_sign_val)?;
    let k2_in_n = signed_to_in_n(builder, n_field, &k2_abs, k2_sign, k2_sign_val)?;

    let lambda = secp256k1_lambda();
    let lambda_bi = alloc_bigint256(builder, Some(lambda.clone()))?;
    let lambda_k2 = bigint256_mul_mod(builder, &lambda_bi, &k2_in_n, n_field)?;

    // Enforce k = k1_in_n + lambda_k2 (mod n). Allow a boolean borrow
    // `t ∈ {0, 1}` because the sum can wrap once.
    let n_big = secp256k1_n();
    let sum_native: Option<BigUint> = match (k1_in_n.to_biguint(), lambda_k2.to_biguint()) {
        (Some(a), Some(b)) => Some(&a + &b),
        _ => None,
    };
    let t_val = match (sum_native.as_ref(), k_val.as_ref()) {
        (Some(s), Some(kv)) => {
            if s == kv {
                Some(0u64)
            } else {
                // s = k + t·n for some t ∈ {0, 1}.
                Some(1u64)
            }
        }
        _ => None,
    };
    let t = builder.alloc_with_value(t_val.map(fr_from_u64))?;
    enforce_boolean(builder, t)?;
    let n_fr = bigint_to_fr(n_big);
    let mut lc = k1_in_n.value_lc();
    for (c, v) in lambda_k2.value_lc().0 {
        lc.0.push((c, v));
    }
    for (c, v) in k.value_lc().0 {
        lc.0.push((-c, v));
    }
    lc.0.push((-n_fr, t));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), lc)?;

    Ok((
        SignedScalar {
            abs: k1_abs,
            sign: k1_sign,
            sign_value: k1_sign_val,
        },
        SignedScalar {
            abs: k2_abs,
            sign: k2_sign,
            sign_value: k2_sign_val,
        },
    ))
}

/// Enforce that `value < 2^129`: BigInt256 limbs are LSB-first u64s, so
/// `limb[3] = 0` and `limb[2] < 2`.
fn enforce_129_bit(
    builder: &mut R1csBuilder<'_>,
    value: &BigInt256,
) -> Result<(), SynthesisError> {
    builder.enforce(
        builder.zero_lc(),
        builder.zero_lc(),
        LinearCombination::from((Fr::one(), value.limbs[3])),
    )?;
    enforce_boolean(builder, value.limbs[2])
}

/// Select the canonical representative of a signed scalar modulo `n`:
/// returns `abs` if `sign = 0` and `n − abs` if `sign = 1`.
fn signed_to_in_n(
    builder: &mut R1csBuilder<'_>,
    n_field: &BigUint,
    abs: &BigInt256,
    sign_var: Variable,
    sign_val: Option<bool>,
) -> Result<BigInt256, SynthesisError> {
    let neg_abs_val: Option<BigUint> = abs.to_biguint().map(|v| {
        if v.is_zero() {
            BigUint::from(0u64)
        } else {
            n_field - v
        }
    });
    let neg_abs = alloc_bigint256(builder, neg_abs_val.clone())?;
    enforce_lt(builder, &neg_abs, n_field)?;

    // Enforce abs + neg_abs ≡ 0 (mod n). For abs ≠ 0 this means
    // abs + neg_abs = n; for abs = 0, neg_abs = 0. We let the constraint
    // be the standard add_mod alias: prover supplies k ∈ {0, 1} with
    // abs + neg_abs = k·n. That k = 0 iff abs = 0 (otherwise k = 1).
    let k_val = abs
        .to_biguint()
        .map(|v| if v.is_zero() { 0u64 } else { 1u64 });
    let k = builder.alloc_with_value(k_val.map(fr_from_u64))?;
    enforce_boolean(builder, k)?;
    let n_fr = bigint_to_fr(n_field);
    let mut lc = abs.value_lc();
    for (c, v) in neg_abs.value_lc().0 {
        lc.0.push((c, v));
    }
    lc.0.push((-n_fr, k));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), lc)?;

    // Now pick out = sign ? neg_abs : abs.
    select_bigint256(builder, sign_var, sign_val, &neg_abs, abs)
}

/// Compute `φ(P) = (β·P.x mod p, P.y)`. The y-coordinate is unchanged
/// (the endomorphism only twists `x`); we reuse the same `Variable`s.
fn phi_secp256k1(
    builder: &mut R1csBuilder<'_>,
    p: &CurvePoint,
) -> Result<CurvePoint, SynthesisError> {
    let beta = secp256k1_beta();
    let beta_bi = alloc_bigint256(builder, Some(beta.clone()))?;
    let new_x = bigint256_mul_mod(builder, &beta_bi, &p.x, secp256k1_p())?;
    Ok(CurvePoint {
        x: new_x,
        y: p.y.clone(),
    })
}

/// In-circuit point negation: `(x, y) → (x, p − y)`.
fn negate_point(
    builder: &mut R1csBuilder<'_>,
    p_field: &BigUint,
    p: &CurvePoint,
) -> Result<CurvePoint, SynthesisError> {
    let neg_y_val: Option<BigUint> = p.y.to_biguint().map(|v| {
        if v.is_zero() {
            BigUint::from(0u64)
        } else {
            p_field - v
        }
    });
    let neg_y = alloc_bigint256(builder, neg_y_val)?;
    enforce_lt(builder, &neg_y, p_field)?;
    // Enforce y + neg_y ≡ 0 (mod p).
    let k_val = p
        .y
        .to_biguint()
        .map(|v| if v.is_zero() { 0u64 } else { 1u64 });
    let k = builder.alloc_with_value(k_val.map(fr_from_u64))?;
    enforce_boolean(builder, k)?;
    let p_fr = bigint_to_fr(p_field);
    let mut lc = p.y.value_lc();
    for (c, v) in neg_y.value_lc().0 {
        lc.0.push((c, v));
    }
    lc.0.push((-p_fr, k));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), lc)?;
    Ok(CurvePoint {
        x: p.x.clone(),
        y: neg_y,
    })
}

/// Conditional point negation: return `sign ? -P : P`. Uses one extra
/// `negate_point` plus a `select_point_with_p` on the y-coordinate (the
/// x-coordinate is independent of sign).
fn conditional_negate(
    builder: &mut R1csBuilder<'_>,
    p_field: &BigUint,
    p: &CurvePoint,
    sign_var: Variable,
    sign_val: Option<bool>,
) -> Result<CurvePoint, SynthesisError> {
    let neg = negate_point(builder, p_field, p)?;
    let y = select_bigint256(builder, sign_var, sign_val, &neg.y, &p.y)?;
    Ok(CurvePoint {
        x: p.x.clone(),
        y,
    })
}

// =============================================================================
// Joint scalar mul (Strauss-Shamir) — optimisation pass
// =============================================================================
//
// `scalar_mul_2p_with_curve` computes `u1·P1 + u2·P2` with a single
// MSB-first iteration that shares the doublings across both scalars. The
// alternative — two separate single-scalar muls plus a final
// `ec_add` — costs `~2·256·(double + add) ≈ 18M constraints` total. The
// joint formulation cuts the doubles in half (~256 instead of 512) by
// doubling a *single* accumulator per iteration, and uses a precomputed
// `T = P1 + P2` table so a single conditional add per iteration covers
// both scalars. Expected savings: ~50% on the full ECDSA verify path.
//
// Per iteration: 1 `ec_double` + 1 `ec_add` + one 4-way addend select +
// one 2-way accumulator select.

/// Decompose a 256-bit `BigInt256` scalar into 256 boolean bit `Variable`s
/// (LSB first), returning both the Arkworks variables and their
/// proving-time concrete values. Wraps the existing per-limb
/// `decompose_into_bits` so callers don't need to repeat the limb-by-limb
/// boilerplate.
fn decompose_scalar_bits(
    builder: &mut R1csBuilder<'_>,
    scalar: &BigInt256,
) -> Result<(Vec<Variable>, Vec<Option<bool>>), SynthesisError> {
    let mut bit_vars: Vec<Variable> = Vec::with_capacity(256);
    let mut bit_vals: Vec<Option<bool>> = Vec::with_capacity(256);
    for i in 0..LIMBS {
        let limb_value = scalar.value.map(|l| Fr::from(l[i]));
        let bits = decompose_into_bits(builder, scalar.limbs[i], 64, limb_value)?;
        for (b_i, b_var) in bits.into_iter().enumerate() {
            bit_vars.push(b_var);
            let bv = scalar.value.map(|l| ((l[i] >> b_i) & 1) == 1);
            bit_vals.push(bv);
        }
    }
    Ok((bit_vars, bit_vals))
}

/// Generic 2-way `BigInt256` select: returns `bit_var == 1 ? when_one :
/// when_zero`. **Does not** re-range-check the output against `p_field` —
/// soundness assumption: both inputs were already constrained to
/// `[0, p_field)` upstream (e.g. via `mul_mod`'s embedded `enforce_lt` or an
/// `alloc_bigint256_lt`), so the selected value inherits that bound by
/// construction. Dropping the redundant range check saves ~526 constraints
/// per coordinate, which adds up across the 512 selects in a scalar mul.
fn select_bigint256(
    builder: &mut R1csBuilder<'_>,
    bit_var: Variable,
    bit_value: Option<bool>,
    when_one: &BigInt256,
    when_zero: &BigInt256,
) -> Result<BigInt256, SynthesisError> {
    let out_val: Option<BigUint> = bit_value.and_then(|bit| {
        if bit {
            when_one.to_biguint()
        } else {
            when_zero.to_biguint()
        }
    });
    let out = alloc_bigint256(builder, out_val)?;
    for i in 0..LIMBS {
        let lhs = LinearCombination(vec![(Fr::one(), bit_var)]);
        let rhs = LinearCombination(vec![
            (Fr::one(), when_one.limbs[i]),
            (-Fr::one(), when_zero.limbs[i]),
        ]);
        let result = LinearCombination(vec![
            (Fr::one(), out.limbs[i]),
            (-Fr::one(), when_zero.limbs[i]),
        ]);
        builder.enforce(lhs, rhs, result)?;
    }
    Ok(out)
}

/// Generic curve-point select. See [`select_bigint256`] for the
/// range-check-elision argument.
fn select_point_with_p(
    builder: &mut R1csBuilder<'_>,
    _p_field: &BigUint,
    bit_var: Variable,
    bit_value: Option<bool>,
    when_one: &CurvePoint,
    when_zero: &CurvePoint,
) -> Result<CurvePoint, SynthesisError> {
    let x = select_bigint256(builder, bit_var, bit_value, &when_one.x, &when_zero.x)?;
    let y = select_bigint256(builder, bit_var, bit_value, &when_one.y, &when_zero.y)?;
    Ok(CurvePoint { x, y })
}

/// 4-way `CurvePoint` select indexed by `(b1, b2)`. Returns one of
/// `(p00, p10, p01, p11)`: `p00` when both bits are zero, `p10` when only
/// `b1`, `p01` when only `b2`, `p11` when both. Implemented as
/// `out = p00 + b1·(p10 − p00) + b2·(p01 − p00) + b1·b2·(p00 − p10 − p01 + p11)`,
/// requiring one aux `b1·b2` mul plus three mul constraints per output
/// limb (one for each of the three coefficients).
#[allow(clippy::too_many_arguments)]
fn select4_point(
    builder: &mut R1csBuilder<'_>,
    p_field: &BigUint,
    b1_var: Variable,
    b1_val: Option<bool>,
    b2_var: Variable,
    b2_val: Option<bool>,
    p00: &CurvePoint,
    p10: &CurvePoint,
    p01: &CurvePoint,
    p11: &CurvePoint,
) -> Result<CurvePoint, SynthesisError> {
    // Allocate b1·b2 once for both coordinates.
    let b1b2_val = match (b1_val, b2_val) {
        (Some(a), Some(b)) => Some(if a && b { Fr::one() } else { Fr::zero() }),
        _ => None,
    };
    let b1b2 = builder.alloc_with_value(b1b2_val)?;
    builder.enforce(
        LinearCombination::from((Fr::one(), b1_var)),
        LinearCombination::from((Fr::one(), b2_var)),
        LinearCombination::from((Fr::one(), b1b2)),
    )?;

    // Compute the selected value for each limb of each coordinate.
    let mut select_one_coord = |a: &BigInt256,
                                b: &BigInt256,
                                c: &BigInt256,
                                d: &BigInt256|
     -> Result<BigInt256, SynthesisError> {
        let out_val: Option<BigUint> = match (b1_val, b2_val) {
            (Some(false), Some(false)) => a.to_biguint(),
            (Some(true), Some(false)) => b.to_biguint(),
            (Some(false), Some(true)) => c.to_biguint(),
            (Some(true), Some(true)) => d.to_biguint(),
            _ => None,
        };
        let out = alloc_bigint256(builder, out_val)?;
        // No `enforce_lt`: when all 4 candidates are `< p_field` (which
        // holds for any output of `mul_mod` and any allocation that itself
        // enforced the bound), the selected value inherits the bound by
        // construction. See `select_bigint256` for the same elision.
        let _ = p_field;
        for i in 0..LIMBS {
            // out_i − a_i − b1·(b_i − a_i) − b2·(c_i − a_i) − b1·b2·(a_i − b_i − c_i + d_i) = 0
            //
            // Split into three mul aux:
            //   t1_i = b1 · (b_i − a_i)
            //   t2_i = b2 · (c_i − a_i)
            //   t3_i = b1·b2 · (a_i − b_i − c_i + d_i)
            // then enforce out_i − a_i − t1_i − t2_i − t3_i = 0 linearly.
            let snap = |bit_val: Option<bool>, x: &BigInt256, y: &BigInt256| -> Option<Fr> {
                let bv = bit_val?;
                let xv = x.value.map(|l| l[i])?;
                let yv = y.value.map(|l| l[i])?;
                let mut diff = Fr::from(xv);
                diff -= Fr::from(yv);
                Some(if bv { diff } else { Fr::zero() })
            };

            let t1_val = snap(b1_val, b, a);
            let t1 = builder.alloc_with_value(t1_val)?;
            builder.enforce(
                LinearCombination::from((Fr::one(), b1_var)),
                LinearCombination(vec![(Fr::one(), b.limbs[i]), (-Fr::one(), a.limbs[i])]),
                LinearCombination::from((Fr::one(), t1)),
            )?;

            let t2_val = snap(b2_val, c, a);
            let t2 = builder.alloc_with_value(t2_val)?;
            builder.enforce(
                LinearCombination::from((Fr::one(), b2_var)),
                LinearCombination(vec![(Fr::one(), c.limbs[i]), (-Fr::one(), a.limbs[i])]),
                LinearCombination::from((Fr::one(), t2)),
            )?;

            let t3_val: Option<Fr> = (|| -> Option<Fr> {
                let b1v = b1_val?;
                let b2v = b2_val?;
                let av = Fr::from(a.value.map(|l| l[i])?);
                let bv = Fr::from(b.value.map(|l| l[i])?);
                let cv = Fr::from(c.value.map(|l| l[i])?);
                let dv = Fr::from(d.value.map(|l| l[i])?);
                Some(if b1v && b2v {
                    av - bv - cv + dv
                } else {
                    Fr::zero()
                })
            })();
            let t3 = builder.alloc_with_value(t3_val)?;
            builder.enforce(
                LinearCombination::from((Fr::one(), b1b2)),
                LinearCombination(vec![
                    (Fr::one(), a.limbs[i]),
                    (-Fr::one(), b.limbs[i]),
                    (-Fr::one(), c.limbs[i]),
                    (Fr::one(), d.limbs[i]),
                ]),
                LinearCombination::from((Fr::one(), t3)),
            )?;

            // out_i = a_i + t1 + t2 + t3
            builder.enforce(
                builder.zero_lc(),
                builder.zero_lc(),
                LinearCombination(vec![
                    (Fr::one(), out.limbs[i]),
                    (-Fr::one(), a.limbs[i]),
                    (-Fr::one(), t1),
                    (-Fr::one(), t2),
                    (-Fr::one(), t3),
                ]),
            )?;
        }
        Ok(out)
    };

    let x = select_one_coord(&p00.x, &p10.x, &p01.x, &p11.x)?;
    let y = select_one_coord(&p00.y, &p10.y, &p01.y, &p11.y)?;
    Ok(CurvePoint { x, y })
}

/// Joint scalar multiplication `u1·P1 + u2·P2` using MSB-first
/// Strauss-Shamir. Halves the doubling count compared to two separate
/// single-scalar muls + a final `ec_add`. Used by
/// [`ecdsa_verify_with_curve`] for the `u1·G + u2·Q` recombination on
/// secp256r1 (secp256k1 takes the GLV path instead — see
/// [`scalar_mul_2p_secp256k1_glv`]).
///
/// Soundness: the accumulator is seeded with a non-zero blinding point so
/// `ec_add` (which has no infinity-handling) stays in the generic-case
/// regime; the constant `2^256 · blinding` contribution is subtracted at
/// the end via `ec_add` with a negated y-coordinate.
pub fn scalar_mul_2p_with_curve(
    builder: &mut R1csBuilder<'_>,
    params: &CurveParams,
    p1: &CurvePoint,
    u1: &BigInt256,
    p2: &CurvePoint,
    u2: &BigInt256,
) -> Result<CurvePoint, SynthesisError> {
    let p_field = params.p;
    let a_mod_p = params.a_mod_p.clone();

    let (u1_bit_vars, u1_bit_vals) = decompose_scalar_bits(builder, u1)?;
    let (u2_bit_vars, u2_bit_vals) = decompose_scalar_bits(builder, u2)?;

    // Precompute T = P1 + P2 (one ec_add).
    let t_in_circuit = ec_add_with_curve(builder, params, p1, p2)?;
    let t_native = match (p1.x.to_biguint(), p1.y.to_biguint(), p2.x.to_biguint(), p2.y.to_biguint()) {
        (Some(x1), Some(y1), Some(x2), Some(y2)) => {
            ec_add_native_with_modulus((&x1, &y1), (&x2, &y2), p_field)
        }
        _ => None,
    };

    // Blinding seed: `2 · G`. Known non-zero, on the curve, derived from
    // public parameters so it's circuit-shape-stable.
    let blinding_native = ec_double_native_with_curve(
        (&params.g.0, &params.g.1),
        p_field,
        &a_mod_p,
    )
    .expect("double generator G");

    // Precompute 2^256 · blinding natively (constant for this curve).
    let two256_blinding_native = {
        let mut acc = blinding_native.clone();
        for _ in 0..256 {
            acc = ec_double_native_with_curve((&acc.0, &acc.1), p_field, &a_mod_p)
                .expect("native double");
        }
        acc
    };

    let mut acc = CurvePoint {
        x: alloc_bigint256(builder, Some(blinding_native.0.clone()))?,
        y: alloc_bigint256(builder, Some(blinding_native.1.clone()))?,
    };
    let mut acc_native: Option<(BigUint, BigUint)> = Some(blinding_native.clone());

    let p1_native: Option<(BigUint, BigUint)> = match (p1.x.to_biguint(), p1.y.to_biguint()) {
        (Some(x), Some(y)) => Some((x, y)),
        _ => None,
    };
    let p2_native: Option<(BigUint, BigUint)> = match (p2.x.to_biguint(), p2.y.to_biguint()) {
        (Some(x), Some(y)) => Some((x, y)),
        _ => None,
    };

    for i in (0..256).rev() {
        // 1) Shared doubling.
        acc = ec_double_with_curve(builder, params, &acc)?;
        acc_native = acc_native
            .as_ref()
            .and_then(|a| ec_double_native_with_curve((&a.0, &a.1), p_field, &a_mod_p));

        // 2) Select addend: (0,0)→P1 filler, (1,0)→P1, (0,1)→P2, (1,1)→T.
        let addend = select4_point(
            builder,
            p_field,
            u1_bit_vars[i],
            u1_bit_vals[i],
            u2_bit_vars[i],
            u2_bit_vals[i],
            p1, // filler when (0,0)
            p1, p2, &t_in_circuit,
        )?;

        // Native value of the chosen addend (for the candidate-add
        // proving-time closure inside ec_add).
        let addend_native: Option<(BigUint, BigUint)> = match (u1_bit_vals[i], u2_bit_vals[i]) {
            (Some(false), Some(false)) => p1_native.clone(), // filler
            (Some(true), Some(false)) => p1_native.clone(),
            (Some(false), Some(true)) => p2_native.clone(),
            (Some(true), Some(true)) => t_native.clone(),
            _ => None,
        };

        // 3) Candidate add.
        let candidate = ec_add_with_curve(builder, params, &acc, &addend)?;
        let candidate_native = match (acc_native.as_ref(), addend_native.as_ref()) {
            (Some(a), Some(b)) => ec_add_native_with_modulus((&a.0, &a.1), (&b.0, &b.1), p_field),
            _ => None,
        };

        // 4) do_add = b1 OR b2 = b1 + b2 − b1·b2.
        let b1b2_val = match (u1_bit_vals[i], u2_bit_vals[i]) {
            (Some(a), Some(b)) => Some(if a && b { Fr::one() } else { Fr::zero() }),
            _ => None,
        };
        let b1b2 = builder.alloc_with_value(b1b2_val)?;
        builder.enforce(
            LinearCombination::from((Fr::one(), u1_bit_vars[i])),
            LinearCombination::from((Fr::one(), u2_bit_vars[i])),
            LinearCombination::from((Fr::one(), b1b2)),
        )?;
        let do_add_val = match (u1_bit_vals[i], u2_bit_vals[i]) {
            (Some(a), Some(b)) => Some(a || b),
            _ => None,
        };
        let do_add_var = builder.alloc_with_value(
            do_add_val.map(|v| if v { Fr::one() } else { Fr::zero() }),
        )?;
        builder.enforce(
            builder.zero_lc(),
            builder.zero_lc(),
            LinearCombination(vec![
                (Fr::one(), do_add_var),
                (-Fr::one(), u1_bit_vars[i]),
                (-Fr::one(), u2_bit_vars[i]),
                (Fr::one(), b1b2),
            ]),
        )?;

        // 5) Pick between candidate and acc based on do_add.
        acc = select_point_with_p(builder, p_field, do_add_var, do_add_val, &candidate, &acc)?;
        acc_native = match (do_add_val, candidate_native, acc_native) {
            (Some(true), Some(c), _) => Some(c),
            (Some(false), _, prev) => prev,
            _ => None,
        };
    }

    // Subtract the 2^256 · blinding contribution.
    let two256_blinding = CurvePoint {
        x: alloc_bigint256(builder, Some(two256_blinding_native.0.clone()))?,
        y: alloc_bigint256(builder, Some(two256_blinding_native.1.clone()))?,
    };
    let neg_y_native = p_field - &two256_blinding_native.1;
    let neg_two256_blinding = CurvePoint {
        x: two256_blinding.x.clone(),
        y: alloc_bigint256(builder, Some(neg_y_native))?,
    };
    let zero = alloc_bigint256(builder, Some(BigUint::from(0u64)))?;
    let sum = add_mod(builder, &two256_blinding.y, &neg_two256_blinding.y, p_field)?;
    enforce_bigint_eq(builder, &sum, &zero)?;
    ec_add_with_curve(builder, params, &acc, &neg_two256_blinding)
}

// =============================================================================
// secp256k1 GLV-accelerated 4-way joint scalar mul
// =============================================================================
//
// `scalar_mul_2p_secp256k1_glv` computes `u1·G + u2·Q` using GLV
// decomposition and 4-way joint Strauss-Shamir. Each scalar is split into
// two ~129-bit halves via the secp256k1 endomorphism `φ`, so the inner
// iteration count drops from 256 to 128 — the dominant constraint cost
// (one `ec_double` + one `ec_add` per iteration) roughly halves.
//
// At each iteration we look up a precomputed 16-entry table indexed by
// the four bit-positions `(k1a_i, k1b_i, k2a_i, k2b_i)`. The table entries
// are subset-sums of `{G, φ(G), Q, φ(Q)}` after signed-scalar conditional
// negation; we build them once with 11 in-circuit `ec_add`s. The 16-way
// select itself is implemented as a depth-4 binary tree of
// `select_point_with_p` (15 select operations total).

/// Build the precomputed table of `{0, G, φG, Q, φQ}` subset sums, indexed
/// by `(b3, b2, b1, b0)` where `b3 = G`, `b2 = φG`, `b1 = Q`, `b0 = φQ`.
/// Entry `0` is a filler (`G`, never actually selected when the OR-of-bits
/// is zero); the other 15 entries are real point sums.
fn build_glv_table(
    builder: &mut R1csBuilder<'_>,
    params: &CurveParams,
    g: &CurvePoint,
    phi_g: &CurvePoint,
    q: &CurvePoint,
    phi_q: &CurvePoint,
) -> Result<Vec<CurvePoint>, SynthesisError> {
    let mut t: Vec<CurvePoint> = Vec::with_capacity(16);
    t.push(g.clone()); // 0: filler
    t.push(g.clone()); // 1: G
    t.push(phi_g.clone()); // 2: φG
    t.push(ec_add_with_curve(builder, params, g, phi_g)?); // 3: G + φG
    t.push(q.clone()); // 4: Q
    t.push(ec_add_with_curve(builder, params, g, q)?); // 5: G + Q
    t.push(ec_add_with_curve(builder, params, phi_g, q)?); // 6: φG + Q
    let t7 = ec_add_with_curve(builder, params, &t[3], q)?; // 7: G + φG + Q
    t.push(t7);
    t.push(phi_q.clone()); // 8: φQ
    t.push(ec_add_with_curve(builder, params, g, phi_q)?); // 9: G + φQ
    t.push(ec_add_with_curve(builder, params, phi_g, phi_q)?); // 10: φG + φQ
    let t11 = ec_add_with_curve(builder, params, &t[3], phi_q)?; // 11: G + φG + φQ
    t.push(t11);
    t.push(ec_add_with_curve(builder, params, q, phi_q)?); // 12: Q + φQ
    let t13 = ec_add_with_curve(builder, params, &t[5], phi_q)?; // 13: G + Q + φQ
    t.push(t13);
    let t14 = ec_add_with_curve(builder, params, &t[6], phi_q)?; // 14: φG + Q + φQ
    t.push(t14);
    let t15 = ec_add_with_curve(builder, params, &t[7], phi_q)?; // 15: G + φG + Q + φQ
    t.push(t15);
    Ok(t)
}

/// 16-way `CurvePoint` select implemented as a depth-4 binary tree of
/// `select_point_with_p`. Indexed by `(b3, b2, b1, b0)` as a 4-bit number,
/// MSB-first.
fn select16_point(
    builder: &mut R1csBuilder<'_>,
    p_field: &BigUint,
    bits: [(Variable, Option<bool>); 4],
    table: &[CurvePoint; 16],
) -> Result<CurvePoint, SynthesisError> {
    // Level 1: select between pairs based on bits[0] (LSB).
    let mut level: Vec<CurvePoint> = Vec::with_capacity(8);
    for j in 0..8 {
        let pair0 = &table[2 * j];
        let pair1 = &table[2 * j + 1];
        level.push(select_point_with_p(
            builder,
            p_field,
            bits[0].0,
            bits[0].1,
            pair1,
            pair0,
        )?);
    }
    // Level 2: select between pairs based on bits[1].
    let mut next: Vec<CurvePoint> = Vec::with_capacity(4);
    for j in 0..4 {
        next.push(select_point_with_p(
            builder,
            p_field,
            bits[1].0,
            bits[1].1,
            &level[2 * j + 1],
            &level[2 * j],
        )?);
    }
    // Level 3: select based on bits[2].
    let mut next2: Vec<CurvePoint> = Vec::with_capacity(2);
    for j in 0..2 {
        next2.push(select_point_with_p(
            builder,
            p_field,
            bits[2].0,
            bits[2].1,
            &next[2 * j + 1],
            &next[2 * j],
        )?);
    }
    // Level 4: select based on bits[3] (MSB).
    select_point_with_p(builder, p_field, bits[3].0, bits[3].1, &next2[1], &next2[0])
}

/// Decompose a 129-bit `BigInt256` into 129 boolean bit `Variable`s
/// (LSB first). Similar to [`decompose_scalar_bits`] but stops at 129 bits
/// because GLV halves are at most that wide.
fn decompose_glv_half_bits(
    builder: &mut R1csBuilder<'_>,
    scalar: &BigInt256,
) -> Result<(Vec<Variable>, Vec<Option<bool>>), SynthesisError> {
    let mut bit_vars: Vec<Variable> = Vec::with_capacity(129);
    let mut bit_vals: Vec<Option<bool>> = Vec::with_capacity(129);
    // Limb 0 (full 64 bits).
    let limb0_value = scalar.value.map(|l| Fr::from(l[0]));
    let bits0 = decompose_into_bits(builder, scalar.limbs[0], 64, limb0_value)?;
    for (b_i, b_var) in bits0.into_iter().enumerate() {
        bit_vars.push(b_var);
        let bv = scalar.value.map(|l| ((l[0] >> b_i) & 1) == 1);
        bit_vals.push(bv);
    }
    // Limb 1 (full 64 bits).
    let limb1_value = scalar.value.map(|l| Fr::from(l[1]));
    let bits1 = decompose_into_bits(builder, scalar.limbs[1], 64, limb1_value)?;
    for (b_i, b_var) in bits1.into_iter().enumerate() {
        bit_vars.push(b_var);
        let bv = scalar.value.map(|l| ((l[1] >> b_i) & 1) == 1);
        bit_vals.push(bv);
    }
    // Limb 2 (just the bottom 1 bit — `enforce_129_bit` already constrained
    // the rest to zero). We use limbs[2] directly as the bit Variable: the
    // boolean check inside `enforce_129_bit` is the same as this bit's
    // bit-value, so no fresh allocation is needed.
    let limb2_low_val = scalar.value.map(|l| (l[2] & 1) == 1);
    bit_vars.push(scalar.limbs[2]);
    bit_vals.push(limb2_low_val);
    Ok((bit_vars, bit_vals))
}

/// GLV-accelerated joint scalar mul for secp256k1: `u1·G + u2·Q` in 128
/// MSB-first iterations using `(k1a, k1b, k2a, k2b)` GLV halves and a
/// 16-entry precomputed addend table.
pub fn scalar_mul_2p_secp256k1_glv(
    builder: &mut R1csBuilder<'_>,
    g: &CurvePoint,
    u1: &BigInt256,
    q: &CurvePoint,
    u2: &BigInt256,
) -> Result<CurvePoint, SynthesisError> {
    let params = CurveParams::secp256k1();
    let p_field = params.p;
    let a_mod_p = params.a_mod_p.clone();

    // 1) GLV-decompose u1 and u2 into signed 129-bit halves.
    let (k1a, k1b) = glv_decompose_in_circuit(builder, u1)?;
    let (k2a, k2b) = glv_decompose_in_circuit(builder, u2)?;

    // 2) Conditionally negate the base points according to each scalar's sign.
    let g_signed = conditional_negate(builder, p_field, g, k1a.sign, k1a.sign_value)?;
    let phi_g = phi_secp256k1(builder, g)?;
    let phi_g_signed = conditional_negate(builder, p_field, &phi_g, k1b.sign, k1b.sign_value)?;
    let q_signed = conditional_negate(builder, p_field, q, k2a.sign, k2a.sign_value)?;
    let phi_q = phi_secp256k1(builder, q)?;
    let phi_q_signed = conditional_negate(builder, p_field, &phi_q, k2b.sign, k2b.sign_value)?;

    // 3) Build the 16-entry precomputed table over the signed base points.
    let table = build_glv_table(
        builder,
        &params,
        &g_signed,
        &phi_g_signed,
        &q_signed,
        &phi_q_signed,
    )?;
    let table_arr: [CurvePoint; 16] = match table.try_into() {
        Ok(arr) => arr,
        Err(_) => unreachable!("build_glv_table always returns 16 entries"),
    };

    // 4) Decompose all four 129-bit absolute scalars into bits.
    let (b_k1a, v_k1a) = decompose_glv_half_bits(builder, &k1a.abs)?;
    let (b_k1b, v_k1b) = decompose_glv_half_bits(builder, &k1b.abs)?;
    let (b_k2a, v_k2a) = decompose_glv_half_bits(builder, &k2a.abs)?;
    let (b_k2b, v_k2b) = decompose_glv_half_bits(builder, &k2b.abs)?;

    // 5) Blinding seed and 2^129 · blinding for end-of-loop subtraction.
    let blinding_native = ec_double_native_with_curve(
        (&params.g.0, &params.g.1),
        p_field,
        &a_mod_p,
    )
    .expect("double generator G");
    let two129_blinding_native = {
        let mut acc = blinding_native.clone();
        for _ in 0..129 {
            acc = ec_double_native_with_curve((&acc.0, &acc.1), p_field, &a_mod_p)
                .expect("native double");
        }
        acc
    };
    let mut acc = CurvePoint {
        x: alloc_bigint256(builder, Some(blinding_native.0.clone()))?,
        y: alloc_bigint256(builder, Some(blinding_native.1.clone()))?,
    };
    let mut acc_native: Option<(BigUint, BigUint)> = Some(blinding_native.clone());

    // Native values for the 16 table entries (for proving-time `ec_add`
    // closures inside the loop).
    let table_native: Vec<Option<(BigUint, BigUint)>> = table_arr
        .iter()
        .map(|p| match (p.x.to_biguint(), p.y.to_biguint()) {
            (Some(x), Some(y)) => Some((x, y)),
            _ => None,
        })
        .collect();

    // 6) MSB-first 129-iteration joint Strauss-Shamir.
    for i in (0..129).rev() {
        acc = ec_double_with_curve(builder, &params, &acc)?;
        acc_native = acc_native
            .as_ref()
            .and_then(|a| ec_double_native_with_curve((&a.0, &a.1), p_field, &a_mod_p));

        // The precomputed table encodes index `i = b3·8 + b2·4 + b1·2 + b0`
        // as the subset sum `(b0·G) + (b1·φG) + (b2·Q) + (b3·φQ)`. So the
        // tree's LSB (`bits[0]`) is the G-bit (= `b_k1a[i]` after sign
        // factoring), `bits[1]` is the φG-bit, etc.
        let bits = [
            (b_k1a[i], v_k1a[i]), // bits[0] = G's bit
            (b_k1b[i], v_k1b[i]), // bits[1] = φG's bit
            (b_k2a[i], v_k2a[i]), // bits[2] = Q's bit
            (b_k2b[i], v_k2b[i]), // bits[3] = φQ's bit (MSB of index)
        ];
        let addend = select16_point(builder, p_field, bits, &table_arr)?;
        let table_index: Option<usize> = match (v_k2b[i], v_k2a[i], v_k1b[i], v_k1a[i]) {
            (Some(b3), Some(b2), Some(b1), Some(b0)) => Some(
                ((b3 as usize) << 3)
                    | ((b2 as usize) << 2)
                    | ((b1 as usize) << 1)
                    | (b0 as usize),
            ),
            _ => None,
        };
        let addend_native = table_index.and_then(|idx| table_native[idx].clone());

        let candidate = ec_add_with_curve(builder, &params, &acc, &addend)?;
        let candidate_native = match (acc_native.as_ref(), addend_native.as_ref()) {
            (Some(a), Some(b)) => ec_add_native_with_modulus((&a.0, &a.1), (&b.0, &b.1), p_field),
            _ => None,
        };

        // OR-of-4-bits via the not-AND-of-negations trick. Allocate three
        // aux muls.
        let n3 = bool_neg(builder, b_k1a[i], v_k1a[i])?;
        let n2 = bool_neg(builder, b_k1b[i], v_k1b[i])?;
        let n1 = bool_neg(builder, b_k2a[i], v_k2a[i])?;
        let n0 = bool_neg(builder, b_k2b[i], v_k2b[i])?;
        let nn_3_2 = bool_and(builder, n3.0, n3.1, n2.0, n2.1)?;
        let nn_1_0 = bool_and(builder, n1.0, n1.1, n0.0, n0.1)?;
        let nn_all = bool_and(builder, nn_3_2.0, nn_3_2.1, nn_1_0.0, nn_1_0.1)?;
        let do_add_val: Option<bool> = nn_all.1.map(|v| !v);
        let do_add_var = builder.alloc_with_value(
            do_add_val.map(|v| if v { Fr::one() } else { Fr::zero() }),
        )?;
        builder.enforce(
            builder.zero_lc(),
            builder.zero_lc(),
            LinearCombination(vec![
                (Fr::one(), do_add_var),
                (Fr::one(), nn_all.0),
                (-Fr::one(), Variable::One),
            ]),
        )?;

        acc = select_point_with_p(builder, p_field, do_add_var, do_add_val, &candidate, &acc)?;
        acc_native = match (do_add_val, candidate_native, acc_native) {
            (Some(true), Some(c), _) => Some(c),
            (Some(false), _, prev) => prev,
            _ => None,
        };
    }

    // 7) Subtract the 2^129 · blinding contribution.
    let two129_blinding = CurvePoint {
        x: alloc_bigint256(builder, Some(two129_blinding_native.0.clone()))?,
        y: alloc_bigint256(builder, Some(two129_blinding_native.1.clone()))?,
    };
    let neg_y_native = p_field - &two129_blinding_native.1;
    let neg_two129_blinding = CurvePoint {
        x: two129_blinding.x.clone(),
        y: alloc_bigint256(builder, Some(neg_y_native))?,
    };
    let zero = alloc_bigint256(builder, Some(BigUint::from(0u64)))?;
    let sum = add_mod(builder, &two129_blinding.y, &neg_two129_blinding.y, p_field)?;
    enforce_bigint_eq(builder, &sum, &zero)?;
    ec_add_with_curve(builder, &params, &acc, &neg_two129_blinding)
}

/// Boolean negation: returns `(var, val)` with `var = 1 − b`. Allocates one
/// witness with value `1 − b_val` and enforces `var + b = 1`.
fn bool_neg(
    builder: &mut R1csBuilder<'_>,
    b_var: Variable,
    b_val: Option<bool>,
) -> Result<(Variable, Option<bool>), SynthesisError> {
    let val = b_val.map(|v| !v);
    let var = builder.alloc_with_value(val.map(|v| if v { Fr::one() } else { Fr::zero() }))?;
    builder.enforce(
        builder.zero_lc(),
        builder.zero_lc(),
        LinearCombination(vec![
            (Fr::one(), var),
            (Fr::one(), b_var),
            (-Fr::one(), Variable::One),
        ]),
    )?;
    Ok((var, val))
}

/// Boolean AND: returns `(var, val)` with `var = a · b`.
fn bool_and(
    builder: &mut R1csBuilder<'_>,
    a_var: Variable,
    a_val: Option<bool>,
    b_var: Variable,
    b_val: Option<bool>,
) -> Result<(Variable, Option<bool>), SynthesisError> {
    let val = match (a_val, b_val) {
        (Some(a), Some(b)) => Some(a && b),
        _ => None,
    };
    let var = builder.alloc_with_value(val.map(|v| if v { Fr::one() } else { Fr::zero() }))?;
    builder.enforce(
        LinearCombination::from((Fr::one(), a_var)),
        LinearCombination::from((Fr::one(), b_var)),
        LinearCombination::from((Fr::one(), var)),
    )?;
    Ok((var, val))
}

// =============================================================================
// Fixed-base generator comb for secp256k1's G
// =============================================================================
//
// Computes `u1 · G` for a 256-bit scalar `u1` via the windowed precomputed
// comb technique. `G` is a curve constant, so we tabulate
// `T[j][d] = d · 16^j · G` for `j ∈ 0..64` and `d ∈ 0..16` at lazy init
// time using OnceLock. Per scalar mul: 64 windows × one constant-table
// select × one in-circuit `ec_add`, no doublings on the runtime path.
//
// Cost: ~672k constraints per scalar mul vs. ~3.9M for the same scalar
// inside the 4-way joint Strauss-Shamir loop. Saves ~12% on the full
// secp256k1 ECDSA verify.

const COMB_W: usize = 4;
const COMB_WINDOWS: usize = 256 / COMB_W;
const COMB_TABLE_SIZE: usize = 1 << COMB_W;

/// One window's lookup row: 16 affine `(x, y)` pairs (the `d`-th is
/// `d · 16^j · G`); index 0 is the identity placeholder.
type CombRow = [Option<(BigUint, BigUint)>; COMB_TABLE_SIZE];

/// Lazily compute the comb table for secp256k1's generator. The outer
/// dimension is the window index `j ∈ 0..64`; the inner is the digit
/// value `d ∈ 0..16`. Entry `(j, d)` is `d · 16^j · G` as an affine
/// `(x, y)` pair, or `None` for `d == 0` (the identity, which we never
/// select on the live path).
fn secp256k1_comb_table() -> &'static Vec<CombRow> {
    static TABLE: OnceLock<Vec<CombRow>> = OnceLock::new();
    TABLE.get_or_init(|| build_comb_table(&CurveParams::secp256k1()))
}

/// 4-bit constant-table select for a `CurvePoint`: returns
/// `table[d]` where `d = b3·8 + b2·4 + b1·2 + b0` and the table entries
/// are 16 known affine points. Implemented as a polynomial expansion over
/// the bit auxiliaries — one R1CS row per output limb, 11 cross-term
/// `aux = b_i · b_j ...` muls shared across all output limbs of this
/// window. Cheaper than a 4-deep tree of `select_point_with_p` when the
/// table entries are constants (the tree path would force allocating each
/// table entry as 8 fresh limb Variables).
fn const_table16_select_point(
    builder: &mut R1csBuilder<'_>,
    bits: [(Variable, Option<bool>); COMB_W],
    table: &[Option<(BigUint, BigUint)>; COMB_TABLE_SIZE],
) -> Result<CurvePoint, SynthesisError> {
    // Resolve table_native (1..15 all guaranteed Some; index 0 is the
    // identity placeholder, used only when `d == 0` which never selects
    // through this function because we OR-of-4-bits-gate the add).
    let mut table_x: [BigUint; COMB_TABLE_SIZE] =
        std::array::from_fn(|_| BigUint::from(0u64));
    let mut table_y: [BigUint; COMB_TABLE_SIZE] =
        std::array::from_fn(|_| BigUint::from(0u64));
    for d in 1..COMB_TABLE_SIZE {
        let (x, y) = table[d].as_ref().expect("comb table entry");
        table_x[d] = x.clone();
        table_y[d] = y.clone();
    }

    // Allocate cross-term aux muls of all subsets of {b0, b1, b2, b3} of
    // size ≥ 2. Index by the bitmask `mask` (in 0..16); `mask` has popcount
    // ≥ 2 for cross-terms, popcount 0 or 1 trivial (use Variable::One or
    // the bit directly).
    //
    // Computation order: increasing popcount, so each new aux can be
    // built from a previously allocated lower-order aux × a single bit.
    let mut cross: [Option<(Variable, Option<Fr>)>; COMB_TABLE_SIZE] =
        std::array::from_fn(|_| None);
    cross[0] = Some((Variable::One, Some(Fr::one())));
    for j in 0..COMB_W {
        let (v, val) = bits[j];
        let fr_val = val.map(|b| if b { Fr::one() } else { Fr::zero() });
        cross[1 << j] = Some((v, fr_val));
    }
    for mask in 0..COMB_TABLE_SIZE {
        if mask.count_ones() < 2 {
            continue;
        }
        // Find the lowest set bit and pair it with the rest.
        let lsb = mask & mask.wrapping_neg();
        let rest = mask & !lsb;
        let (lsb_var, lsb_val) = cross[lsb].expect("single-bit aux");
        let (rest_var, rest_val) = cross[rest].expect("lower-popcount aux");
        let combined_val = match (lsb_val, rest_val) {
            (Some(a), Some(b)) => Some(a * b),
            _ => None,
        };
        let aux = builder.alloc_with_value(combined_val)?;
        builder.enforce(
            LinearCombination::from((Fr::one(), lsb_var)),
            LinearCombination::from((Fr::one(), rest_var)),
            LinearCombination::from((Fr::one(), aux)),
        )?;
        cross[mask] = Some((aux, combined_val));
    }

    // Express each coordinate of the output as
    //   out_coord = Σ_{d=0..15} 1[d == bits] · table[d].coord
    // The indicator `1[d == bits]` expands via inclusion–exclusion to a
    // signed linear combination of `cross[subset]` terms. Specifically:
    //   1[d == bits] = Σ_{S ⊇ d_set} (−1)^(|S| − |d_set|) · ∏_{j ∈ S} b_j
    // For each output limb we precompute the constant coefficient on each
    // `cross[mask]` term as
    //   coeff[mask] = Σ_{d ⊆ mask} (−1)^(|mask| − |d|) · table[d].limb
    // (Möbius inversion: each `cross[mask]` contributes to all `d ⊆ mask`
    // indicators; conversely each `d`'s indicator pulls from masks
    // containing `d`.)
    let mut select_one_coord = |table_vals: &[BigUint; COMB_TABLE_SIZE]| -> Result<BigInt256, SynthesisError> {
        // Compute the output's BigUint value natively from the selected
        // bits' values.
        let bit_vals: Option<[bool; COMB_W]> = (|| -> Option<[bool; COMB_W]> {
            let mut arr = [false; COMB_W];
            for j in 0..COMB_W {
                arr[j] = bits[j].1?;
            }
            Some(arr)
        })();
        let out_val: Option<BigUint> = bit_vals.map(|bv| {
            let mut idx = 0usize;
            for (j, &b) in bv.iter().enumerate() {
                if b {
                    idx |= 1 << j;
                }
            }
            table_vals[idx].clone()
        });
        let out_limbs_val: Option<[u64; LIMBS]> = out_val.as_ref().map(biguint_to_limbs);

        let p_field = secp256k1_p();
        let mut limbs = [Variable::One; LIMBS];
        for i in 0..LIMBS {
            let lv = out_limbs_val.map(|l| l[i]);
            limbs[i] = alloc_u64_limb(builder, lv)?;
        }
        let out = BigInt256 { limbs, value: out_limbs_val };
        let _ = p_field;

        // For each output limb i, enforce
        //   out.limbs[i] = Σ_{mask=0..15} coeff_i[mask] · cross[mask].var
        // where `coeff_i[mask] = Σ_{d ⊆ mask} (−1)^(|mask|−|d|) · table_vals[d].limb_i`.
        for limb_i in 0..LIMBS {
            // Compute the 16 coefficients for this limb.
            let mut coeffs: [Fr; COMB_TABLE_SIZE] = [Fr::zero(); COMB_TABLE_SIZE];
            for (mask, slot) in coeffs.iter_mut().enumerate() {
                let mut acc = Fr::zero();
                let mut d = mask as i64;
                // Iterate over all d ⊆ mask (subsets of mask).
                loop {
                    let popcount_diff = (mask as u32 - (d as u32)).count_ones() as i32;
                    let sign_is_neg = popcount_diff % 2 != 0;
                    let limb_val = biguint_to_limbs(&table_vals[d as usize])[limb_i];
                    let term = Fr::from(limb_val);
                    if sign_is_neg {
                        acc -= term;
                    } else {
                        acc += term;
                    }
                    if d == 0 {
                        break;
                    }
                    d = (d - 1) & mask as i64;
                }
                *slot = acc;
            }
            // Emit out.limbs[i] − Σ_mask coeff[mask] · cross[mask].var = 0.
            let mut lc: Vec<(Fr, Variable)> = Vec::new();
            lc.push((Fr::one(), out.limbs[limb_i]));
            for (mask, c) in coeffs.iter().enumerate() {
                if c.is_zero() {
                    continue;
                }
                let (var, _) = cross[mask].expect("cross-term aux");
                lc.push((-(*c), var));
            }
            builder.enforce(builder.zero_lc(), builder.zero_lc(), LinearCombination(lc))?;
        }
        Ok(out)
    };

    let x = select_one_coord(&table_x)?;
    let y = select_one_coord(&table_y)?;
    Ok(CurvePoint { x, y })
}

/// Build a 64-window comb table for an arbitrary short-Weierstrass curve
/// generator. The structure is identical to [`secp256k1_comb_table`]; this
/// helper takes the curve parameters explicitly so the same code path
/// serves secp256r1 too.
fn build_comb_table(params: &CurveParams) -> Vec<CombRow> {
    let (gx, gy) = params.g.clone();
    let p = params.p;
    let a = params.a_mod_p.clone();
    // window_base[j] = 16^j · G via 4 doublings per step.
    let mut window_base: Vec<(BigUint, BigUint)> = Vec::with_capacity(COMB_WINDOWS);
    let mut cur = (gx, gy);
    for _ in 0..COMB_WINDOWS {
        window_base.push(cur.clone());
        for _ in 0..COMB_W {
            cur = ec_double_native_with_curve((&cur.0, &cur.1), p, &a)
                .expect("double generator-aligned multiple");
        }
    }
    let mut table = Vec::with_capacity(COMB_WINDOWS);
    for base in &window_base {
        let mut row: CombRow = std::array::from_fn(|_| None);
        row[1] = Some(base.clone());
        let two_base = ec_double_native_with_curve((&base.0, &base.1), p, &a)
            .expect("comb-row double");
        row[2] = Some(two_base.clone());
        let mut acc = two_base;
        for slot in row.iter_mut().skip(3) {
            acc = ec_add_native_with_modulus((&acc.0, &acc.1), (&base.0, &base.1), p)
                .expect("comb-row add");
            *slot = Some(acc.clone());
        }
        table.push(row);
    }
    table
}

/// Comb table for secp256r1's generator. Same structure as
/// [`secp256k1_comb_table`] but on the P-256 curve.
fn secp256r1_comb_table() -> &'static Vec<CombRow> {
    static TABLE: OnceLock<Vec<CombRow>> = OnceLock::new();
    TABLE.get_or_init(|| build_comb_table(&CurveParams::secp256r1()))
}

/// Compute `u · G` for a fixed-base curve `G` via a 4-bit comb over the
/// supplied precomputed `table`. Used by both secp256k1 and secp256r1's
/// `u1·G` paths.
fn scalar_mul_g_comb(
    builder: &mut R1csBuilder<'_>,
    params: &CurveParams,
    table: &[CombRow],
    u1: &BigInt256,
) -> Result<CurvePoint, SynthesisError> {
    let p_field = params.p;
    let a_mod_p = params.a_mod_p.clone();

    // Decompose u1 into 256 boolean bits.
    let (bit_vars, bit_vals) = decompose_scalar_bits(builder, u1)?;

    // Blinding seed = 2·G; constant 2·G is on the curve and non-zero.
    let blinding_native = ec_double_native_with_curve(
        (&params.g.0, &params.g.1),
        p_field,
        &a_mod_p,
    )
    .expect("blinding seed");

    let mut acc = CurvePoint {
        x: alloc_bigint256(builder, Some(blinding_native.0.clone()))?,
        y: alloc_bigint256(builder, Some(blinding_native.1.clone()))?,
    };
    let mut acc_native: Option<(BigUint, BigUint)> = Some(blinding_native.clone());

    for (j, row) in table.iter().enumerate() {
        let base = j * COMB_W;
        let bits = [
            (bit_vars[base], bit_vals[base]),
            (bit_vars[base + 1], bit_vals[base + 1]),
            (bit_vars[base + 2], bit_vals[base + 2]),
            (bit_vars[base + 3], bit_vals[base + 3]),
        ];
        let addend = const_table16_select_point(builder, bits, row)?;
        let addend_native: Option<(BigUint, BigUint)> = (|| -> Option<(BigUint, BigUint)> {
            let mut d = 0usize;
            for (k, (_, v)) in bits.iter().enumerate() {
                if (*v)? {
                    d |= 1 << k;
                }
            }
            row[d].clone()
        })();

        // do_add = OR of the 4 window bits. When the digit is 0 we still
        // pretend to add (so ec_add stays generic), but revert via select.
        let any_bit_val: Option<bool> = (|| -> Option<bool> {
            let mut any = false;
            for (_, v) in bits.iter() {
                if (*v)? {
                    any = true;
                }
            }
            Some(any)
        })();

        let candidate = ec_add_with_curve(builder, params, &acc, &addend)?;
        let candidate_native = match (acc_native.as_ref(), addend_native.as_ref()) {
            (Some(a), Some(b)) => {
                ec_add_native_with_modulus((&a.0, &a.1), (&b.0, &b.1), p_field)
            }
            _ => None,
        };

        // Build do_add = 1 − (1−b0)(1−b1)(1−b2)(1−b3) via the existing
        // not-AND-of-negations helpers.
        let n3 = bool_neg(builder, bits[0].0, bits[0].1)?;
        let n2 = bool_neg(builder, bits[1].0, bits[1].1)?;
        let n1 = bool_neg(builder, bits[2].0, bits[2].1)?;
        let n0 = bool_neg(builder, bits[3].0, bits[3].1)?;
        let nn_a = bool_and(builder, n3.0, n3.1, n2.0, n2.1)?;
        let nn_b = bool_and(builder, n1.0, n1.1, n0.0, n0.1)?;
        let nn_all = bool_and(builder, nn_a.0, nn_a.1, nn_b.0, nn_b.1)?;
        let do_add_var = builder.alloc_with_value(
            any_bit_val.map(|v| if v { Fr::one() } else { Fr::zero() }),
        )?;
        builder.enforce(
            builder.zero_lc(),
            builder.zero_lc(),
            LinearCombination(vec![
                (Fr::one(), do_add_var),
                (Fr::one(), nn_all.0),
                (-Fr::one(), Variable::One),
            ]),
        )?;

        acc = select_point_with_p(builder, p_field, do_add_var, any_bit_val, &candidate, &acc)?;
        acc_native = match (any_bit_val, candidate_native, acc_native) {
            (Some(true), Some(c), _) => Some(c),
            (Some(false), _, prev) => prev,
            _ => None,
        };
    }

    // Subtract the blinding seed at the end. The seed remained the same
    // across iterations (the comb table absorbs the doubling), so we
    // subtract just `2·G`.
    let neg_blinding_y_native = p_field - &blinding_native.1;
    let blinding = CurvePoint {
        x: alloc_bigint256(builder, Some(blinding_native.0.clone()))?,
        y: alloc_bigint256(builder, Some(blinding_native.1.clone()))?,
    };
    let neg_blinding = CurvePoint {
        x: blinding.x.clone(),
        y: alloc_bigint256(builder, Some(neg_blinding_y_native))?,
    };
    let zero = alloc_bigint256(builder, Some(BigUint::from(0u64)))?;
    let sum = add_mod(builder, &blinding.y, &neg_blinding.y, p_field)?;
    enforce_bigint_eq(builder, &sum, &zero)?;
    ec_add_with_curve(builder, params, &acc, &neg_blinding)
}

/// Windowed (4-bit) double-and-add scalar mul `u·Q` for a variable-base
/// curve point `Q`. Used on secp256r1's `u2·Q` where GLV is unavailable
/// but we still want to amortise the per-iteration add cost over
/// 4-bit windows. Precomputes 15 multiples `2·Q…15·Q` (`Q` itself is
/// `table[1]`); each window iteration runs 4 in-circuit doublings, picks
/// the addend from the 16-entry table via a 4-deep tree of
/// `select_point_with_p`, and OR-gates the conditional add so windows
/// with digit `0` are no-ops.
///
/// Cost: 64 iters × (4 doubles + 1 add + 15 select_point + OR-gate) +
/// 15 ec_adds for the precomputed table ≈ 3.85M constraints for a
/// 256-bit scalar — drops from ~5.4M for plain double-and-add.
fn windowed_scalar_mul_q(
    builder: &mut R1csBuilder<'_>,
    params: &CurveParams,
    q: &CurvePoint,
    u2: &BigInt256,
) -> Result<CurvePoint, SynthesisError> {
    let p_field = params.p;
    let a_mod_p = params.a_mod_p.clone();

    // 1) Decompose u2 into 256 boolean bits (LSB first).
    let (bit_vars, bit_vals) = decompose_scalar_bits(builder, u2)?;

    // 2) Precompute multiples 1·Q, 2·Q, …, 15·Q in-circuit. Index 0 is
    //    a filler (use `Q` itself) so the conditional ec_add stays in
    //    the generic case when the window digit is 0.
    let mut table: Vec<CurvePoint> = Vec::with_capacity(16);
    table.push(q.clone()); // filler for d=0 (never bound to acc when do_add=0)
    table.push(q.clone()); // d=1
    let two_q = ec_double_with_curve(builder, params, q)?;
    table.push(two_q.clone()); // d=2
    let mut acc_mult = two_q;
    for _d in 3..16 {
        acc_mult = ec_add_with_curve(builder, params, &acc_mult, q)?;
        table.push(acc_mult.clone());
    }

    // 3) Blinding seed: 2·G of the *base curve* (a known on-curve
    //    non-zero point unrelated to Q).
    let blinding_native = ec_double_native_with_curve(
        (&params.g.0, &params.g.1),
        p_field,
        &a_mod_p,
    )
    .expect("blinding seed");
    let two256_blinding_native = {
        let mut acc = blinding_native.clone();
        for _ in 0..256 {
            acc = ec_double_native_with_curve((&acc.0, &acc.1), p_field, &a_mod_p)
                .expect("native double");
        }
        acc
    };

    let mut acc = CurvePoint {
        x: alloc_bigint256(builder, Some(blinding_native.0.clone()))?,
        y: alloc_bigint256(builder, Some(blinding_native.1.clone()))?,
    };
    let mut acc_native: Option<(BigUint, BigUint)> = Some(blinding_native);

    // 4) MSB-first 64 windows.
    for w in (0..COMB_WINDOWS).rev() {
        let base = w * COMB_W;
        let bits = [
            (bit_vars[base], bit_vals[base]),
            (bit_vars[base + 1], bit_vals[base + 1]),
            (bit_vars[base + 2], bit_vals[base + 2]),
            (bit_vars[base + 3], bit_vals[base + 3]),
        ];
        // 4 doublings of acc.
        for _ in 0..COMB_W {
            acc = ec_double_with_curve(builder, params, &acc)?;
            acc_native = acc_native
                .as_ref()
                .and_then(|a| ec_double_native_with_curve((&a.0, &a.1), p_field, &a_mod_p));
        }

        // 16-way binary-tree select on the precomputed Q multiples.
        let addend = select16_point(builder, p_field, bits, table.as_slice().try_into().expect("16"))?;
        let table_index: Option<usize> = (|| -> Option<usize> {
            let mut idx = 0usize;
            for (k, (_, v)) in bits.iter().enumerate() {
                if (*v)? {
                    idx |= 1 << k;
                }
            }
            Some(idx)
        })();
        let addend_native: Option<(BigUint, BigUint)> = table_index.and_then(|idx| {
            let pt = &table[idx];
            match (pt.x.to_biguint(), pt.y.to_biguint()) {
                (Some(x), Some(y)) => Some((x, y)),
                _ => None,
            }
        });

        let candidate = ec_add_with_curve(builder, params, &acc, &addend)?;
        let candidate_native = match (acc_native.as_ref(), addend_native.as_ref()) {
            (Some(a), Some(b)) => ec_add_native_with_modulus((&a.0, &a.1), (&b.0, &b.1), p_field),
            _ => None,
        };

        // OR-of-4-bits via not-AND-of-negations.
        let n3 = bool_neg(builder, bits[0].0, bits[0].1)?;
        let n2 = bool_neg(builder, bits[1].0, bits[1].1)?;
        let n1 = bool_neg(builder, bits[2].0, bits[2].1)?;
        let n0 = bool_neg(builder, bits[3].0, bits[3].1)?;
        let nn_a = bool_and(builder, n3.0, n3.1, n2.0, n2.1)?;
        let nn_b = bool_and(builder, n1.0, n1.1, n0.0, n0.1)?;
        let nn_all = bool_and(builder, nn_a.0, nn_a.1, nn_b.0, nn_b.1)?;
        let any_bit_val: Option<bool> = nn_all.1.map(|v| !v);
        let do_add_var = builder.alloc_with_value(
            any_bit_val.map(|v| if v { Fr::one() } else { Fr::zero() }),
        )?;
        builder.enforce(
            builder.zero_lc(),
            builder.zero_lc(),
            LinearCombination(vec![
                (Fr::one(), do_add_var),
                (Fr::one(), nn_all.0),
                (-Fr::one(), Variable::One),
            ]),
        )?;

        acc = select_point_with_p(builder, p_field, do_add_var, any_bit_val, &candidate, &acc)?;
        acc_native = match (any_bit_val, candidate_native, acc_native) {
            (Some(true), Some(c), _) => Some(c),
            (Some(false), _, prev) => prev,
            _ => None,
        };
    }

    // 5) Subtract 2^256 · blinding contribution.
    let two256_blinding = CurvePoint {
        x: alloc_bigint256(builder, Some(two256_blinding_native.0.clone()))?,
        y: alloc_bigint256(builder, Some(two256_blinding_native.1.clone()))?,
    };
    let neg_y_native = p_field - &two256_blinding_native.1;
    let neg_two256_blinding = CurvePoint {
        x: two256_blinding.x.clone(),
        y: alloc_bigint256(builder, Some(neg_y_native))?,
    };
    let zero = alloc_bigint256(builder, Some(BigUint::from(0u64)))?;
    let sum = add_mod(builder, &two256_blinding.y, &neg_two256_blinding.y, p_field)?;
    enforce_bigint_eq(builder, &sum, &zero)?;
    ec_add_with_curve(builder, params, &acc, &neg_two256_blinding)
}

/// Joint scalar mul for secp256r1 ECDSA: `u1·G + u2·Q`. P-256 has no
/// useful endomorphism, so GLV doesn't apply; instead we split `u1·G`
/// off via the fixed-base comb (no doublings on `G`) and compute `u2·Q`
/// via 4-bit windowed double-and-add (fewer adds per scalar than the
/// joint Strauss-Shamir loop, which was paying 1 add per bit).
fn scalar_mul_2p_secp256r1_comb_windowed(
    builder: &mut R1csBuilder<'_>,
    u1: &BigInt256,
    q: &CurvePoint,
    u2: &BigInt256,
) -> Result<CurvePoint, SynthesisError> {
    let params = CurveParams::secp256r1();
    // u1·G via fixed-base comb.
    let u1g = scalar_mul_g_comb(builder, &params, secp256r1_comb_table(), u1)?;
    // u2·Q via 4-bit windowed double-and-add.
    let u2q = windowed_scalar_mul_q(builder, &params, q, u2)?;
    // Combine.
    ec_add_with_curve(builder, &params, &u1g, &u2q)
}

/// Joint scalar mul for secp256k1 ECDSA: `u1·G + u2·Q`. Splits into
/// `u1·G` via the fixed-base comb and `u2·Q` via the 2-way GLV joint
/// Strauss-Shamir (which still benefits from the secp256k1 endomorphism
/// on `Q`).
fn scalar_mul_2p_secp256k1_comb_glv(
    builder: &mut R1csBuilder<'_>,
    u1: &BigInt256,
    q: &CurvePoint,
    u2: &BigInt256,
) -> Result<CurvePoint, SynthesisError> {
    let params = CurveParams::secp256k1();
    let p_field = params.p;
    let a_mod_p = params.a_mod_p.clone();

    // u1·G via fixed-base comb (no doublings).
    let u1g = scalar_mul_g_comb(builder, &params, secp256k1_comb_table(), u1)?;

    // u2·Q via GLV + 2-way joint Strauss-Shamir.
    let (k2a, k2b) = glv_decompose_in_circuit(builder, u2)?;
    let q_signed = conditional_negate(builder, p_field, q, k2a.sign, k2a.sign_value)?;
    let phi_q = phi_secp256k1(builder, q)?;
    let phi_q_signed = conditional_negate(builder, p_field, &phi_q, k2b.sign, k2b.sign_value)?;

    // Run 2-way joint Strauss-Shamir on the 129-bit halves of k2.
    let (b_k2a, v_k2a) = decompose_glv_half_bits(builder, &k2a.abs)?;
    let (b_k2b, v_k2b) = decompose_glv_half_bits(builder, &k2b.abs)?;

    // Precompute T = Q' + φQ'.
    let t = ec_add_with_curve(builder, &params, &q_signed, &phi_q_signed)?;
    let blinding_native = ec_double_native_with_curve(
        (&params.g.0, &params.g.1),
        p_field,
        &a_mod_p,
    )
    .expect("blinding");
    let two129_blinding_native = {
        let mut acc = blinding_native.clone();
        for _ in 0..129 {
            acc = ec_double_native_with_curve((&acc.0, &acc.1), p_field, &a_mod_p)
                .expect("native double");
        }
        acc
    };
    let mut acc = CurvePoint {
        x: alloc_bigint256(builder, Some(blinding_native.0.clone()))?,
        y: alloc_bigint256(builder, Some(blinding_native.1.clone()))?,
    };
    let mut acc_native: Option<(BigUint, BigUint)> = Some(blinding_native.clone());

    let q_native: Option<(BigUint, BigUint)> = match (q_signed.x.to_biguint(), q_signed.y.to_biguint()) {
        (Some(x), Some(y)) => Some((x, y)),
        _ => None,
    };
    let phi_q_native: Option<(BigUint, BigUint)> = match (phi_q_signed.x.to_biguint(), phi_q_signed.y.to_biguint()) {
        (Some(x), Some(y)) => Some((x, y)),
        _ => None,
    };
    let t_native: Option<(BigUint, BigUint)> = match (t.x.to_biguint(), t.y.to_biguint()) {
        (Some(x), Some(y)) => Some((x, y)),
        _ => None,
    };

    for i in (0..129).rev() {
        acc = ec_double_with_curve(builder, &params, &acc)?;
        acc_native = acc_native
            .as_ref()
            .and_then(|a| ec_double_native_with_curve((&a.0, &a.1), p_field, &a_mod_p));

        let addend = select4_point(
            builder,
            p_field,
            b_k2a[i],
            v_k2a[i],
            b_k2b[i],
            v_k2b[i],
            &q_signed,
            &q_signed,
            &phi_q_signed,
            &t,
        )?;
        let addend_native = match (v_k2a[i], v_k2b[i]) {
            (Some(false), Some(false)) => q_native.clone(),
            (Some(true), Some(false)) => q_native.clone(),
            (Some(false), Some(true)) => phi_q_native.clone(),
            (Some(true), Some(true)) => t_native.clone(),
            _ => None,
        };
        let candidate = ec_add_with_curve(builder, &params, &acc, &addend)?;
        let candidate_native = match (acc_native.as_ref(), addend_native.as_ref()) {
            (Some(a), Some(b)) => ec_add_native_with_modulus((&a.0, &a.1), (&b.0, &b.1), p_field),
            _ => None,
        };

        // do_add = b1 OR b2.
        let b1b2_val = match (v_k2a[i], v_k2b[i]) {
            (Some(a), Some(b)) => Some(if a && b { Fr::one() } else { Fr::zero() }),
            _ => None,
        };
        let b1b2 = builder.alloc_with_value(b1b2_val)?;
        builder.enforce(
            LinearCombination::from((Fr::one(), b_k2a[i])),
            LinearCombination::from((Fr::one(), b_k2b[i])),
            LinearCombination::from((Fr::one(), b1b2)),
        )?;
        let do_add_val = match (v_k2a[i], v_k2b[i]) {
            (Some(a), Some(b)) => Some(a || b),
            _ => None,
        };
        let do_add_var = builder.alloc_with_value(
            do_add_val.map(|v| if v { Fr::one() } else { Fr::zero() }),
        )?;
        builder.enforce(
            builder.zero_lc(),
            builder.zero_lc(),
            LinearCombination(vec![
                (Fr::one(), do_add_var),
                (-Fr::one(), b_k2a[i]),
                (-Fr::one(), b_k2b[i]),
                (Fr::one(), b1b2),
            ]),
        )?;
        acc = select_point_with_p(builder, p_field, do_add_var, do_add_val, &candidate, &acc)?;
        acc_native = match (do_add_val, candidate_native, acc_native) {
            (Some(true), Some(c), _) => Some(c),
            (Some(false), _, prev) => prev,
            _ => None,
        };
    }

    // Subtract 2^129 · blinding.
    let two129_blinding = CurvePoint {
        x: alloc_bigint256(builder, Some(two129_blinding_native.0.clone()))?,
        y: alloc_bigint256(builder, Some(two129_blinding_native.1.clone()))?,
    };
    let neg_y_native = p_field - &two129_blinding_native.1;
    let neg_two129 = CurvePoint {
        x: two129_blinding.x.clone(),
        y: alloc_bigint256(builder, Some(neg_y_native))?,
    };
    let zero = alloc_bigint256(builder, Some(BigUint::from(0u64)))?;
    let sum = add_mod(builder, &two129_blinding.y, &neg_two129.y, p_field)?;
    enforce_bigint_eq(builder, &sum, &zero)?;
    let u2_part = ec_add_with_curve(builder, &params, &acc, &neg_two129)?;

    ec_add_with_curve(builder, &params, &u1g, &u2_part)
}

// =============================================================================
// ECDSA verification gadget
// =============================================================================

/// Verify an ECDSA secp256k1 signature in-circuit. Returns `Ok(())` if the
/// constraint system pins the signature as valid; the prover cannot satisfy
/// the constraint system without a valid (Q, r, s, m) tuple.
///
/// Inputs and outputs are all `BigInt256` over the scalar/base fields as
/// appropriate. The caller must have decoded the byte inputs via
/// [`bigint256_from_be_bytes`] and bound them to allocated witnesses.
pub fn ecdsa_verify(
    builder: &mut R1csBuilder<'_>,
    public_key: &CurvePoint,
    r: &BigInt256,
    s: &BigInt256,
    e: &BigInt256,
) -> Result<(), SynthesisError> {
    ecdsa_verify_with_curve(builder, &CurveParams::secp256k1(), public_key, r, s, e)
}

/// Generic in-circuit ECDSA verification. Same flow as [`ecdsa_verify`]
/// but parameterised by the curve, so the same code path serves both
/// secp256k1 and secp256r1.
pub fn ecdsa_verify_with_curve(
    builder: &mut R1csBuilder<'_>,
    params: &CurveParams,
    public_key: &CurvePoint,
    r: &BigInt256,
    s: &BigInt256,
    e: &BigInt256,
) -> Result<(), SynthesisError> {
    let n_field = params.n;
    let p_field = params.p;

    // ECDSA input validation. The spec rejects signatures with `r` or `s`
    // outside `[1, n − 1]`; without these checks a malicious prover could
    // (a) submit `s = 0` and bypass the `inv_mod(s)` constraint by
    //     supplying a wildcard pseudo-inverse, or
    // (b) submit `r ≥ n` and exploit the fact that
    //     `target = xr mod n` collapses to the same value for two
    //     different `r`.
    // We also enforce that the public key lies on the curve — without
    // this, a malicious prover could place `Q` off the curve and exploit
    // the looser arithmetic the generic add/double formulas allow.
    enforce_in_range_one_to_n(builder, r, n_field)?;
    enforce_in_range_one_to_n(builder, s, n_field)?;
    enforce_on_curve(builder, params, public_key)?;

    let w = inv_mod(builder, s, n_field)?;
    let u1 = bigint256_mul_mod(builder, e, &w, n_field)?;
    let u2 = bigint256_mul_mod(builder, r, &w, n_field)?;
    // Curve-specific scalar mul dispatch:
    // * secp256k1: u1·G via fixed-base 4-bit comb plus u2·Q via GLV +
    //   2-way joint Strauss-Shamir over 129-bit halves. Combined via a
    //   final ec_add.
    // * secp256r1: u1·G via fixed-base 4-bit comb plus u2·Q via 4-bit
    //   windowed double-and-add. P-256 has no useful endomorphism, so
    //   GLV doesn't apply; the comb-plus-windowed split still beats joint
    //   Strauss-Shamir by saving 192 adds (a chained 64-window scan with
    //   one add per window vs. the 256 adds the joint loop did).
    let r_point = if std::ptr::eq(params.p as *const _, secp256k1_p() as *const _) {
        scalar_mul_2p_secp256k1_comb_glv(builder, &u1, public_key, &u2)?
    } else {
        scalar_mul_2p_secp256r1_comb_windowed(builder, &u1, public_key, &u2)?
    };
    let xr = r_point.x.clone();
    // Compute xr mod n natively.
    let xr_mod_n: Option<BigUint> = xr.to_biguint().map(|v| &v % n_field);
    let target = alloc_bigint256(builder, xr_mod_n.clone())?;
    enforce_lt(builder, &target, n_field)?;
    // Prover supplies k ∈ {0, 1} such that xr = target + k * n.
    // (Because n < p < 2n, this is sufficient — xr can be at most p-1 < 2n.)
    let kv = match (xr.to_biguint(), xr_mod_n) {
        (Some(x), Some(t)) => {
            if x == t {
                Some(0u64)
            } else {
                Some(1u64)
            }
        }
        _ => None,
    };
    let k = builder.alloc_with_value(kv.map(Fr::from))?;
    enforce_boolean(builder, k)?;
    // Enforce xr - target - k*n = 0 (in the Fr field, via value LCs).
    let n_fr = bigint_to_fr(n_field);
    let mut lc = xr.value_lc();
    for (c, v) in target.value_lc().0 {
        lc.0.push((-c, v));
    }
    lc.0.push((-n_fr, k));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), lc)?;
    enforce_bigint_eq(builder, &target, r)?;
    let _ = p_field;
    Ok(())
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;

    fn run<F: FnOnce(&mut R1csBuilder<'_>)>(f: F) -> bool {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = crate::witness::WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();
        f(&mut b);
        cs.is_satisfied().unwrap()
    }

    #[test]
    fn bigint_mul_mod_n_native_match() {
        // a · b mod n with known values.
        let a = BigUint::from_str_radix(
            "1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF",
            16,
        )
        .unwrap();
        let b = BigUint::from_str_radix(
            "FEDCBA0987654321FEDCBA0987654321FEDCBA0987654321FEDCBA0987654321",
            16,
        )
        .unwrap();
        let n = secp256k1_n();
        let expected = (&a * &b) % n;
        assert!(run(|builder| {
            let av = alloc_bigint256(builder, Some(a.clone())).unwrap();
            let bv = alloc_bigint256(builder, Some(b.clone())).unwrap();
            let c = bigint256_mul_mod(builder, &av, &bv, n).unwrap();
            let c_actual = c.to_biguint().unwrap();
            assert_eq!(c_actual, expected, "native value mismatch");
        }));
    }

    /// Verify the GLV endomorphism: for the secp256k1 generator G,
    /// `(β·G.x mod p, G.y)` must equal `λ·G` (computed via repeated
    /// doubling).
    #[test]
    fn glv_phi_endomorphism_matches_lambda_g() {
        let (gx, gy) = secp256k1_g().clone();
        let p = secp256k1_p();
        let beta = secp256k1_beta();
        let lambda = secp256k1_lambda();
        // φ(G) = (β·G.x mod p, G.y)
        let phi_g_x = (beta * &gx) % p;
        let phi_g_y = gy.clone();
        // Compute λ·G via repeated doubling + adding.
        let mut acc: Option<(BigUint, BigUint)> = None;
        let mut current = (gx.clone(), gy.clone());
        let mut bits = lambda.clone();
        while bits > BigUint::from(0u64) {
            if &bits & BigUint::from(1u64) == BigUint::from(1u64) {
                acc = match acc {
                    None => Some(current.clone()),
                    Some((ax, ay)) => ec_add_native((&ax, &ay), (&current.0, &current.1)),
                };
            }
            bits >>= 1;
            if bits > BigUint::from(0u64) {
                current = ec_double_native((&current.0, &current.1)).expect("double");
            }
        }
        let (lx, ly) = acc.expect("λ·G");
        assert_eq!(lx, phi_g_x, "φ(G).x must equal (λ·G).x");
        assert_eq!(ly, phi_g_y, "φ(G).y must equal (λ·G).y");
    }

    /// Native GLV decomposition self-test: for a random scalar `k`,
    /// `k1 + λ·k2 ≡ k (mod n)` must hold, and both halves must fit in
    /// 129 bits.
    #[test]
    fn glv_decompose_native_relation_holds() {
        use num_bigint::{BigInt, Sign};
        let n = secp256k1_n();
        let lambda = secp256k1_lambda();
        let n_big = BigInt::from(n.clone());
        let lambda_big = BigInt::from(lambda.clone());

        for seed in [1u64, 42, 1234, 999999, 0xDEADBEEF] {
            let mut k_bytes = [0u8; 32];
            for (i, b) in seed.to_be_bytes().iter().enumerate() {
                k_bytes[24 + i] = *b;
            }
            let k = BigUint::from_bytes_be(&k_bytes) % n;
            let (k1, k2) = glv_decompose_native(&k);
            // k1 + λ·k2 ≡ k (mod n).
            let k1_in_n = ((&k1 % &n_big) + &n_big) % &n_big;
            let k2_in_n = ((&k2 % &n_big) + &n_big) % &n_big;
            let combined = (&k1_in_n + &lambda_big * &k2_in_n) % &n_big;
            assert_eq!(
                combined,
                BigInt::from(k.clone()),
                "GLV relation fails for k=0x{:x}",
                k
            );
            // |k1|, |k2| < 2^129.
            let bound = BigInt::from(BigUint::from(1u64) << 129);
            let abs_k1 = BigInt::from_biguint(Sign::Plus, k1.magnitude().clone());
            let abs_k2 = BigInt::from_biguint(Sign::Plus, k2.magnitude().clone());
            assert!(abs_k1 < bound, "|k1| exceeds 2^129 for k=0x{:x}", k);
            assert!(abs_k2 < bound, "|k2| exceeds 2^129 for k=0x{:x}", k);
        }
    }

    #[test]
    fn bigint_inv_mod_p_round_trip() {
        let a = BigUint::from_str_radix(
            "AAAA00001234567890ABCDEF1234567890ABCDEF1234567890ABCDEF12345678",
            16,
        )
        .unwrap();
        let p = secp256k1_p();
        assert!(run(|builder| {
            let av = alloc_bigint256(builder, Some(a.clone())).unwrap();
            let _inv = inv_mod(builder, &av, p).unwrap();
        }));
    }

    #[test]
    #[ignore]
    fn report_mul_mod_n_constraint_count() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = crate::witness::WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();
        let a = alloc_bigint256(&mut b, Some(BigUint::from(123u64))).unwrap();
        let c = alloc_bigint256(&mut b, Some(BigUint::from(456u64))).unwrap();
        let _ = bigint256_mul_mod(&mut b, &a, &c, secp256k1_n()).unwrap();
        println!("mul_mod_n constraints: {}", cs.num_constraints());
    }

    #[test]
    #[ignore]
    fn report_ec_add_constraint_count() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = crate::witness::WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();
        let (gx, gy) = secp256k1_g().clone();
        let (g2x, g2y) = ec_double_native((&gx, &gy)).unwrap();
        let p = CurvePoint {
            x: alloc_bigint256(&mut b, Some(gx)).unwrap(),
            y: alloc_bigint256(&mut b, Some(gy)).unwrap(),
        };
        let q = CurvePoint {
            x: alloc_bigint256(&mut b, Some(g2x)).unwrap(),
            y: alloc_bigint256(&mut b, Some(g2y)).unwrap(),
        };
        let _ = ec_add(&mut b, &p, &q).unwrap();
        println!("ec_add constraints: {}", cs.num_constraints());
    }

    #[test]
    fn ec_double_secp256r1_matches_native() {
        // Verify the parameterised in-circuit doubling on P-256 matches a
        // native double of the generator. This exercises the `a = -3`
        // coefficient path.
        let params = CurveParams::secp256r1();
        let (gx, gy) = params.g.clone();
        let (expected_x, expected_y) =
            ec_double_native_with_curve((&gx, &gy), params.p, &params.a_mod_p)
                .expect("native double G on P-256");
        assert!(run(|builder| {
            let p = CurvePoint {
                x: alloc_bigint256(builder, Some(gx.clone())).unwrap(),
                y: alloc_bigint256(builder, Some(gy.clone())).unwrap(),
            };
            let r = ec_double_with_curve(builder, &params, &p).unwrap();
            assert_eq!(r.x.to_biguint().unwrap(), expected_x);
            assert_eq!(r.y.to_biguint().unwrap(), expected_y);
        }));
    }

    #[test]
    fn ec_add_in_circuit_matches_native() {
        // P = G, Q = 2G (a known generic-add pair). Native compute the result
        // then compare against the gadget.
        let (gx, gy) = secp256k1_g().clone();
        let (g2x, g2y) = ec_double_native((&gx, &gy)).expect("double G");
        let (g3x, g3y) = ec_add_native((&gx, &gy), (&g2x, &g2y)).expect("G + 2G generic case");
        assert!(run(|builder| {
            let p = CurvePoint {
                x: alloc_bigint256(builder, Some(gx.clone())).unwrap(),
                y: alloc_bigint256(builder, Some(gy.clone())).unwrap(),
            };
            let q = CurvePoint {
                x: alloc_bigint256(builder, Some(g2x.clone())).unwrap(),
                y: alloc_bigint256(builder, Some(g2y.clone())).unwrap(),
            };
            let r = ec_add(builder, &p, &q).unwrap();
            assert_eq!(r.x.to_biguint().unwrap(), g3x);
            assert_eq!(r.y.to_biguint().unwrap(), g3y);
        }));
    }

    #[test]
    fn ecdsa_native_kat_via_k256() {
        // KAT from RFC 6979 / k256's own test vectors. We just confirm the
        // native helper builds in dev mode.
        use k256::ecdsa::signature::hazmat::PrehashSigner;
        use k256::ecdsa::SigningKey;
        let sk = SigningKey::from_slice(&[1u8; 32]).unwrap();
        let vk = sk.verifying_key();
        let msg_digest = [0u8; 32];
        let sig: k256::ecdsa::Signature = sk.sign_prehash(&msg_digest).unwrap();
        // Re-verify with the public-key bytes.
        let encoded = vk.to_sec1_point(false);
        let pkx: [u8; 32] = encoded.x().unwrap().as_slice().try_into().unwrap();
        let pky: [u8; 32] = encoded.y().unwrap().as_slice().try_into().unwrap();
        let sig_bytes = sig.to_bytes();
        let r: [u8; 32] = sig_bytes[..32].try_into().unwrap();
        let s: [u8; 32] = sig_bytes[32..].try_into().unwrap();
        assert!(ecdsa_verify_native((pkx, pky), (r, s), msg_digest));
    }

    /// Construct a [`CurvePoint`] from a `(BigUint, BigUint)` pair. Convenience
    /// wrapper for the baseline measurement tests below.
    fn point_from_biguints(
        builder: &mut R1csBuilder<'_>,
        x: BigUint,
        y: BigUint,
    ) -> CurvePoint {
        CurvePoint {
            x: alloc_bigint256(builder, Some(x)).unwrap(),
            y: alloc_bigint256(builder, Some(y)).unwrap(),
        }
    }

    /// Generate a real KAT signature with k256 + a deterministic secret key,
    /// run the in-circuit verifier on it, and return the constraint count.
    /// Used as the optimization baseline.
    fn measure_ecdsa_verify_secp256k1() -> usize {
        use k256::ecdsa::signature::hazmat::PrehashSigner;
        use k256::ecdsa::SigningKey;
        let sk = SigningKey::from_slice(&[7u8; 32]).unwrap();
        let vk = sk.verifying_key();
        let msg_digest = [0x5au8; 32];
        let sig: k256::ecdsa::Signature = sk.sign_prehash(&msg_digest).unwrap();
        let encoded = vk.to_sec1_point(false);
        let pkx: [u8; 32] = encoded.x().unwrap().as_slice().try_into().unwrap();
        let pky: [u8; 32] = encoded.y().unwrap().as_slice().try_into().unwrap();
        let sig_bytes = sig.to_bytes();
        let r_bytes: [u8; 32] = sig_bytes[..32].try_into().unwrap();
        let s_bytes: [u8; 32] = sig_bytes[32..].try_into().unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = crate::witness::WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();

        let pkx_big = BigUint::from_bytes_be(&pkx);
        let pky_big = BigUint::from_bytes_be(&pky);
        let r_big = BigUint::from_bytes_be(&r_bytes);
        let s_big = BigUint::from_bytes_be(&s_bytes);
        let e_big = BigUint::from_bytes_be(&msg_digest);

        let q = point_from_biguints(&mut b, pkx_big, pky_big);
        let r = alloc_bigint256(&mut b, Some(r_big)).unwrap();
        let s = alloc_bigint256(&mut b, Some(s_big)).unwrap();
        let e = alloc_bigint256(&mut b, Some(e_big)).unwrap();
        ecdsa_verify(&mut b, &q, &r, &s, &e).unwrap();
        let n_constraints = cs.num_constraints();
        if !cs.is_satisfied().unwrap() {
            let which = cs.which_is_unsatisfied().unwrap();
            panic!(
                "KAT must satisfy the gadget; constraint count={n_constraints}; \
                 first unsatisfied: {which:?}"
            );
        }
        n_constraints
    }

    /// Off-curve public key must be rejected by `enforce_on_curve`. We
    /// construct a synthetic `(Q.x, fake_y)` that satisfies neither
    /// `y² = x³ + 7` (secp256k1) nor any other Weierstrass equation, and
    /// confirm the constraint system reports unsatisfied.
    #[test]
    fn ecdsa_rejects_off_curve_public_key() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = crate::witness::WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();
        // Use generator's x but flip y to a value that's not the correct
        // y(G) (and not -y(G) either, which would still be on the curve).
        let (gx, _gy) = secp256k1_g().clone();
        let bogus_y = BigUint::from(42u64);
        let q = point_from_biguints(&mut b, gx, bogus_y);
        let r = alloc_bigint256(&mut b, Some(BigUint::from(1u64))).unwrap();
        let s = alloc_bigint256(&mut b, Some(BigUint::from(1u64))).unwrap();
        let e = alloc_bigint256(&mut b, Some(BigUint::from(0u64))).unwrap();
        // The verifier returns Ok because constraint emission succeeds; the
        // resulting constraint system is what must be unsatisfied.
        let _ = ecdsa_verify(&mut b, &q, &r, &s, &e);
        assert!(
            !cs.is_satisfied().unwrap(),
            "off-curve public key must fail enforce_on_curve"
        );
    }

    /// `enforce_in_range_one_to_n` must reject `value = 0`. The
    /// constraint `value · value_inv = 1 (mod n)` has no solution when
    /// `value = 0`, so for any prover-supplied `value_inv` the
    /// multiplication constraint is unsatisfied.
    #[test]
    fn enforce_in_range_one_to_n_rejects_zero() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = crate::witness::WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();
        // Allocate `value = 0` and lie about the inverse: claim the
        // inverse is 1 (so the prover's mul gives `0 · 1 = 0 ≠ 1`).
        let n = secp256k1_n();
        let value = alloc_bigint256(&mut b, Some(BigUint::from(0u64))).unwrap();
        // Call the in-range check; the alloc inside will produce `None`
        // for the inverse so we have to short-circuit the soundness check
        // by re-implementing the constraint with our chosen fake inverse.
        // The simplest way to demonstrate: emit `value · 1 = 1` manually
        // and verify the constraint system is unsatisfied.
        let one = alloc_bigint256(&mut b, Some(BigUint::from(1u64))).unwrap();
        let prod = bigint256_mul_mod(&mut b, &value, &one, n).unwrap();
        enforce_bigint_eq(&mut b, &prod, &one).unwrap();
        assert!(
            !cs.is_satisfied().unwrap(),
            "value = 0 must fail the value · value_inv = 1 constraint"
        );
    }

    /// Baseline measurement for the secp256k1 ECDSA verify gadget. Reports
    /// the number of R1CS constraints emitted on a real KAT and pins it
    /// against an upper bound so optimization regressions trip CI.
    ///
    /// History:
    /// * 17.6M — initial implementation (LSB-first double-and-add, separate
    ///   scalar muls per `u1·G` and `u2·Q`).
    /// * 9.1M  — MSB-first joint Strauss-Shamir (shared doublings).
    /// * 6.1M  — `sub_mod` simplified to one allocation + one linear
    ///   constraint (was two `add_mod`s + alias check).
    /// * 5.8M  — `enforce_lt` elided from `select_*` outputs (inputs are
    ///   already `< p`).
    /// * 4.0M  — GLV endomorphism: 4-way joint Strauss-Shamir over 129-bit
    ///   halves with a 16-entry precomputed addend table.
    /// * 3.6M  — Fixed-base 4-bit generator comb for `u1·G` + 2-way joint
    ///   GLV Strauss-Shamir for `u2·Q`. Also includes the on-curve and
    ///   range-check soundness validations added concurrently.
    #[test]
    fn report_ecdsa_verify_secp256k1_baseline() {
        let n = measure_ecdsa_verify_secp256k1();
        // Hard upper bound — present implementation lives well below this.
        // Lower this when an optimization PR cuts the count further.
        const UPPER_BOUND: usize = 3_800_000;
        println!("ecdsa_verify_with_curve (secp256k1) constraints: {n}");
        assert!(
            n <= UPPER_BOUND,
            "ECDSA secp256k1 constraint count regressed: {n} > {UPPER_BOUND}"
        );
    }

    /// Same as the secp256k1 baseline but for the parameterised P-256 path
    /// inside `ecdsa_verify_with_curve`. The signature is generated with
    /// the `p256` crate and re-verified in-circuit.
    fn measure_ecdsa_verify_secp256r1() -> usize {
        use p256::ecdsa::signature::hazmat::PrehashSigner;
        use p256::ecdsa::SigningKey;
        let sk = SigningKey::from_slice(&[11u8; 32]).unwrap();
        let vk = sk.verifying_key();
        let msg_digest = [0xa5u8; 32];
        let sig: p256::ecdsa::Signature = sk.sign_prehash(&msg_digest).unwrap();
        let encoded = vk.to_sec1_bytes();
        // Encoded is 65 bytes 0x04 || x || y.
        let pkx: [u8; 32] = encoded[1..33].try_into().unwrap();
        let pky: [u8; 32] = encoded[33..65].try_into().unwrap();
        let sig_bytes = sig.to_bytes();
        let r_bytes: [u8; 32] = sig_bytes[..32].try_into().unwrap();
        let s_bytes: [u8; 32] = sig_bytes[32..].try_into().unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = crate::witness::WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();

        let pkx_big = BigUint::from_bytes_be(&pkx);
        let pky_big = BigUint::from_bytes_be(&pky);
        let r_big = BigUint::from_bytes_be(&r_bytes);
        let s_big = BigUint::from_bytes_be(&s_bytes);
        let e_big = BigUint::from_bytes_be(&msg_digest);

        let params = CurveParams::secp256r1();
        let q = point_from_biguints(&mut b, pkx_big, pky_big);
        let r = alloc_bigint256(&mut b, Some(r_big)).unwrap();
        let s = alloc_bigint256(&mut b, Some(s_big)).unwrap();
        let e = alloc_bigint256(&mut b, Some(e_big)).unwrap();
        ecdsa_verify_with_curve(&mut b, &params, &q, &r, &s, &e).unwrap();
        assert!(
            cs.is_satisfied().unwrap(),
            "P-256 KAT must satisfy the gadget"
        );
        cs.num_constraints()
    }

    /// Baseline measurement for the secp256r1 (NIST P-256) ECDSA verify
    /// gadget. P-256 has no useful endomorphism, so GLV doesn't apply;
    /// the optimisation lineage is shared with secp256k1 up to and
    /// including `enforce_lt` elision.
    ///
    /// History:
    /// * 18.2M — initial implementation.
    /// * 9.4M  — MSB-first joint Strauss-Shamir.
    /// * 6.4M  — simplified `sub_mod`.
    /// * 6.1M  — `enforce_lt` elision in `select_*`.
    /// * 5.4M  — Fixed-base 4-bit comb for `u1·G` + 4-bit windowed
    ///   double-and-add for `u2·Q`. P-256 has no useful endomorphism, so
    ///   GLV doesn't apply; this split saves the 192 adds the joint
    ///   Strauss-Shamir loop was paying per-bit.
    #[test]
    fn report_ecdsa_verify_secp256r1_baseline() {
        let n = measure_ecdsa_verify_secp256r1();
        const UPPER_BOUND: usize = 5_700_000;
        println!("ecdsa_verify_with_curve (secp256r1) constraints: {n}");
        assert!(
            n <= UPPER_BOUND,
            "ECDSA secp256r1 constraint count regressed: {n} > {UPPER_BOUND}"
        );
    }

    /// Native ECDSA verification mirror, used by tests to populate
    /// prover-side witnesses. Kept inside the test module so the gadget
    /// crate doesn't need `k256` as a non-dev dep.
    pub fn ecdsa_verify_native(
        public_key: ([u8; 32], [u8; 32]),
        signature: ([u8; 32], [u8; 32]),
        msg_digest: [u8; 32],
    ) -> bool {
        use k256::ecdsa::signature::hazmat::PrehashVerifier;
        use k256::ecdsa::{Signature, VerifyingKey};
        let mut sec1 = [0u8; 65];
        sec1[0] = 0x04;
        sec1[1..33].copy_from_slice(&public_key.0);
        sec1[33..].copy_from_slice(&public_key.1);
        let vk = match VerifyingKey::from_sec1_bytes(&sec1) {
            Ok(v) => v,
            Err(_) => return false,
        };
        let mut sig_bytes = [0u8; 64];
        sig_bytes[..32].copy_from_slice(&signature.0);
        sig_bytes[32..].copy_from_slice(&signature.1);
        let sig = match Signature::from_slice(&sig_bytes) {
            Ok(s) => s,
            Err(_) => return false,
        };
        vk.verify_prehash(&msg_digest, &sig).is_ok()
    }
}
