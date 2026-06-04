//! Keccak-f[1600] permutation gadget (ROADMAP step **WS-D.1**).
//!
//! Implements the FIPS 202 Keccak-f[1600] permutation as 24 rounds over a 5x5
//! array of 64-bit lanes. Each lane is held as a 64-bit [`WordN`] (LSB first).
//!
//! The four bit-twiddles needed by Keccak are:
//!
//! | op            | R1CS cost per 64-bit lane                                                     |
//! |---------------|-------------------------------------------------------------------------------|
//! | `rotl_lane`   | 0 (pure index permutation; no fresh witnesses, no constraints)                 |
//! | `not_lane`    | 0 (per-bit `1 - x` LC; no fresh witnesses, no constraints)                     |
//! | `xor_n`       | 64 (one fresh boolean witness per bit + the `(2a)*b = a+b-out` XOR constraint)  |
//! | `and_n`       | 64 (one fresh witness per bit; constraint `a_i * b_i = out_i`)                  |
//!
//! Per round we use roughly:
//! * θ: 5 lane-XORs (the column parities) + 5 lane-XORs (D = C[x-1] XOR rotl(C[x+1],1))
//!   + 25 lane-XORs (A'[x,y] = A[x,y] XOR D[x]) ≈ 35 × 64 = ~2240 XOR constraints.
//! * ρ + π: 0 (pure permutations).
//! * χ: 25 NOT + 25 AND + 25 XOR = 25 × (64 + 64) = ~3200 constraints.
//! * ι: one lane-XOR with the round-constant lane ≈ 64 constraints.
//!
//! Times 24 rounds, plus the 25 input lane decompositions and 25 output
//! rebindings at the dispatcher level. Real per-circuit constraint counts are
//! printed by the KAT test below.

#![allow(clippy::needless_range_loop)]

use ark_bn254::Fr;
use ark_ff::One;
use ark_relations::r1cs::{LinearCombination, SynthesisError, Variable};

use crate::gadgets::bitwise::{and_n, xor_n, xor_n_inputs, WordN};
use crate::gadgets::range::{decompose_into_bits, enforce_recompose_equals};
use crate::r1cs_builder::R1csBuilder;

/// Keccak state width in lanes (5 × 5 = 25 64-bit lanes = 1600 bits).
pub const KECCAK_LANES: usize = 25;
/// Number of Keccak-f[1600] rounds.
pub const KECCAK_ROUNDS: usize = 24;
/// Bit width of one Keccak lane.
pub const LANE_BITS: usize = 64;

/// Round constants RC[0..24] for Keccak-f[1600] (FIPS 202 §3.2.5 / Algorithm 5).
pub const KECCAKF_RC: [u64; KECCAK_ROUNDS] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

/// ρ rotation offsets indexed by `[x][y]` (FIPS 202 §3.2.2 / Table 2).
///
/// `ROTATION_OFFSETS[x][y]` is the number of bit-positions by which lane
/// `A[x,y]` is rotated left during the ρ step. The (0,0) lane is the identity.
pub const ROTATION_OFFSETS: [[u32; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

// =============================================================================
// Native reference (used by KAT + setup-mode value tracking).
// =============================================================================

/// Native Keccak-f[1600] permutation operating in place on a 25-lane state.
///
/// This is an inline implementation (no external `keccak` crate dependency
/// in the gadget code-path) so the gadget can track concrete values through
/// every round at proving time without pulling extra crates into the library
/// build. The reference [`keccak`] crate is only used in the test module.
pub fn keccakf1600_native(state: &mut [u64; KECCAK_LANES]) {
    for rc in KECCAKF_RC.iter() {
        // θ
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
        }
        let mut d = [0u64; 5];
        for x in 0..5 {
            d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        }
        for x in 0..5 {
            for y in 0..5 {
                state[x + 5 * y] ^= d[x];
            }
        }

        // ρ + π. Build B such that B[y][(2x + 3y) mod 5] = rotl(A[x][y], r[x][y]).
        let mut b = [0u64; 25];
        for x in 0..5 {
            for y in 0..5 {
                let nx = y;
                let ny = (2 * x + 3 * y) % 5;
                b[nx + 5 * ny] = state[x + 5 * y].rotate_left(ROTATION_OFFSETS[x][y]);
            }
        }

        // χ
        for y in 0..5 {
            for x in 0..5 {
                state[x + 5 * y] =
                    b[x + 5 * y] ^ (!b[((x + 1) % 5) + 5 * y] & b[((x + 2) % 5) + 5 * y]);
            }
        }

        // ι
        state[0] ^= rc;
    }
}

// =============================================================================
// 64-bit lane bitwise helpers (no fresh witnesses, no constraints).
// =============================================================================

/// Left rotation of a 64-bit lane by `k` bit-positions. Pure index permutation:
/// `out_i = a_{(i + 64 - k) mod 64}`. Zero R1CS cost.
fn rotl_lane(a: &WordN, k: u32) -> WordN {
    debug_assert_eq!(a.num_bits, LANE_BITS);
    let k = (k as usize) % LANE_BITS;
    let bits: Vec<LinearCombination<Fr>> = (0..LANE_BITS)
        .map(|i| a.bits[(i + LANE_BITS - k) % LANE_BITS].clone())
        .collect();
    let value = a.value.map(|v| v.rotate_left(k as u32));
    WordN::from_bits(bits, LANE_BITS, value)
}

/// Bitwise NOT of a 64-bit lane: per-bit `1 - a_i` as a fresh LC. Zero R1CS cost
/// when callers consume the result inside a downstream AND / XOR (the per-bit
/// LC just gets folded into a bigger LC at the next gate).
fn not_lane(a: &WordN) -> WordN {
    debug_assert_eq!(a.num_bits, LANE_BITS);
    let bits: Vec<LinearCombination<Fr>> = a
        .bits
        .iter()
        .map(|bit| {
            let mut terms: Vec<(Fr, Variable)> = Vec::with_capacity(bit.0.len() + 1);
            terms.push((Fr::one(), Variable::One));
            for (c, v) in bit.0.iter() {
                terms.push((-*c, *v));
            }
            LinearCombination(terms)
        })
        .collect();
    let value = a.value.map(|v| !v);
    WordN::from_bits(bits, LANE_BITS, value)
}

/// Build a 64-bit "constant lane" whose bit-LCs are the constant 0/1
/// coefficients on the always-on `Variable::One`. Used for the round-constant
/// in the ι step.
fn constant_lane(value: u64) -> WordN {
    let mut bits = Vec::with_capacity(LANE_BITS);
    for i in 0..LANE_BITS {
        let bit_val = (value >> i) & 1;
        let lc = if bit_val == 1 {
            LinearCombination(vec![(Fr::one(), Variable::One)])
        } else {
            LinearCombination(vec![])
        };
        bits.push(lc);
    }
    WordN::from_bits(bits, LANE_BITS, Some(value))
}

// =============================================================================
// Lane decomposition / rebinding helpers (used by the blackbox dispatcher).
// =============================================================================

/// Decompose a single 64-bit value-variable into a 64-bit [`WordN`] with all
/// bits as freshly-allocated boolean witnesses (LSB first). This is the
/// gadget's input boundary: each ACIR input witness for a Keccak lane comes
/// in as a `Variable` holding the lane's u64 value packed into an `Fr`.
pub fn lane_from_value_var(
    builder: &mut R1csBuilder<'_>,
    value_var: Variable,
    value: Option<Fr>,
) -> Result<WordN, SynthesisError> {
    let bits = decompose_into_bits(builder, value_var, LANE_BITS, value)?;
    let u64_value = value.map(fr_to_u64_low);
    let bit_lcs = bits
        .into_iter()
        .map(|v| LinearCombination(vec![(Fr::one(), v)]))
        .collect();
    Ok(WordN::from_bits(bit_lcs, LANE_BITS, u64_value))
}

/// Bind the bit-decomposition of `word` to the ACIR output `out_var` via a
/// single linear constraint `sum_i 2^i * bits[i] = out_var`.
pub fn bind_lane_to_var(
    builder: &R1csBuilder<'_>,
    word: &WordN,
    out_var: Variable,
) -> Result<(), SynthesisError> {
    debug_assert_eq!(word.num_bits, LANE_BITS);
    enforce_recompose_equals(builder, &word.bits, out_var)
}

/// Truncate an `Fr` to the low 64 bits. Mirrors the helper in
/// `gadgets::bitwise` but kept private to the keccak module to keep the
/// inter-module surface minimal.
fn fr_to_u64_low(fr: Fr) -> u64 {
    let bytes = crate::field::fr_to_be_bytes(&fr);
    let mut out = 0u64;
    for &b in &bytes[24..32] {
        out = (out << 8) | b as u64;
    }
    out
}

// =============================================================================
// In-circuit permutation.
// =============================================================================

/// Run Keccak-f[1600] on the 25 input lane variables and return 25 freshly-
/// bit-decomposed output lane variables.
///
/// Each input variable is range-checked (implicitly) by the 64-bit
/// decomposition that the gadget does on entry. Each output variable is
/// allocated fresh and pinned to its lane's bit-LC sum via one linear
/// constraint.
pub fn keccakf1600_in_circuit(
    builder: &mut R1csBuilder<'_>,
    state: &[Variable; KECCAK_LANES],
    values: &[Option<Fr>; KECCAK_LANES],
) -> Result<[Variable; KECCAK_LANES], SynthesisError> {
    // 1. Decompose each input lane into a 64-bit WordN.
    let mut lanes: Vec<WordN> = Vec::with_capacity(KECCAK_LANES);
    for i in 0..KECCAK_LANES {
        lanes.push(lane_from_value_var(builder, state[i], values[i])?);
    }

    // 2. Run 24 rounds in-place on `lanes`.
    for round in 0..KECCAK_ROUNDS {
        // θ -----------------------------------------------------------------
        // C[x] = A[x,0] XOR A[x,1] XOR A[x,2] XOR A[x,3] XOR A[x,4]
        //
        // The 5-input XOR per column is batched via `xor_n_inputs` (sum +
        // 2-bit carry) instead of a chain of 4 binary XORs. Drops the
        // per-bit cost from `4·2 = 8` constraints to `1 + 2 + 1 = 4`,
        // saving ~8% of total Keccak-f[1600] cost across 24 rounds.
        let mut c: Vec<WordN> = Vec::with_capacity(5);
        for x in 0..5 {
            let inputs: [&WordN; 5] = [
                &lanes[x],
                &lanes[x + 5],
                &lanes[x + 10],
                &lanes[x + 15],
                &lanes[x + 20],
            ];
            c.push(xor_n_inputs(builder, &inputs)?);
        }
        // D[x] = C[x-1] XOR rotl(C[x+1], 1)
        let mut d: Vec<WordN> = Vec::with_capacity(5);
        for x in 0..5 {
            let left = &c[(x + 4) % 5];
            let right_rot = rotl_lane(&c[(x + 1) % 5], 1);
            d.push(xor_n(builder, left, &right_rot)?);
        }
        // A'[x,y] = A[x,y] XOR D[x]
        for x in 0..5 {
            for y in 0..5 {
                let idx = x + 5 * y;
                lanes[idx] = xor_n(builder, &lanes[idx], &d[x])?;
            }
        }

        // ρ + π -------------------------------------------------------------
        // B[y, (2x + 3y) mod 5] = rotl(A[x,y], r[x,y])
        let mut b: Vec<Option<WordN>> = (0..KECCAK_LANES).map(|_| None).collect();
        for x in 0..5 {
            for y in 0..5 {
                let nx = y;
                let ny = (2 * x + 3 * y) % 5;
                b[nx + 5 * ny] = Some(rotl_lane(&lanes[x + 5 * y], ROTATION_OFFSETS[x][y]));
            }
        }
        let b: Vec<WordN> = b.into_iter().map(|o| o.expect("filled")).collect();

        // χ -----------------------------------------------------------------
        // A''[x,y] = B[x,y] XOR ((NOT B[x+1,y]) AND B[x+2,y])
        for y in 0..5 {
            // Pre-compute NOT B[*,y] once per row (free — pure LC negation).
            let row_not: Vec<WordN> = (0..5).map(|x| not_lane(&b[x + 5 * y])).collect();
            for x in 0..5 {
                let nb = &row_not[(x + 1) % 5];
                let b2 = &b[((x + 2) % 5) + 5 * y];
                let and_part = and_n(builder, nb, b2)?;
                lanes[x + 5 * y] = xor_n(builder, &b[x + 5 * y], &and_part)?;
            }
        }

        // ι -----------------------------------------------------------------
        let rc_lane = constant_lane(KECCAKF_RC[round]);
        lanes[0] = xor_n(builder, &lanes[0], &rc_lane)?;
    }

    // 3. Allocate fresh output variables and bind each to its lane's bit sum.
    let mut out_vars = [Variable::One; KECCAK_LANES];
    for i in 0..KECCAK_LANES {
        let out_val = lanes[i].value.map(|v| {
            // u64 -> Fr (low 64 bits live in the lowest 8 BE bytes).
            let mut bytes = [0u8; 32];
            let v_be = v.to_be_bytes();
            bytes[24..32].copy_from_slice(&v_be);
            use ark_ff::PrimeField;
            Fr::from_be_bytes_mod_order(&bytes)
        });
        let out_var = builder.alloc_with_value(out_val)?;
        bind_lane_to_var(builder, &lanes[i], out_var)?;
        out_vars[i] = out_var;
    }

    Ok(out_vars)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::witness::WitnessMap;
    use ark_ff::PrimeField;
    use ark_relations::r1cs::ConstraintSystem;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    /// Expected output of Keccak-f[1600] applied to the all-zero state.
    ///
    /// Source: XKCP "KeccakF-1600-IntermediateValues.txt" / Noir's own
    /// `acvm-repo/blackbox_solver/src/hash.rs` sanity test. Pinned here so
    /// the gadget KAT is fully self-contained.
    const KECCAKF_ZERO_OUT: [u64; KECCAK_LANES] = [
        0xF1258F7940E1DDE7,
        0x84D5CCF933C0478A,
        0xD598261EA65AA9EE,
        0xBD1547306F80494D,
        0x8B284E056253D057,
        0xFF97A42D7F8E6FD4,
        0x90FEE5A0A44647C4,
        0x8C5BDA0CD6192E76,
        0xAD30A6F71B19059C,
        0x30935AB7D08FFC64,
        0xEB5AA93F2317D635,
        0xA9A6E6260D712103,
        0x81A57C16DBCF555F,
        0x43B831CD0347C826,
        0x01F22F1A11A5569F,
        0x05E5635A21D9AE61,
        0x64BEFEF28CC970F2,
        0x613670957BC46611,
        0xB87C5A554FD00ECB,
        0x8C3EE88A1CCF32C8,
        0x940C7922AE3A2614,
        0x1841F924A2C509E4,
        0x16F53526E70465C2,
        0x75F644E97F30A13B,
        0xEAF1FF7B5CECA249,
    ];

    fn u64_to_fr(v: u64) -> Fr {
        let mut bytes = [0u8; 32];
        let v_be = v.to_be_bytes();
        bytes[24..32].copy_from_slice(&v_be);
        Fr::from_be_bytes_mod_order(&bytes)
    }

    fn alloc_lane_var(builder: &mut R1csBuilder<'_>, value: u64) -> (Variable, Option<Fr>) {
        let fr = u64_to_fr(value);
        let v = builder.alloc_with_value(Some(fr)).unwrap();
        (v, Some(fr))
    }

    fn lane_var_value(cs: &ark_relations::r1cs::ConstraintSystemRef<Fr>, v: Variable) -> Fr {
        // Variable::Witness(k) maps to the proving-time assignment at index k.
        match v {
            Variable::Witness(idx) => cs.borrow().unwrap().witness_assignment[idx],
            _ => panic!("lane_var_value: not a witness"),
        }
    }

    fn fr_to_u64(fr: Fr) -> u64 {
        let bytes = crate::field::fr_to_be_bytes(&fr);
        let mut out = 0u64;
        for &b in &bytes[24..32] {
            out = (out << 8) | b as u64;
        }
        out
    }

    #[test]
    fn native_matches_keccak_crate_on_zero_state() {
        // Sanity: our inline native impl matches the published `keccak` crate.
        let mut state = [0u64; KECCAK_LANES];
        keccakf1600_native(&mut state);
        assert_eq!(state, KECCAKF_ZERO_OUT);

        // Double-check against the `keccak` crate.
        let mut state2 = [0u64; KECCAK_LANES];
        keccak::f1600(&mut state2);
        assert_eq!(state, state2);
    }

    #[test]
    fn in_circuit_zero_state_matches_kat() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();

        // Inputs: 25 lane variables all set to 0.
        let mut in_vars = [Variable::One; KECCAK_LANES];
        let mut in_vals: [Option<Fr>; KECCAK_LANES] = [None; KECCAK_LANES];
        for i in 0..KECCAK_LANES {
            let (v, val) = alloc_lane_var(&mut b, 0);
            in_vars[i] = v;
            in_vals[i] = val;
        }

        let out_vars = keccakf1600_in_circuit(&mut b, &in_vars, &in_vals).unwrap();

        assert!(cs.is_satisfied().unwrap(), "constraint system unsatisfied");

        for i in 0..KECCAK_LANES {
            let got = fr_to_u64(lane_var_value(&cs, out_vars[i]));
            assert_eq!(
                got, KECCAKF_ZERO_OUT[i],
                "lane {i} mismatch: got 0x{got:016x} want 0x{:016x}",
                KECCAKF_ZERO_OUT[i]
            );
        }

        println!(
            "Keccak-f[1600] (zero state): {} constraints, {} witnesses",
            cs.num_constraints(),
            cs.num_witness_variables()
        );
    }

    #[test]
    fn in_circuit_random_state_matches_native() {
        let mut rng = StdRng::seed_from_u64(0xD1_D1_D1_D1);
        let input: [u64; KECCAK_LANES] = std::array::from_fn(|_| rng.gen::<u64>());

        let mut expected = input;
        keccakf1600_native(&mut expected);

        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::<Fr>::new();
        let mut b = R1csBuilder::new(cs.clone(), Some(&map));
        b.finish_public_pass();

        let mut in_vars = [Variable::One; KECCAK_LANES];
        let mut in_vals: [Option<Fr>; KECCAK_LANES] = [None; KECCAK_LANES];
        for i in 0..KECCAK_LANES {
            let (v, val) = alloc_lane_var(&mut b, input[i]);
            in_vars[i] = v;
            in_vals[i] = val;
        }

        let out_vars = keccakf1600_in_circuit(&mut b, &in_vars, &in_vals).unwrap();

        assert!(cs.is_satisfied().unwrap(), "constraint system unsatisfied");

        for i in 0..KECCAK_LANES {
            let got = fr_to_u64(lane_var_value(&cs, out_vars[i]));
            assert_eq!(
                got, expected[i],
                "lane {i} mismatch: got 0x{got:016x} want 0x{:016x}",
                expected[i]
            );
        }
    }
}
