//! Black-box opcode lowering.
//!
//! Currently supports:
//! * `RANGE` (via [`crate::gadgets::range::enforce_range`])
//! * `Sha256Compression` (via [`crate::gadgets::hash::sha256_compression`])
//! * `AND` / `XOR` (via [`crate::gadgets::bitwise::{and_n, xor_n}`],
//!   ROADMAP step **WS-B.1**)
//!
//! All other variants are rejected before lowering ever starts (see
//! [`crate::opcodes::OpcodeClass::is_supported`] and the eager check in
//! [`crate::lower::LoweredAcirCircuit::new`]).

use acir::circuit::opcodes::{BlackBoxFuncCall, FunctionInput};
use acir::native_types::Witness;
use acir::FieldElement;
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_relations::r1cs::{LinearCombination, SynthesisError, Variable};

use crate::artifact::WitnessIndex;
use crate::field::noir_field_to_fr;
use crate::gadgets::aes::aes128_encrypt_in_circuit;
use crate::gadgets::bitwise::{and_n, xor_n, WordN, WORDN_MAX_BITS};
use crate::gadgets::blake2s::blake2s_in_circuit;
use crate::gadgets::blake3::blake3_in_circuit;
use crate::gadgets::curve::{curve_point_from_vars, ec_add_in_circuit, msm_in_circuit, CurvePoint};
use crate::gadgets::hash::{sha256_compression, word32_from_value_var};
use crate::gadgets::keccak::{keccakf1600_in_circuit, KECCAK_LANES};
use crate::gadgets::poseidon::{poseidon2_permutation, T as POSEIDON2_T};
use crate::gadgets::range::enforce_range;
use crate::r1cs_builder::R1csBuilder;

pub fn name_of(bb: &BlackBoxFuncCall<FieldElement>) -> String {
    bb.name().to_string()
}

/// Dispatch a supported black-box opcode to its gadget. Unsupported variants
/// reach this point only if `OpcodeClass::is_supported` is out of sync with
/// the dispatcher — treat that as an internal error rather than corrupting
/// the constraint system.
pub fn lower_black_box(
    builder: &mut R1csBuilder<'_>,
    bb: &BlackBoxFuncCall<FieldElement>,
) -> Result<(), SynthesisError> {
    match bb {
        BlackBoxFuncCall::RANGE { input, num_bits } => {
            // Constant fast path (ROADMAP WS-B.3): if the input is a known
            // constant, the range check is statically resolvable — no
            // constraints emitted. Otherwise fall back to the bit-decomposition
            // gadget on the underlying witness.
            if let Some(fr) = function_input_const_value(input) {
                let bound_fits = fr_fits_in_bits(&fr, *num_bits as usize);
                if !bound_fits {
                    tracing::error!(
                        "RANGE constant {fr} doesn't fit in {num_bits} bits — \
                         circuit is unsatisfiable as written."
                    );
                    return Err(SynthesisError::Unsatisfiable);
                }
                return Ok(());
            }
            let (var, value) = function_input_to_var(builder, input)?;
            enforce_range(builder, var, *num_bits as usize, value)?;
            Ok(())
        }
        BlackBoxFuncCall::Sha256Compression {
            inputs,
            hash_values,
            outputs,
        } => lower_sha256_compression(builder, inputs, hash_values, outputs),
        BlackBoxFuncCall::AND {
            lhs,
            rhs,
            num_bits,
            output,
        } => lower_bitwise_and(builder, lhs, rhs, *num_bits, *output),
        BlackBoxFuncCall::XOR {
            lhs,
            rhs,
            num_bits,
            output,
        } => lower_bitwise_xor(builder, lhs, rhs, *num_bits, *output),
        BlackBoxFuncCall::Poseidon2Permutation { inputs, outputs } => {
            lower_poseidon2_permutation(builder, inputs, outputs)
        }
        BlackBoxFuncCall::Keccakf1600 { inputs, outputs } => {
            lower_keccakf1600(builder, inputs, outputs)
        }
        BlackBoxFuncCall::Blake2s { inputs, outputs } => lower_blake2s(builder, inputs, outputs),
        BlackBoxFuncCall::Blake3 { inputs, outputs } => lower_blake3(builder, inputs, outputs),
        BlackBoxFuncCall::AES128Encrypt {
            inputs,
            iv,
            key,
            outputs,
        } => lower_aes128_encrypt(builder, inputs, iv, key, outputs),
        BlackBoxFuncCall::EmbeddedCurveAdd {
            input1,
            input2,
            predicate: _,
            outputs,
        } => lower_embedded_curve_add(builder, input1, input2, outputs),
        BlackBoxFuncCall::MultiScalarMul {
            points,
            scalars,
            predicate: _,
            outputs,
        } => lower_multi_scalar_mul(builder, points, scalars, outputs),
        BlackBoxFuncCall::EcdsaSecp256k1 {
            public_key_x,
            public_key_y,
            signature,
            hashed_message,
            predicate: _,
            output,
        } => lower_ecdsa_with_curve(
            builder,
            &crate::gadgets::ecdsa::CurveParams::secp256k1(),
            "secp256k1",
            public_key_x,
            public_key_y,
            signature,
            hashed_message,
            *output,
        ),
        BlackBoxFuncCall::EcdsaSecp256r1 {
            public_key_x,
            public_key_y,
            signature,
            hashed_message,
            predicate: _,
            output,
        } => lower_ecdsa_with_curve(
            builder,
            &crate::gadgets::ecdsa::CurveParams::secp256r1(),
            "secp256r1",
            public_key_x,
            public_key_y,
            signature,
            hashed_message,
            *output,
        ),
        _ => Err(SynthesisError::Unsatisfiable),
    }
}

/// Lower `BlackBoxFuncCall::EmbeddedCurveAdd { input1, input2, outputs }`
/// (ROADMAP step **WS-D.5**). Both points are Grumpkin affine `(x, y, is_inf)`
/// triples; the output is a fresh affine triple bound to the three ACIR
/// output witnesses.
fn lower_embedded_curve_add(
    builder: &mut R1csBuilder<'_>,
    input1: &[FunctionInput<FieldElement>; 3],
    input2: &[FunctionInput<FieldElement>; 3],
    outputs: &(
        acir::native_types::Witness,
        acir::native_types::Witness,
        acir::native_types::Witness,
    ),
) -> Result<(), SynthesisError> {
    let p1 = resolve_curve_point(builder, input1)?;
    let p2 = resolve_curve_point(builder, input2)?;
    let sum = ec_add_in_circuit(builder, &p1, &p2)?;
    bind_curve_point_outputs(builder, &sum, outputs)
}

/// Lower `BlackBoxFuncCall::MultiScalarMul { points, scalars, outputs }`.
/// `points.len()` must be `3 * N` (each point is `(x, y, is_inf)`) and
/// `scalars.len()` must be `2 * N` (each scalar is a `(lo, hi)` pair).
fn lower_multi_scalar_mul(
    builder: &mut R1csBuilder<'_>,
    points: &[FunctionInput<FieldElement>],
    scalars: &[FunctionInput<FieldElement>],
    outputs: &(
        acir::native_types::Witness,
        acir::native_types::Witness,
        acir::native_types::Witness,
    ),
) -> Result<(), SynthesisError> {
    if points.len() % 3 != 0 || scalars.len() % 2 != 0 {
        tracing::error!(
            "MultiScalarMul: points.len() ({}) must be a multiple of 3 and scalars.len() ({}) \
             must be a multiple of 2",
            points.len(),
            scalars.len(),
        );
        return Err(SynthesisError::Unsatisfiable);
    }
    let n_pts = points.len() / 3;
    let n_sc = scalars.len() / 2;
    if n_pts != n_sc {
        tracing::error!(
            "MultiScalarMul: points/3 ({}) != scalars/2 ({})",
            n_pts,
            n_sc,
        );
        return Err(SynthesisError::Unsatisfiable);
    }

    let mut curve_points: Vec<CurvePoint> = Vec::with_capacity(n_pts);
    for i in 0..n_pts {
        let triple: [&FunctionInput<FieldElement>; 3] =
            [&points[3 * i], &points[3 * i + 1], &points[3 * i + 2]];
        let p = resolve_curve_point_slice(builder, &triple)?;
        curve_points.push(p);
    }

    let mut limbs: Vec<(Variable, Option<Fr>, Variable, Option<Fr>)> = Vec::with_capacity(n_sc);
    for i in 0..n_sc {
        let (lo_var, lo_val) = function_input_to_var(builder, &scalars[2 * i])?;
        let (hi_var, hi_val) = function_input_to_var(builder, &scalars[2 * i + 1])?;
        limbs.push((lo_var, lo_val, hi_var, hi_val));
    }

    let result = msm_in_circuit(builder, &curve_points, &limbs)?;
    bind_curve_point_outputs(builder, &result, outputs)
}

/// Resolve a fixed-size `[FunctionInput; 3]` array into a `CurvePoint`.
fn resolve_curve_point(
    builder: &mut R1csBuilder<'_>,
    triple: &[FunctionInput<FieldElement>; 3],
) -> Result<CurvePoint, SynthesisError> {
    let slice: [&FunctionInput<FieldElement>; 3] = [&triple[0], &triple[1], &triple[2]];
    resolve_curve_point_slice(builder, &slice)
}

/// Resolve a borrowed-slice triple. The `is_infinity` flag is constrained to
/// be boolean inside `curve_point_from_vars`.
fn resolve_curve_point_slice(
    builder: &mut R1csBuilder<'_>,
    triple: &[&FunctionInput<FieldElement>; 3],
) -> Result<CurvePoint, SynthesisError> {
    let (xv, xval) = function_input_to_var(builder, triple[0])?;
    let (yv, yval) = function_input_to_var(builder, triple[1])?;
    let (iv, ival) = function_input_to_var(builder, triple[2])?;
    let is_inf_val: Option<bool> = ival.map(|v| {
        if v == Fr::one() {
            true
        } else if v.is_zero() {
            false
        } else {
            // Noir's contract: is_infinity is boolean. We let the boolean
            // enforcement constraint surface the violation downstream.
            false
        }
    });
    curve_point_from_vars(builder, xv, yv, iv, xval, yval, is_inf_val)
}

/// Bind the three output coordinates of a `CurvePoint` to three ACIR output
/// witnesses. Each output is a single linear equality.
fn bind_curve_point_outputs(
    builder: &mut R1csBuilder<'_>,
    point: &CurvePoint,
    outputs: &(
        acir::native_types::Witness,
        acir::native_types::Witness,
        acir::native_types::Witness,
    ),
) -> Result<(), SynthesisError> {
    let (ox, oy, oi) = outputs;
    bind_var_to_witness(builder, point.x, *ox)?;
    bind_var_to_witness(builder, point.y, *oy)?;
    bind_var_to_witness(builder, point.is_infinity, *oi)?;
    Ok(())
}

/// Bind an existing `Variable` (representing a computed gadget output) to a
/// new ACIR output `Witness` via the linear constraint
/// `0 * 0 = gadget_var - witness_var`.
fn bind_var_to_witness(
    builder: &mut R1csBuilder<'_>,
    gadget_var: Variable,
    out_wit: acir::native_types::Witness,
) -> Result<(), SynthesisError> {
    let out_idx = WitnessIndex::from_witness(out_wit);
    let witness_var = builder.alloc_witness(out_idx)?;
    builder.enforce(
        builder.zero_lc(),
        builder.zero_lc(),
        LinearCombination(vec![(Fr::one(), gadget_var), (-Fr::one(), witness_var)]),
    )
}

/// Lower `BlackBoxFuncCall::AES128Encrypt { inputs, iv, key, outputs }`
/// (ROADMAP step **WS-D.7**). The opcode is **CBC mode, no padding** —
/// `inputs.len()` is required to be a positive multiple of 16. (Noir's
/// `std::aes128::aes128_encrypt` wrapper handles PKCS#7 padding in Noir
/// before emitting the opcode, so a 16-byte plaintext shows up here as
/// 32 input bytes.) The 16-byte IV and key arrive as fixed-size arrays.
fn lower_aes128_encrypt(
    builder: &mut R1csBuilder<'_>,
    inputs: &[FunctionInput<FieldElement>],
    iv: &[FunctionInput<FieldElement>; 16],
    key: &[FunctionInput<FieldElement>; 16],
    outputs: &[Witness],
) -> Result<(), SynthesisError> {
    if inputs.is_empty() || inputs.len() % 16 != 0 {
        tracing::error!(
            "lower_aes128_encrypt: input length {} must be a positive multiple of 16 \
             (the AES128Encrypt opcode is CBC mode with NO padding; Noir's stdlib pads \
             before invoking the opcode).",
            inputs.len()
        );
        return Err(SynthesisError::Unsatisfiable);
    }
    if outputs.len() != inputs.len() {
        tracing::error!(
            "lower_aes128_encrypt: expected outputs.len() == inputs.len() ({}, got {})",
            inputs.len(),
            outputs.len(),
        );
        return Err(SynthesisError::Unsatisfiable);
    }

    let mut in_vars: Vec<(Variable, Option<Fr>)> = Vec::with_capacity(inputs.len());
    for fi in inputs.iter() {
        let (var, value) = function_input_to_var(builder, fi)?;
        in_vars.push((var, value));
    }
    let mut iv_vars_vec: Vec<(Variable, Option<Fr>)> = Vec::with_capacity(16);
    for fi in iv.iter() {
        let (var, value) = function_input_to_var(builder, fi)?;
        iv_vars_vec.push((var, value));
    }
    let iv_vars: [(Variable, Option<Fr>); 16] = iv_vars_vec
        .try_into()
        .map_err(|_| SynthesisError::Unsatisfiable)?;
    let mut key_vars_vec: Vec<(Variable, Option<Fr>)> = Vec::with_capacity(16);
    for fi in key.iter() {
        let (var, value) = function_input_to_var(builder, fi)?;
        key_vars_vec.push((var, value));
    }
    let key_vars: [(Variable, Option<Fr>); 16] = key_vars_vec
        .try_into()
        .map_err(|_| SynthesisError::Unsatisfiable)?;

    let gadget_out = aes128_encrypt_in_circuit(builder, &in_vars, &iv_vars, &key_vars)?;

    for (i, out_wit) in outputs.iter().enumerate() {
        let out_idx = WitnessIndex::from_witness(*out_wit);
        let witness_var = builder.alloc_witness(out_idx)?;
        builder.enforce(
            builder.zero_lc(),
            builder.zero_lc(),
            LinearCombination(vec![(Fr::one(), gadget_out[i]), (-Fr::one(), witness_var)]),
        )?;
    }
    Ok(())
}

/// Lower `BlackBoxFuncCall::Blake2s { inputs, outputs }` (ROADMAP step
/// **WS-D.2**). Each `FunctionInput` is a u8-valued field element (Noir emits
/// the u8 range check via a separate RANGE opcode, so we don't re-decompose
/// here — `blake2s_in_circuit` does an internal 8-bit decomposition for its
/// own bit-packing, which is the equivalent of a RANGE check). The 32 output
/// bytes are bound to fresh ACIR output witnesses via single linear
/// equalities.
fn lower_blake2s(
    builder: &mut R1csBuilder<'_>,
    inputs: &[FunctionInput<FieldElement>],
    outputs: &[Witness; 32],
) -> Result<(), SynthesisError> {
    // Resolve each FunctionInput byte into (Variable, Option<Fr>).
    let mut in_vars: Vec<(Variable, Option<Fr>)> = Vec::with_capacity(inputs.len());
    for fi in inputs.iter() {
        let (var, value) = function_input_to_var(builder, fi)?;
        in_vars.push((var, value));
    }

    let gadget_out = blake2s_in_circuit(builder, &in_vars)?;

    // Bind each gadget output byte Variable to the ACIR output Witness with a
    // single linear equality `0 * 0 = gadget_out - witness`.
    for (i, out_wit) in outputs.iter().enumerate() {
        let out_idx = WitnessIndex::from_witness(*out_wit);
        let witness_var = builder.alloc_witness(out_idx)?;
        builder.enforce(
            builder.zero_lc(),
            builder.zero_lc(),
            LinearCombination(vec![(Fr::one(), gadget_out[i]), (-Fr::one(), witness_var)]),
        )?;
    }
    Ok(())
}

/// Lower `BlackBoxFuncCall::Blake3 { inputs, outputs }` (ROADMAP step
/// **WS-D.3**). Each `FunctionInput` is a u8-valued field element; the gadget
/// internally bit-decomposes each byte (which doubles as the implicit
/// 8-bit range check). The 32 output bytes are bound to fresh ACIR output
/// witnesses via single linear equalities. Handles inputs of any length via
/// the standard Blake3 binary tree of `PARENT` compressions over 1024-byte
/// chunk chaining values.
fn lower_blake3(
    builder: &mut R1csBuilder<'_>,
    inputs: &[FunctionInput<FieldElement>],
    outputs: &[Witness; 32],
) -> Result<(), SynthesisError> {
    let mut in_vars: Vec<(Variable, Option<Fr>)> = Vec::with_capacity(inputs.len());
    for fi in inputs.iter() {
        let (var, value) = function_input_to_var(builder, fi)?;
        in_vars.push((var, value));
    }

    let gadget_out = blake3_in_circuit(builder, &in_vars)?;

    for (i, out_wit) in outputs.iter().enumerate() {
        let out_idx = WitnessIndex::from_witness(*out_wit);
        let witness_var = builder.alloc_witness(out_idx)?;
        builder.enforce(
            builder.zero_lc(),
            builder.zero_lc(),
            LinearCombination(vec![(Fr::one(), gadget_out[i]), (-Fr::one(), witness_var)]),
        )?;
    }
    Ok(())
}

/// Lower `BlackBoxFuncCall::Keccakf1600 { inputs, outputs }` (ROADMAP step
/// **WS-D.1**). Each lane is a 64-bit u64 packed into one field element on
/// both the input and output side. We bit-decompose every input lane (which
/// also enforces the implicit 64-bit range check), run the in-circuit
/// permutation, then bind each output Witness to its lane's bit sum.
fn lower_keccakf1600(
    builder: &mut R1csBuilder<'_>,
    inputs: &[FunctionInput<FieldElement>; KECCAK_LANES],
    outputs: &[Witness; KECCAK_LANES],
) -> Result<(), SynthesisError> {
    // Resolve each FunctionInput into a (Variable, Option<Fr>) pair. Constants
    // get pinned to a fresh witness by `function_input_to_var`, so the
    // downstream gadget can treat all inputs uniformly.
    let mut in_vars = [Variable::One; KECCAK_LANES];
    let mut in_vals: [Option<Fr>; KECCAK_LANES] = [None; KECCAK_LANES];
    for (i, fi) in inputs.iter().enumerate() {
        let (var, value) = function_input_to_var(builder, fi)?;
        in_vars[i] = var;
        in_vals[i] = value;
    }

    // The Keccak gadget bit-decomposes each lane internally (range-checking
    // each 64-bit lane along the way) and returns 25 fresh output lane
    // Variables already bound to their bit sums.
    let gadget_out_vars = keccakf1600_in_circuit(builder, &in_vars, &in_vals)?;

    // Bind each gadget output Variable to the ACIR output Witness with a
    // single linear equality. We can't reuse the gadget's lane WordN here
    // because `keccakf1600_in_circuit` doesn't expose them, so we just chain
    // an equality: `0 * 0 = gadget_out - witness`.
    for (i, out_wit) in outputs.iter().enumerate() {
        let out_idx = WitnessIndex::from_witness(*out_wit);
        let witness_var = builder.alloc_witness(out_idx)?;
        builder.enforce(
            builder.zero_lc(),
            builder.zero_lc(),
            LinearCombination(vec![
                (Fr::one(), gadget_out_vars[i]),
                (-Fr::one(), witness_var),
            ]),
        )?;
    }
    Ok(())
}

/// Lower `BlackBoxFuncCall::Poseidon2Permutation` over BN254 Fr. Noir's stdlib
/// pins the state width to
/// `bn254_blackbox_solver::poseidon2_config_state_size() = 4`. Any other
/// width is a backend bug or a Noir-version skew and we reject loudly.
fn lower_poseidon2_permutation(
    builder: &mut R1csBuilder<'_>,
    inputs: &[FunctionInput<FieldElement>],
    outputs: &[Witness],
) -> Result<(), SynthesisError> {
    assert_eq!(
        inputs.len(),
        POSEIDON2_T,
        "Poseidon2Permutation: expected {} inputs (state width T), got {}",
        POSEIDON2_T,
        inputs.len()
    );
    assert_eq!(
        outputs.len(),
        POSEIDON2_T,
        "Poseidon2Permutation: expected {} outputs (state width T), got {}",
        POSEIDON2_T,
        outputs.len()
    );

    // Resolve each input FunctionInput into (Variable, value).
    let mut in_vars = [Variable::One; POSEIDON2_T];
    let mut in_vals: [Option<Fr>; POSEIDON2_T] = [None; POSEIDON2_T];
    for (i, fi) in inputs.iter().enumerate() {
        let (var, value) = function_input_to_var(builder, fi)?;
        in_vars[i] = var;
        in_vals[i] = value;
    }

    let out_vars = poseidon2_permutation(builder, &in_vars, &in_vals)?;

    // Bind each gadget output Variable to the ACIR output Witness with a
    // single linear equality `0 * 0 = out_var - witness_var`.
    for (i, out_wit) in outputs.iter().enumerate() {
        let out_idx = WitnessIndex::from_witness(*out_wit);
        let witness_var = builder.alloc_witness(out_idx)?;
        builder.enforce(
            builder.zero_lc(),
            builder.zero_lc(),
            LinearCombination(vec![(Fr::one(), out_vars[i]), (-Fr::one(), witness_var)]),
        )?;
    }
    Ok(())
}

/// Lower `BlackBoxFuncCall::AND { lhs, rhs, num_bits, output }`.
///
/// Per ROADMAP step **WS-B.1**, this supports `num_bits ∈ [1, 64]`. Both
/// inputs are bit-decomposed into `num_bits` boolean wires, AND'd bit-wise
/// via [`and_n`], then recomposed into the output witness.
fn lower_bitwise_and(
    builder: &mut R1csBuilder<'_>,
    lhs: &FunctionInput<FieldElement>,
    rhs: &FunctionInput<FieldElement>,
    num_bits: u32,
    output: Witness,
) -> Result<(), SynthesisError> {
    let aw = decompose_function_input(builder, lhs, num_bits)?;
    let bw = decompose_function_input(builder, rhs, num_bits)?;
    let out_word = and_n(builder, &aw, &bw)?;
    bind_word_to_output(builder, &out_word, output)
}

/// Lower `BlackBoxFuncCall::XOR { lhs, rhs, num_bits, output }`.
///
/// Per ROADMAP step **WS-B.1**, this supports `num_bits ∈ [1, 64]`. Both
/// inputs are bit-decomposed into `num_bits` boolean wires, XOR'd bit-wise
/// via [`xor_n`], then recomposed into the output witness.
fn lower_bitwise_xor(
    builder: &mut R1csBuilder<'_>,
    lhs: &FunctionInput<FieldElement>,
    rhs: &FunctionInput<FieldElement>,
    num_bits: u32,
    output: Witness,
) -> Result<(), SynthesisError> {
    let aw = decompose_function_input(builder, lhs, num_bits)?;
    let bw = decompose_function_input(builder, rhs, num_bits)?;
    let out_word = xor_n(builder, &aw, &bw)?;
    bind_word_to_output(builder, &out_word, output)
}

/// Resolve a [`FunctionInput`] to a [`WordN`] of width `num_bits`. Widths
/// outside `[1, WORDN_MAX_BITS]` are rejected as `SynthesisError::Unsatisfiable`
/// — the user-facing `BackendError` is raised earlier by
/// `LoweredAcirCircuit::check_bitwise_widths` at setup time, so reaching this
/// branch implies a caller skipped the preflight. See ROADMAP step **WS-B.1**.
fn decompose_function_input(
    builder: &mut R1csBuilder<'_>,
    fi: &FunctionInput<FieldElement>,
    num_bits: u32,
) -> Result<WordN, SynthesisError> {
    let num_bits = num_bits as usize;
    if !(1..=WORDN_MAX_BITS).contains(&num_bits) {
        tracing::error!(
            "BlackBoxFuncCall::{{AND,XOR}}: num_bits={num_bits} > {WORDN_MAX_BITS}; \
             setup-time preflight (`check_bitwise_widths`) should have caught this. \
             See ROADMAP step WS-B.1."
        );
        return Err(SynthesisError::Unsatisfiable);
    }
    let (var, value) = function_input_to_var(builder, fi)?;
    WordN::from_value_var(builder, var, num_bits, value)
}

/// Allocate the ACIR `output` witness and bind it to the (already bit-
/// decomposed) `WordN` via a single linear recomposition constraint.
fn bind_word_to_output(
    builder: &mut R1csBuilder<'_>,
    word: &WordN,
    output: Witness,
) -> Result<(), SynthesisError> {
    let out_idx = WitnessIndex::from_witness(output);
    let out_var = builder.alloc_witness(out_idx)?;
    word.bind_to_var(builder, out_var)
}

fn lower_sha256_compression(
    builder: &mut R1csBuilder<'_>,
    inputs: &[FunctionInput<FieldElement>; 16],
    hash_values: &[FunctionInput<FieldElement>; 8],
    outputs: &[Witness; 8],
) -> Result<(), SynthesisError> {
    // Allocate / fetch every input and hash-state word as a Word32 with full
    // bit decomposition. Doing the decomposition here also gives us the
    // implicit 32-bit range check for free, which mirrors Noir's own
    // contract that Sha256Compression operands are u32s.
    let mut input_words = Vec::with_capacity(16);
    for fi in inputs.iter() {
        let (var, value) = function_input_to_var(builder, fi)?;
        let word = word32_from_value_var(builder, var, value)?;
        input_words.push(word);
    }
    let mut state_words = Vec::with_capacity(8);
    for fi in hash_values.iter() {
        let (var, value) = function_input_to_var(builder, fi)?;
        let word = word32_from_value_var(builder, var, value)?;
        state_words.push(word);
    }

    let input_arr: [_; 16] = std::array::from_fn(|i| input_words[i].clone());
    let state_arr: [_; 8] = std::array::from_fn(|i| state_words[i].clone());
    let out_words = sha256_compression(builder, &input_arr, &state_arr)?;

    // Bind the output Words to the ACIR output witnesses.
    for (i, out_wit) in outputs.iter().enumerate() {
        let out_idx = WitnessIndex::from_witness(*out_wit);
        let out_var = builder.alloc_witness(out_idx)?;
        // Enforce sum_j 2^j * bits[j] = out_var.
        crate::gadgets::range::enforce_recompose_equals(builder, &out_words[i].bits, out_var)?;
    }
    Ok(())
}

/// Resolve a [`FunctionInput`] into an Arkworks `Variable` plus the concrete
/// `Fr` value (or `None` in setup mode). For constants we allocate a fresh
/// auxiliary variable and pin it via a linear constraint, so downstream code
/// can treat constants and witnesses uniformly.
fn function_input_to_var(
    builder: &mut R1csBuilder<'_>,
    fi: &FunctionInput<FieldElement>,
) -> Result<(Variable, Option<Fr>), SynthesisError> {
    match fi {
        FunctionInput::Witness(w) => {
            let idx = WitnessIndex::from_witness(*w);
            let var = builder.alloc_witness(idx)?;
            let value = builder.maybe_witness_value(idx)?;
            Ok((var, value))
        }
        FunctionInput::Constant(c) => {
            let fr = noir_field_to_fr(c);
            // Allocate `var` and enforce `var = fr * One`, i.e. `0 * 0 = var - fr * One`.
            let var = builder.alloc_with_value(Some(fr))?;
            builder.enforce(
                builder.zero_lc(),
                builder.zero_lc(),
                LinearCombination(vec![(Fr::one(), var), (-fr, Variable::One)]),
            )?;
            Ok((var, Some(fr)))
        }
    }
}

/// Constant fast path (ROADMAP step **WS-B.3**). Returns `Some(value)` when
/// `fi` is a `FunctionInput::Constant`, allowing the caller to short-circuit
/// gadgets whose result is statically determined by a known constant input.
/// Returns `None` for witness inputs.
///
/// Today's callers: the [`enforce_range`] dispatch arm — if the RANGE input
/// is a constant that fits in the declared bit width, no constraints are
/// emitted. The pattern is straightforward to extend to any gadget whose
/// per-input cost dominates and whose output is constant-traceable.
fn function_input_const_value(fi: &FunctionInput<FieldElement>) -> Option<Fr> {
    match fi {
        FunctionInput::Witness(_) => None,
        FunctionInput::Constant(c) => Some(noir_field_to_fr(c)),
    }
}

/// Returns `true` if `value`'s big-endian representation has all-zero bits
/// above position `num_bits`. Used by the RANGE constant fast path.
fn fr_fits_in_bits(value: &Fr, num_bits: usize) -> bool {
    use crate::field::fr_to_be_bytes;
    if num_bits >= 254 {
        return true;
    }
    let bytes = fr_to_be_bytes(value);
    // bytes are big-endian, 32 bytes total. Bit `i` (LSB index) lives at byte
    // `31 - i/8`, position `i % 8`. We need every bit at position ≥ num_bits
    // to be zero.
    let high_zero_bytes = 32 - num_bits.div_ceil(8);
    for &b in &bytes[..high_zero_bytes] {
        if b != 0 {
            return false;
        }
    }
    // For the boundary byte (if num_bits isn't byte-aligned), the high bits
    // above (num_bits % 8) must also be zero.
    let leftover = num_bits % 8;
    if leftover != 0 {
        let boundary_byte = bytes[high_zero_bytes];
        let mask = !((1u8 << leftover) - 1);
        if boundary_byte & mask != 0 {
            return false;
        }
    }
    true
}

/// Lower `BlackBoxFuncCall::EcdsaSecp256k1` / `EcdsaSecp256r1`
/// (ROADMAP step **WS-D.6**), parameterised by the curve so the same code
/// path serves both Noir opcodes.
///
/// Inputs: 32-byte public-key X / Y / hashed-message (each `[u8; 32]`) and a
/// 64-byte signature (`r || s`). The gadget pins the `output: Witness` to
/// `1` whenever the supplied tuple is a valid signature; an invalid tuple
/// makes the constraint system unsatisfiable (proving fails). This matches
/// the contract Noir users expect: `let valid = ecdsa_verify(...); assert(valid);`.
///
/// **Cost warning**: a single ECDSA verification lowers to ~20M R1CS
/// constraints (two 256-bit scalar muls with non-native limb arithmetic
/// over BN254). Setup + prove on a circuit dominated by ECDSA may take
/// tens of minutes; the components are correct but the uncached schoolbook
/// lowering is intentionally un-optimised. See `gadgets::ecdsa` module docs.
#[allow(clippy::too_many_arguments)]
fn lower_ecdsa_with_curve(
    builder: &mut R1csBuilder<'_>,
    params: &crate::gadgets::ecdsa::CurveParams,
    curve_name: &str,
    public_key_x: &[FunctionInput<FieldElement>; 32],
    public_key_y: &[FunctionInput<FieldElement>; 32],
    signature: &[FunctionInput<FieldElement>; 64],
    hashed_message: &[FunctionInput<FieldElement>; 32],
    output: acir::native_types::Witness,
) -> Result<(), SynthesisError> {
    use crate::gadgets::ecdsa;
    tracing::warn!(
        "Lowering BlackBoxFuncCall::Ecdsa{} — this gadget emits roughly \
         20M R1CS constraints per verification (schoolbook non-native arithmetic). \
         Expect very long setup + prove times on circuits dominated by ECDSA.",
        curve_name,
    );

    fn decode_bytes_array<const N: usize>(
        builder: &mut R1csBuilder<'_>,
        bytes: &[FunctionInput<FieldElement>; N],
    ) -> Result<([Variable; N], Option<[u8; N]>), SynthesisError> {
        let mut byte_vars = [Variable::One; N];
        let mut byte_values_arr = [0u8; N];
        let mut all_known = true;
        for i in 0..N {
            let (var, value) = function_input_to_var(builder, &bytes[i])?;
            byte_vars[i] = var;
            match value {
                Some(v) => {
                    let big: num_bigint::BigUint = v.into();
                    let mut bs = big.to_bytes_be();
                    while bs.len() < 32 {
                        bs.insert(0, 0);
                    }
                    byte_values_arr[i] = *bs.last().unwrap();
                }
                None => all_known = false,
            }
        }
        Ok((
            byte_vars,
            if all_known {
                Some(byte_values_arr)
            } else {
                None
            },
        ))
    }

    let (pkx_vars, pkx_vals) = decode_bytes_array::<32>(builder, public_key_x)?;
    let (pky_vars, pky_vals) = decode_bytes_array::<32>(builder, public_key_y)?;
    let (sig_vars, sig_vals) = decode_bytes_array::<64>(builder, signature)?;
    let (msg_vars, msg_vals) = decode_bytes_array::<32>(builder, hashed_message)?;

    let pkx = ecdsa::bigint256_from_be_bytes(builder, pkx_vars, pkx_vals)?;
    let pky = ecdsa::bigint256_from_be_bytes(builder, pky_vars, pky_vals)?;
    let public_key = ecdsa::CurvePoint { x: pkx, y: pky };

    let mut r_vars = [Variable::One; 32];
    r_vars.copy_from_slice(&sig_vars[..32]);
    let mut s_vars = [Variable::One; 32];
    s_vars.copy_from_slice(&sig_vars[32..]);
    let r_vals: Option<[u8; 32]> = sig_vals.map(|s| {
        let mut a = [0u8; 32];
        a.copy_from_slice(&s[..32]);
        a
    });
    let s_vals: Option<[u8; 32]> = sig_vals.map(|s| {
        let mut a = [0u8; 32];
        a.copy_from_slice(&s[32..]);
        a
    });
    let r = ecdsa::bigint256_from_be_bytes(builder, r_vars, r_vals)?;
    let s = ecdsa::bigint256_from_be_bytes(builder, s_vars, s_vals)?;
    let e = ecdsa::bigint256_from_be_bytes(builder, msg_vars, msg_vals)?;

    ecdsa::ecdsa_verify_with_curve(builder, params, &public_key, &r, &s, &e)?;

    // Bind the output witness to 1 — Noir uses `let v = ecdsa_verify(...); assert(v)`.
    let out_idx = crate::artifact::WitnessIndex::from_witness(output);
    let out_var = builder.alloc_witness(out_idx)?;
    builder.enforce(
        builder.zero_lc(),
        builder.zero_lc(),
        LinearCombination(vec![(Fr::one(), out_var), (-Fr::one(), Variable::One)]),
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fr_fits_in_bits_small_values() {
        assert!(fr_fits_in_bits(&Fr::from(0u64), 1));
        assert!(fr_fits_in_bits(&Fr::from(1u64), 1));
        assert!(!fr_fits_in_bits(&Fr::from(2u64), 1));
        assert!(fr_fits_in_bits(&Fr::from(255u64), 8));
        assert!(!fr_fits_in_bits(&Fr::from(256u64), 8));
        assert!(fr_fits_in_bits(&Fr::from(0xFFFF_FFFFu64), 32));
        assert!(!fr_fits_in_bits(&Fr::from(0x1_0000_0000u64), 32));
    }

    #[test]
    fn fr_fits_in_bits_non_byte_aligned() {
        // Bit 0..6 set, bit 7 clear → fits in 7 bits.
        assert!(fr_fits_in_bits(&Fr::from(0x7Fu64), 7));
        assert!(!fr_fits_in_bits(&Fr::from(0x80u64), 7));
        // Bit 12 set → fits in 13, not 12.
        assert!(fr_fits_in_bits(&Fr::from(0x1000u64), 13));
        assert!(!fr_fits_in_bits(&Fr::from(0x1000u64), 12));
    }

    #[test]
    fn function_input_const_value_returns_some_for_constants() {
        let fi: FunctionInput<FieldElement> = FunctionInput::Constant(FieldElement::from(42u128));
        assert_eq!(function_input_const_value(&fi), Some(Fr::from(42u64)));
    }

    #[test]
    fn function_input_const_value_returns_none_for_witness() {
        let fi: FunctionInput<FieldElement> =
            FunctionInput::Witness(acir::native_types::Witness(7));
        assert_eq!(function_input_const_value(&fi), None);
    }
}
