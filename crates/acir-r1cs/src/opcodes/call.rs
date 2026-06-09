//! Cross-circuit `Opcode::Call` lowering.
//!
//! Strategy: inline the callee circuit's opcodes into the caller's
//! `ConstraintSystem`, rewriting every callee `Witness` index by adding a
//! per-call offset so the callee's namespace never collides with the
//! caller's. The callee's witness values come from a separate entry in the
//! parsed `WitnessStack` (see [`crate::witness::WitnessMap::callee_witnesses`]).
//!
//! ## Aliasing
//!
//! For each call, we add an aliasing constraint per input/output:
//! * `caller_input_var == shifted_callee_param_var` for each
//!   `callee.public_parameters` ↔ `caller_inputs` pair.
//! * `caller_output_var == shifted_callee_return_var` for each
//!   `callee.return_values` ↔ `caller_outputs` pair.
//!
//! Both are emitted as a single linear constraint of the form
//! `0 * 0 = lhs_var - rhs_var`.
//!
//! ## Predicate
//!
//! Both unconditional and predicated calls are supported. When the predicate
//! is the constant `1` (the common case) the call is inlined directly; for a
//! non-trivial predicate, `lower.rs` materialises it, range-checks it to
//! `{0,1}`, combines it with any outer call-site predicate, and gates every
//! constraint the callee emits via the builder's auxiliary-error predicate
//! mechanism (see [`crate::r1cs_builder::R1csBuilder::push_predicate`]).
//!
//! ## Recursion
//!
//! Nested calls (a callee that itself contains `Opcode::Call`) are
//! supported: `shift_opcode` properly rewrites the inner call's
//! `inputs`/`outputs` witnesses, and the dispatch loop in `lower.rs`
//! recurses on `Opcode::Call`. Each call site (top-level or nested) grabs
//! a fresh, disjoint witness-index range from
//! [`R1csBuilder::alloc_call_offset`], so independent invocations can never
//! alias each other.

use acir::FieldElement;
use acir::circuit::brillig::BrilligOutputs;
use acir::circuit::opcodes::{BlackBoxFuncCall, BlockId, FunctionInput};
use acir::circuit::{Circuit, Opcode};
use acir::native_types::{Expression, Witness};
use ark_bn254::Fr;
use ark_ff::One;
use ark_relations::gr1cs::LinearCombination;
use std::collections::BTreeMap;

use crate::artifact::WitnessIndex;
use crate::error::BackendError;
use crate::field::noir_field_to_fr;
use crate::r1cs_builder::R1csBuilder;
#[cfg(test)]
use crate::witness::CALLEE_NAMESPACE_STRIDE;

/// Predicate test: returns `true` iff `expr` is the constant 1.
pub fn predicate_is_one(predicate: &Expression<FieldElement>) -> bool {
    predicate.mul_terms.is_empty()
        && predicate.linear_combinations.is_empty()
        && noir_field_to_fr(&predicate.q_c) == Fr::one()
}

/// Legacy slot-keyed offset (kept for tests that exercise the shifting
/// logic in isolation). The production lowering uses
/// [`crate::r1cs_builder::R1csBuilder::alloc_call_offset`] instead so that
/// nested invocations get fresh, disjoint ranges from a running counter.
#[cfg(test)]
pub fn call_offset(slot: u32) -> u32 {
    CALLEE_NAMESPACE_STRIDE.saturating_mul(slot + 1)
}

/// Apply `+offset` to every `Witness` index inside `opcode`. Returns a fresh
/// `Opcode` with the shifted indices; the original is left untouched.
pub fn shift_opcode(op: &Opcode<FieldElement>, offset: u32) -> Opcode<FieldElement> {
    match op {
        Opcode::AssertZero(expr) => Opcode::AssertZero(shift_expression(expr, offset)),
        Opcode::BlackBoxFuncCall(bb) => Opcode::BlackBoxFuncCall(shift_blackbox(bb, offset)),
        Opcode::MemoryOp { block_id, op } => {
            let mut shifted = op.clone();
            shifted.index = shift_witness(op.index, offset);
            shifted.value = shift_witness(op.value, offset);
            Opcode::MemoryOp {
                block_id: shift_block_id(*block_id, offset),
                op: shifted,
            }
        }
        Opcode::MemoryInit {
            block_id,
            init,
            block_type,
        } => Opcode::MemoryInit {
            block_id: shift_block_id(*block_id, offset),
            init: init.iter().map(|w| shift_witness(*w, offset)).collect(),
            block_type: block_type.clone(),
        },
        Opcode::BrilligCall {
            id,
            inputs,
            outputs,
            predicate,
        } => Opcode::BrilligCall {
            id: *id,
            inputs: inputs.clone(),
            outputs: outputs
                .iter()
                .map(|o| shift_brillig_output(o, offset))
                .collect(),
            predicate: shift_expression(predicate, offset),
        },
        Opcode::Call {
            id,
            inputs,
            outputs,
            predicate,
        } => Opcode::Call {
            id: *id,
            inputs: inputs.iter().map(|w| shift_witness(*w, offset)).collect(),
            outputs: outputs.iter().map(|w| shift_witness(*w, offset)).collect(),
            predicate: shift_expression(predicate, offset),
        },
    }
}

fn shift_witness(w: Witness, offset: u32) -> Witness {
    Witness(w.0.saturating_add(offset))
}

/// Shift a `BlockId` by the same per-call offset used for witnesses. Callee
/// memory blocks live in a disjoint id range from the caller's so that
/// memory inside helper functions doesn't collide with memory at the call
/// site. The id space is u32; with `CALLEE_NAMESPACE_STRIDE = 2^24` we get
/// 255 nested-callee namespaces, far more than any real Noir program needs.
fn shift_block_id(b: BlockId, offset: u32) -> BlockId {
    BlockId(b.0.saturating_add(offset))
}

fn shift_function_input(
    fi: &FunctionInput<FieldElement>,
    offset: u32,
) -> FunctionInput<FieldElement> {
    match fi {
        FunctionInput::Witness(w) => FunctionInput::Witness(shift_witness(*w, offset)),
        FunctionInput::Constant(c) => FunctionInput::Constant(*c),
    }
}

fn shift_expression(expr: &Expression<FieldElement>, offset: u32) -> Expression<FieldElement> {
    let mut new_expr = Expression {
        q_c: expr.q_c,
        ..Default::default()
    };
    for (c, l, r) in &expr.mul_terms {
        new_expr
            .mul_terms
            .push((*c, shift_witness(*l, offset), shift_witness(*r, offset)));
    }
    for (c, w) in &expr.linear_combinations {
        new_expr
            .linear_combinations
            .push((*c, shift_witness(*w, offset)));
    }
    new_expr
}

fn shift_brillig_output(out: &BrilligOutputs, offset: u32) -> BrilligOutputs {
    match out {
        BrilligOutputs::Simple(w) => BrilligOutputs::Simple(shift_witness(*w, offset)),
        BrilligOutputs::Array(ws) => {
            BrilligOutputs::Array(ws.iter().map(|w| shift_witness(*w, offset)).collect())
        }
    }
}

fn shift_blackbox(
    bb: &BlackBoxFuncCall<FieldElement>,
    offset: u32,
) -> BlackBoxFuncCall<FieldElement> {
    use BlackBoxFuncCall::*;
    match bb {
        RANGE { input, num_bits } => RANGE {
            input: shift_function_input(input, offset),
            num_bits: *num_bits,
        },
        AND {
            lhs,
            rhs,
            num_bits,
            output,
        } => AND {
            lhs: shift_function_input(lhs, offset),
            rhs: shift_function_input(rhs, offset),
            num_bits: *num_bits,
            output: shift_witness(*output, offset),
        },
        XOR {
            lhs,
            rhs,
            num_bits,
            output,
        } => XOR {
            lhs: shift_function_input(lhs, offset),
            rhs: shift_function_input(rhs, offset),
            num_bits: *num_bits,
            output: shift_witness(*output, offset),
        },
        Sha256Compression {
            inputs,
            hash_values,
            outputs,
        } => Sha256Compression {
            inputs: Box::new(std::array::from_fn(|i| {
                shift_function_input(&inputs[i], offset)
            })),
            hash_values: Box::new(std::array::from_fn(|i| {
                shift_function_input(&hash_values[i], offset)
            })),
            outputs: Box::new(std::array::from_fn(|i| shift_witness(outputs[i], offset))),
        },
        Keccakf1600 { inputs, outputs } => Keccakf1600 {
            inputs: Box::new(std::array::from_fn(|i| {
                shift_function_input(&inputs[i], offset)
            })),
            outputs: Box::new(std::array::from_fn(|i| shift_witness(outputs[i], offset))),
        },
        Blake2s { inputs, outputs } => Blake2s {
            inputs: inputs
                .iter()
                .map(|i| shift_function_input(i, offset))
                .collect(),
            outputs: Box::new(std::array::from_fn(|i| shift_witness(outputs[i], offset))),
        },
        Blake3 { inputs, outputs } => Blake3 {
            inputs: inputs
                .iter()
                .map(|i| shift_function_input(i, offset))
                .collect(),
            outputs: Box::new(std::array::from_fn(|i| shift_witness(outputs[i], offset))),
        },
        Poseidon2Permutation { inputs, outputs } => Poseidon2Permutation {
            inputs: inputs
                .iter()
                .map(|i| shift_function_input(i, offset))
                .collect(),
            outputs: outputs.iter().map(|w| shift_witness(*w, offset)).collect(),
        },
        AES128Encrypt {
            inputs,
            iv,
            key,
            outputs,
        } => AES128Encrypt {
            inputs: inputs
                .iter()
                .map(|i| shift_function_input(i, offset))
                .collect(),
            iv: Box::new(std::array::from_fn(|i| {
                shift_function_input(&iv[i], offset)
            })),
            key: Box::new(std::array::from_fn(|i| {
                shift_function_input(&key[i], offset)
            })),
            outputs: outputs.iter().map(|w| shift_witness(*w, offset)).collect(),
        },
        EmbeddedCurveAdd {
            input1,
            input2,
            predicate,
            outputs,
        } => EmbeddedCurveAdd {
            // Inputs are now 2-element `[FunctionInput; 2]` arrays
            // (x, y) per point — `is_infinity` was removed in acir
            // v1.0.0-beta.22.
            input1: Box::new(std::array::from_fn(|i| {
                shift_function_input(&input1[i], offset)
            })),
            input2: Box::new(std::array::from_fn(|i| {
                shift_function_input(&input2[i], offset)
            })),
            predicate: shift_function_input(predicate, offset),
            outputs: (
                shift_witness(outputs.0, offset),
                shift_witness(outputs.1, offset),
            ),
        },
        MultiScalarMul {
            points,
            scalars,
            predicate,
            outputs,
        } => MultiScalarMul {
            points: points
                .iter()
                .map(|i| shift_function_input(i, offset))
                .collect(),
            scalars: scalars
                .iter()
                .map(|i| shift_function_input(i, offset))
                .collect(),
            predicate: shift_function_input(predicate, offset),
            outputs: (
                shift_witness(outputs.0, offset),
                shift_witness(outputs.1, offset),
            ),
        },
        // Variants we don't yet support: clone unchanged. The dispatch will
        // reject them upstream so witness-index shifting correctness here is
        // moot.
        other => other.clone(),
    }
}

/// Inject the callee's witness values (already shifted by `offset`) into the
/// builder's extra-witnesses pool, then add aliasing constraints between
/// caller inputs/outputs and the shifted callee parameter/return witnesses.
/// Returns the rewritten `Vec<Opcode<FieldElement>>` ready to be fed through
/// the existing dispatch loop.
pub fn prepare_call(
    builder: &mut R1csBuilder<'_>,
    callee: &Circuit<FieldElement>,
    callee_witness: Option<&BTreeMap<WitnessIndex, Fr>>,
    inputs: &[Witness],
    outputs: &[Witness],
    offset: u32,
    opcode_index: usize,
) -> Result<Vec<Opcode<FieldElement>>, BackendError> {
    // Noir convention: a `Call`'s `inputs` are bound to the callee's
    // `private_parameters` (the helper's signature inputs); `outputs` are
    // bound to the callee's `return_values`. Helpers don't have
    // `public_parameters` from the verifier's view — that set is always
    // empty for callees.
    let callee_params: Vec<Witness> = callee.private_parameters.iter().copied().collect();
    let callee_returns: Vec<Witness> = callee.return_values.0.iter().copied().collect();
    if callee_params.len() != inputs.len() {
        return Err(BackendError::ArtifactParse(format!(
            "Call opcode at index {opcode_index}: caller passed {} inputs but callee declares {} private parameters",
            inputs.len(),
            callee_params.len(),
        )));
    }
    if callee_returns.len() != outputs.len() {
        return Err(BackendError::ArtifactParse(format!(
            "Call opcode at index {opcode_index}: callee declares {} return values but caller expects {}",
            callee_returns.len(),
            outputs.len(),
        )));
    }

    if let Some(cw) = callee_witness {
        let injected: Vec<(WitnessIndex, Fr)> = cw
            .iter()
            .map(|(idx, v)| (WitnessIndex(idx.0.saturating_add(offset)), *v))
            .collect();
        builder.inject_witnesses(injected);
    }

    for (caller_in, callee_param) in inputs.iter().zip(callee_params.iter()) {
        let cw = WitnessIndex::from_witness(*caller_in);
        let pw = WitnessIndex(callee_param.0.saturating_add(offset));
        alias(builder, cw, pw)?;
    }
    for (caller_out, callee_ret) in outputs.iter().zip(callee_returns.iter()) {
        let cw = WitnessIndex::from_witness(*caller_out);
        let pw = WitnessIndex(callee_ret.0.saturating_add(offset));
        alias(builder, cw, pw)?;
    }

    let mut shifted = Vec::with_capacity(callee.opcodes.len());
    for op in callee.opcodes.iter() {
        shifted.push(shift_opcode(op, offset));
    }
    Ok(shifted)
}

fn alias(
    builder: &mut R1csBuilder<'_>,
    lhs: WitnessIndex,
    rhs: WitnessIndex,
) -> Result<(), BackendError> {
    let lhs_var = builder
        .alloc_witness(lhs)
        .map_err(|_| BackendError::ConstraintUnsatisfied {
            detail: format!(
                "Call lowering: failed to allocate caller witness w{}",
                lhs.0
            ),
        })?;
    let rhs_var = builder
        .alloc_witness(rhs)
        .map_err(|_| BackendError::ConstraintUnsatisfied {
            detail: format!(
                "Call lowering: failed to allocate callee witness w{}",
                rhs.0
            ),
        })?;
    builder
        .enforce(
            builder.zero_lc(),
            builder.zero_lc(),
            LinearCombination(vec![(Fr::one(), lhs_var), (-Fr::one(), rhs_var)]),
        )
        .map_err(|_| BackendError::ConstraintUnsatisfied {
            detail: format!(
                "Call lowering: failed to enforce alias w{} == w{}",
                lhs.0, rhs.0
            ),
        })?;
    Ok(())
}
