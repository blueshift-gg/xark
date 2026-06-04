//! ACIR -> R1CS lowering.
//!
//! Public input ordering is fixed by [`NoirArtifact::public_inputs`] and
//! enforced here: public input variables are allocated first, in that exact
//! order, before any opcode is touched.

use std::collections::{BTreeMap, HashMap};

use acir::circuit::opcodes::BlockId;
use acir::AcirField;
use acir::circuit::{Opcode, Program};
use acir::native_types::Expression;
use acir::FieldElement;
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_relations::r1cs::{ConstraintSystemRef, LinearCombination, SynthesisError, Variable};
use sha2::{Digest, Sha256};

use crate::artifact::{NoirArtifact, WitnessIndex};
use crate::error::BackendError;
use crate::field::noir_field_to_fr;
use crate::gadgets::boolean::enforce_boolean;
use crate::opcodes::{classify, memory as memory_lower, unsupported::unsupported_error};
use crate::r1cs_builder::R1csBuilder;
use crate::witness::WitnessMap;
use crate::{CURVE, LOWERING_VERSION, PROVING_SYSTEM};

/// A Noir artifact whose opcodes have been checked for backend support, and
/// which can be synthesized into an Arkworks `ConstraintSystem`.
#[derive(Clone)]
pub struct LoweredAcirCircuit {
    pub artifact: NoirArtifact,
    /// Cached count of mul-term auxiliary constraints we'd emit (handy for the
    /// inspect command and for sanity-checking against the actual CS after
    /// synthesis).
    pub estimated_constraints: usize,
}

impl LoweredAcirCircuit {
    /// Build a lowered circuit from a parsed artifact. This eagerly rejects
    /// unsupported opcodes so callers don't pay setup cost on a circuit that
    /// would have failed anyway.
    pub fn new(artifact: NoirArtifact) -> Result<Self, BackendError> {
        for (i, op) in artifact.opcodes().iter().enumerate() {
            let class = classify(op);
            if !class.is_supported() {
                return Err(unsupported_error(i, op));
            }
        }
        let estimated_constraints = estimate_constraints(artifact.opcodes());
        let lowered = Self {
            artifact,
            estimated_constraints,
        };
        // Memory ops pass the classify-time gate unconditionally, but the
        // *variable-index* rejection lives in the lowering pass (it requires
        // walking the AssertZero stream to detect pinned-constant indices).
        // Run the memory-only pre-flight now so users get the rich
        // "see ROADMAP WS-C.5" error at `setup` / `inspect` time rather than
        // a `SynthesisError::Unsatisfiable` deep inside `prove`.
        lowered.check_memory_support()?;
        // AND/XOR opcodes carry a `num_bits` field that is unconstrained at
        // the ACIR level but capped at `WORDN_MAX_BITS` (= 64) by the gadget.
        // Surface oversized widths as a clean setup-time error rather than a
        // panic inside the lowering closure.
        lowered.check_bitwise_widths()?;
        Ok(lowered)
    }

    /// Walk the opcode stream and reject any AND/XOR black-box call whose
    /// `num_bits` exceeds the gadget's supported width
    /// ([`crate::gadgets::bitwise::WORDN_MAX_BITS`]). Returns an
    /// [`BackendError::UnsupportedOpcode`] with the same shape as the generic
    /// classification path so users get one error format regardless of why an
    /// opcode is unsupported.
    pub fn check_bitwise_widths(&self) -> Result<(), BackendError> {
        use acir::circuit::opcodes::BlackBoxFuncCall;
        use crate::gadgets::bitwise::WORDN_MAX_BITS;
        for (i, op) in self.artifact.opcodes().iter().enumerate() {
            if let Opcode::BlackBoxFuncCall(bb) = op {
                let (kind, num_bits) = match bb {
                    BlackBoxFuncCall::AND { num_bits, .. } => ("AND", *num_bits),
                    BlackBoxFuncCall::XOR { num_bits, .. } => ("XOR", *num_bits),
                    _ => continue,
                };
                let n = num_bits as usize;
                if !(1..=WORDN_MAX_BITS).contains(&n) {
                    return Err(BackendError::UnsupportedOpcode {
                        opcode: format!("BlackBoxFuncCall::{kind}"),
                        index: i,
                        help: format!(
                            "BlackBoxFuncCall::{kind} with num_bits={n} is outside the supported \
                             range [1, {WORDN_MAX_BITS}].\n\n\
                             Noir 1.0.0-beta.21 emits AND/XOR only for u8/u16/u32/u64 operands; \
                             wider integer types are decomposed at the source level before \
                             reaching ACIR. If you have produced an artifact that violates this, \
                             you are probably on a newer Noir version — file an issue with the \
                             artifact and we will widen the gadget. See ROADMAP step WS-B.1."
                        ),
                    });
                }
            }
        }
        Ok(())
    }

    /// Lower the circuit into an Arkworks constraint system. `witness` must be
    /// `Some` for proving and `None` for setup.
    pub fn synthesize(
        &self,
        cs: ConstraintSystemRef<Fr>,
        witness: Option<&WitnessMap<Fr>>,
    ) -> Result<(), SynthesisError> {
        let mut builder = R1csBuilder::new(cs, witness);

        // 1) Allocate public inputs first, in declaration order.
        for idx in &self.artifact.public_inputs {
            builder.alloc_public(*idx)?;
        }
        builder.finish_public_pass();

        // 1b) Pre-pass: detect witnesses pinned to constants by a trivial
        //     `AssertZero` of the shape `coeff * w + q_c = 0`. Constant-index
        //     `MemoryOp` lowering uses this map to recognise when an op's
        //     index witness is actually a compile-time constant. See
        //     `docs/memory.md` and ROADMAP step WS-C.4. The map is mutable so
        //     that Call inlining can splice in callee-scope pins discovered
        //     from shifted callee opcodes.
        let mut pinned_constants =
            memory_lower::extract_pinned_constants(self.artifact.opcodes());
        // Shadow of declared memory blocks: maps each `BlockId` to the
        // per-slot witness indices currently stored. `MemoryInit` populates
        // it; constant-index `MemoryOp[write]` updates it in-place. Shared
        // across the whole circuit (including inlined callees) — block ids
        // inside a callee are shifted to a disjoint range by `shift_opcode`
        // so collisions are impossible.
        let mut memory_blocks: HashMap<BlockId, Vec<memory_lower::ShadowEntry>> = HashMap::new();

        // 2) Lower every opcode. Anything not classified as supported was
        //    rejected at `new()` time, so the only opcodes we expect here are
        //    `AssertZero`, supported black-box calls (RANGE, Sha256Compression,
        //    bitwise, ...), `BrilligCall` (trust-outputs), and the memory
        //    opcodes.
        for (i, op) in self.artifact.opcodes().iter().enumerate() {
            self.lower_opcode(
                &mut builder,
                &mut memory_blocks,
                &mut pinned_constants,
                None,
                i,
                op,
            )?;
            tracing::trace!("lowered opcode {i}");
        }

        Ok(())
    }

    /// Dispatch a single opcode through its appropriate lowering arm. Shared
    /// between the top-level circuit and inlined callee bodies (B.5). The
    /// `predicate` parameter carries the combined call-site predicate: it is
    /// `None` at the top level (constraints always fire) and `Some(p)` inside
    /// a callee whose `Call`'s predicate is non-trivial (constraints are
    /// gated by `p`).
    fn lower_opcode(
        &self,
        builder: &mut R1csBuilder<'_>,
        memory_blocks: &mut HashMap<BlockId, Vec<memory_lower::ShadowEntry>>,
        pinned_constants: &mut BTreeMap<WitnessIndex, Fr>,
        predicate: Option<CallPredicate>,
        index: usize,
        op: &Opcode<FieldElement>,
    ) -> Result<(), SynthesisError> {
        // When a Call predicate is active, install it on the builder so the
        // universal e-aux gating in `R1csBuilder::enforce` automatically
        // gates every constraint emitted while dispatching this opcode —
        // including the per-gadget constraints inside `lower_black_box` and
        // the per-slot constraints inside `lower_memory_*`. Restored before
        // returning so a sibling opcode in the same callee body sees the
        // same gating state, and the top-level dispatcher sees `None`.
        let predicate_guard = predicate.map(|p| builder.push_predicate(p.var));
        let result = match op {
            Opcode::AssertZero(expr) => {
                // AssertZero is lowered with explicit gating (rather than
                // routing through the builder-level e-aux trick) so that the
                // common ungated 0-mul and 1-mul fast paths stay cheap. The
                // gated path inside `lower_assert_zero_gated` mirrors the
                // same `p · combined = 0` shape the e-aux trick would
                // produce but skips the extra aux per constraint. Suspend
                // the builder's predicate during the call so the universal
                // gating doesn't add a second layer.
                let saved = builder.take_predicate();
                let r = lower_assert_zero_gated(builder, expr, predicate.map(|p| p.var));
                builder.restore_predicate(saved);
                r
            }
            Opcode::BlackBoxFuncCall(bb) => {
                crate::opcodes::blackbox::lower_black_box(builder, bb)
            }
            Opcode::BrilligCall { outputs, .. } => {
                // Trust-outputs strategy: allocate the declared output
                // witnesses (so they're pinned in the constraint system) and
                // rely on the surrounding `AssertZero` opcodes to constrain
                // their values. When those `AssertZero` opcodes are gated by
                // a non-trivial predicate, the Brillig outputs are
                // free-witnesses at p=0 — which is exactly what we want for
                // a conditionally-emitted hint.
                crate::opcodes::brillig::lower_brillig_call(builder, outputs)
            }
            Opcode::MemoryInit {
                block_id,
                init,
                block_type,
            } => memory_lower::lower_memory_init(
                builder,
                memory_blocks,
                index,
                *block_id,
                init,
                block_type,
            )
            .map_err(backend_to_synthesis),
            Opcode::MemoryOp { block_id, op, .. } => memory_lower::lower_memory_op(
                builder,
                pinned_constants,
                memory_blocks,
                index,
                *block_id,
                op,
            )
            .map_err(backend_to_synthesis),
            Opcode::Call {
                id,
                inputs,
                outputs,
                predicate: call_pred,
            } => self.lower_call_at(
                builder,
                memory_blocks,
                pinned_constants,
                predicate,
                index,
                *id,
                inputs,
                outputs,
                call_pred,
            ),
        };
        if let Some(previous) = predicate_guard {
            builder.restore_predicate(previous);
        }
        result
    }

    /// Lower a `Call` opcode by inlining the callee with witness-index
    /// shifting (ROADMAP step WS-B.5). Recurses on nested `Opcode::Call`
    /// inside the callee. Handles predicated calls by gating every callee
    /// `AssertZero` by the combined predicate; rejects BlackBox/Memory
    /// opcodes under a non-trivial predicate (per-gadget predicate threading
    /// is out of scope — see the soundness note in the function body).
    #[allow(clippy::too_many_arguments)]
    fn lower_call_at(
        &self,
        builder: &mut R1csBuilder<'_>,
        memory_blocks: &mut HashMap<BlockId, Vec<memory_lower::ShadowEntry>>,
        pinned_constants: &mut BTreeMap<WitnessIndex, Fr>,
        parent_predicate: Option<CallPredicate>,
        opcode_index: usize,
        callee_id: acir::circuit::opcodes::AcirFunctionId,
        inputs: &[acir::native_types::Witness],
        outputs: &[acir::native_types::Witness],
        predicate: &acir::native_types::Expression<acir::FieldElement>,
    ) -> Result<(), SynthesisError> {
        use crate::opcodes::call;
        // Look up the callee circuit.
        let callee_idx = callee_id.0 as usize;
        if callee_idx >= self.artifact.program.functions.len() {
            tracing::error!("Call opcode at index {opcode_index} references function id {callee_idx} but program has {} functions", self.artifact.program.functions.len());
            return Err(SynthesisError::Unsatisfiable);
        }
        let callee_circuit = &self.artifact.program.functions[callee_idx];
        // Grab a fresh per-call witness/block-id offset. This is allocated
        // from a running counter on the builder, so siblings *and* nested
        // invocations all get disjoint witness-index ranges (and disjoint
        // memory-block id ranges, since `shift_opcode` shifts both) without
        // collision.
        let offset = builder.alloc_call_offset()?;

        // Resolve the call's predicate to a Variable. `None` if the call is
        // unconditional (predicate Expression evaluates to constant 1) — the
        // common case in production Noir output today. Otherwise we
        // materialise the predicate, range-check it to {0,1}, and combine it
        // with any outer call-site predicate.
        let call_predicate = if call::predicate_is_one(predicate) {
            None
        } else {
            Some(materialize_predicate(builder, predicate)?)
        };
        let combined_predicate =
            combine_predicates(builder, parent_predicate, call_predicate)?;

        // Pull the callee's witness map (if proving). In setup mode the
        // builder has no witness, so we pass None and rely on alloc_witness
        // not invoking value closures.
        let callee_witness = builder.callee_witness_map(callee_id.0).cloned();

        let shifted = call::prepare_call(
            builder,
            callee_circuit,
            callee_witness.as_ref(),
            inputs,
            outputs,
            offset,
            opcode_index,
        )
        .map_err(backend_to_synthesis)?;

        // Splice in any callee-scope constant pins so MemoryOp inside the
        // callee can detect constant indices the same way the top-level pass
        // does. Pins use shifted witness indices (callee opcodes were just
        // rewritten), so they live in the same namespace as the rest of the
        // builder.
        for (idx, value) in memory_lower::extract_pinned_constants(&shifted) {
            pinned_constants.entry(idx).or_insert(value);
        }

        for (j, op) in shifted.iter().enumerate() {
            self.lower_opcode(
                builder,
                memory_blocks,
                pinned_constants,
                combined_predicate,
                j,
                op,
            )?;
        }
        Ok(())
    }

    /// Walk the opcode stream and return the first `BackendError` raised by
    /// memory lowering (constant-index detection failures, databus blocks,
    /// out-of-bounds constants, ...). Useful for surfacing memory errors at
    /// `setup` time without running the full Arkworks synthesis dance.
    pub fn check_memory_support(&self) -> Result<(), BackendError> {
        let pinned_constants = memory_lower::extract_pinned_constants(self.artifact.opcodes());
        let mut memory_blocks: HashMap<BlockId, Vec<memory_lower::ShadowEntry>> = HashMap::new();
        for (i, op) in self.artifact.opcodes().iter().enumerate() {
            match op {
                Opcode::MemoryInit {
                    block_id,
                    init,
                    block_type,
                } => {
                    // We pass a throwaway builder reference via a fresh
                    // constraint system so the helper's signature lines up,
                    // but the init lowering does not actually touch the
                    // builder beyond reading the block id / witnesses.
                    let cs = ark_relations::r1cs::ConstraintSystem::<Fr>::new_ref();
                    cs.set_mode(ark_relations::r1cs::SynthesisMode::Setup);
                    let mut builder = R1csBuilder::new(cs, None);
                    memory_lower::lower_memory_init(
                        &mut builder,
                        &mut memory_blocks,
                        i,
                        *block_id,
                        init,
                        block_type,
                    )?;
                }
                Opcode::MemoryOp { block_id, op, .. } => {
                    // Likewise — we only need the constant-index detection
                    // half of `lower_memory_op` to fire its error if the op
                    // is variable-index. Allocating witnesses against a
                    // throwaway builder is cheap.
                    let cs = ark_relations::r1cs::ConstraintSystem::<Fr>::new_ref();
                    cs.set_mode(ark_relations::r1cs::SynthesisMode::Setup);
                    let mut builder = R1csBuilder::new(cs, None);
                    builder.finish_public_pass();
                    memory_lower::lower_memory_op(
                        &mut builder,
                        &pinned_constants,
                        &mut memory_blocks,
                        i,
                        *block_id,
                        op,
                    )?;
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Number of public input wires the verifier will see.
    pub fn num_public_inputs(&self) -> usize {
        self.artifact.public_inputs.len()
    }

    /// Deterministic hash binding circuit identity, lowering version, curve,
    /// and proving system. Used for `metadata.json`.
    pub fn circuit_hash(&self) -> String {
        let mut h = Sha256::new();
        h.update(b"xark-circuit-v1");
        h.update(LOWERING_VERSION.to_be_bytes());
        h.update(CURVE.as_bytes());
        h.update([0u8]);
        h.update(PROVING_SYSTEM.as_bytes());
        h.update([0u8]);
        h.update(self.artifact.metadata.noir_version.as_bytes());
        h.update([0u8]);
        // Public input order is part of identity.
        h.update((self.artifact.public_inputs.len() as u32).to_be_bytes());
        for w in &self.artifact.public_inputs {
            h.update(w.0.to_be_bytes());
        }
        // Canonical msgpack-compact bytes for the ACIR program. This is the
        // same gzip-compressed format Noir writes to disk
        // (`Program::serialize_program`), so it's stable across `Display`
        // formatting changes in the `acir` crate.
        let program_bytes = Program::serialize_program(&self.artifact.program);
        h.update((program_bytes.len() as u64).to_be_bytes());
        h.update(&program_bytes);
        hex::encode(h.finalize())
    }
}

/// Build a [`LoweredAcirCircuit`] from a [`NoirArtifact`]. Convenience wrapper.
pub fn lower_program(artifact: NoirArtifact) -> Result<LoweredAcirCircuit, BackendError> {
    LoweredAcirCircuit::new(artifact)
}

/// Compute a rough lower bound on the number of R1CS constraints the circuit
/// will produce. One per `AssertZero`, plus one auxiliary `t_i = a_i * b_i`
/// per multiplication term beyond the first in any expression with >1 mul
/// terms.
pub fn estimate_constraints(opcodes: &[Opcode<FieldElement>]) -> usize {
    let mut total = 0usize;
    for op in opcodes {
        if let Opcode::AssertZero(expr) = op {
            total += 1;
            if expr.mul_terms.len() > 1 {
                total += expr.mul_terms.len();
            }
        }
    }
    total
}

/// Map a `BackendError` from a lowering helper into the `SynthesisError`
/// shape that Arkworks' `ConstraintSynthesizer` requires. The richer error
/// is surfaced separately at `setup` time via `check_memory_support`; this
/// path collapses to `Unsatisfiable` so we don't lose the constraint
/// failure during proving.
fn backend_to_synthesis(err: BackendError) -> SynthesisError {
    tracing::debug!("memory lowering error during synthesize: {err}");
    SynthesisError::Unsatisfiable
}

/// Lower an `AssertZero(expr)` opcode, optionally gated by a predicate
/// `Variable`. When `predicate` is `None`, the ungated constraint
/// `expr == 0` is emitted (matching the fast paths from the original
/// implementation: 0-mul → linear, 1-mul → a*(coeff*b)=-(linear+q_c),
/// many-mul → aux + linear). When `predicate` is `Some(p)`, every mul term
/// is materialised as an aux variable `t_i = a_i * b_i` and the constraint
/// `p * (Σ coeff_i · t_i + linear + q_c) = 0` is emitted as a single R1CS
/// row. The cost is one extra mul aux per mul term (vs. ungated 0-mul or
/// 1-mul cases) plus one gating constraint per AssertZero — independent of
/// the gadget's internal shape, so any opcode whose lowering reduces to a
/// stream of AssertZeros can be predicated uniformly. (See ROADMAP step
/// WS-B.5 follow-up for non-trivial-predicate Call support.)
fn lower_assert_zero_gated(
    builder: &mut R1csBuilder,
    expr: &Expression<FieldElement>,
    predicate: Option<Variable>,
) -> Result<(), SynthesisError> {
    let q_c = noir_field_to_fr(&expr.q_c);
    let linear = build_linear_lc(builder, &expr.linear_combinations, q_c)?;

    if let Some(p) = predicate {
        // Gated path: materialise every mul term as aux, build the full
        // LC, then enforce `p * combined = 0`.
        let mut combined = linear;
        for (coeff, lhs, rhs) in &expr.mul_terms {
            let coeff_fr = noir_field_to_fr(coeff);
            let a_idx = WitnessIndex::from_witness(*lhs);
            let b_idx = WitnessIndex::from_witness(*rhs);
            let a = builder.alloc_witness(a_idx)?;
            let b = builder.alloc_witness(b_idx)?;
            let value_fn: Box<dyn FnOnce() -> Result<Fr, SynthesisError>> = {
                let snap = builder.witness_value_snapshot(a_idx, b_idx);
                Box::new(move || {
                    let (av, bv) = snap?;
                    Ok(av * bv)
                })
            };
            let t = builder.alloc_aux(value_fn)?;
            let a_lc = LinearCombination::from((Fr::one(), a));
            let b_lc = LinearCombination::from((Fr::one(), b));
            let t_lc = LinearCombination::from((Fr::one(), t));
            builder.enforce(a_lc, b_lc, t_lc)?;
            combined = add_lc(&combined, &LinearCombination::from((coeff_fr, t)));
        }
        let p_lc = LinearCombination::from((Fr::one(), p));
        builder.enforce(p_lc, combined, builder.zero_lc())?;
        return Ok(());
    }

    match expr.mul_terms.len() {
        0 => {
            // 0 * 0 = -(linear + q_c)
            // Equivalent to enforcing `linear + q_c = 0`.
            builder.enforce(builder.zero_lc(), builder.zero_lc(), neg_lc(&linear))?;
        }
        1 => {
            let (coeff, lhs, rhs) = &expr.mul_terms[0];
            let coeff_fr = noir_field_to_fr(coeff);
            let a = builder.alloc_witness(WitnessIndex::from_witness(*lhs))?;
            let b = builder.alloc_witness(WitnessIndex::from_witness(*rhs))?;
            // a * (coeff * b) = -(linear + q_c)
            let a_lc = LinearCombination::from((Fr::one(), a));
            let b_lc = LinearCombination::from((coeff_fr, b));
            builder.enforce(a_lc, b_lc, neg_lc(&linear))?;
        }
        _ => {
            // For each mul term `coeff * a * b`, allocate `t = a * b` and
            // enforce `a * b = t`. Then enforce
            // `sum_i(coeff_i * t_i) + linear + q_c = 0`.
            let mut combined = linear;
            for (coeff, lhs, rhs) in &expr.mul_terms {
                let coeff_fr = noir_field_to_fr(coeff);
                let a_idx = WitnessIndex::from_witness(*lhs);
                let b_idx = WitnessIndex::from_witness(*rhs);
                let a = builder.alloc_witness(a_idx)?;
                let b = builder.alloc_witness(b_idx)?;

                // Capture witness once so the proving-time closure doesn't
                // need to re-borrow the builder.
                let value_fn: Box<dyn FnOnce() -> Result<Fr, SynthesisError>> = {
                    let snap = builder.witness_value_snapshot(a_idx, b_idx);
                    Box::new(move || {
                        let (av, bv) = snap?;
                        Ok(av * bv)
                    })
                };
                let t = builder.alloc_aux(value_fn)?;
                let a_lc = LinearCombination::from((Fr::one(), a));
                let b_lc = LinearCombination::from((Fr::one(), b));
                let t_lc = LinearCombination::from((Fr::one(), t));
                builder.enforce(a_lc, b_lc, t_lc)?;

                combined = add_lc(&combined, &LinearCombination::from((coeff_fr, t)));
            }
            // Enforce `combined = 0`.
            builder.enforce(builder.zero_lc(), builder.zero_lc(), neg_lc(&combined))?;
        }
    }
    Ok(())
}

/// Materialised call-site predicate: the Arkworks `Variable` constrained to
/// the predicate Expression's value plus the proving-time `Fr` value (or
/// `None` in setup mode). Carrying the value alongside the Variable lets
/// `combine_predicates` compute `p_outer · p_inner` natively without needing
/// to read the constraint system's internal witness assignments.
#[derive(Clone, Copy)]
struct CallPredicate {
    var: Variable,
    value: Option<Fr>,
}

/// Resolve a Call opcode's `predicate` Expression to a [`CallPredicate`]
/// whose `Variable` is constrained boolean. Hot path: `predicate == 1 * w`
/// reuses the witness variable directly. General case: materialise the
/// Expression's value as an aux witness, link it to the Expression with a
/// single linear constraint, and add a `p * (1 - p) = 0` range check so a
/// malicious prover can't disable constraints by passing a fractional p.
fn materialize_predicate(
    builder: &mut R1csBuilder<'_>,
    predicate: &Expression<FieldElement>,
) -> Result<CallPredicate, SynthesisError> {
    // Fast path: predicate is exactly `1 * w` with `q_c == 0`. The
    // surrounding caller circuit has already constrained `w` to {0, 1} via
    // a RANGE or boolean opcode (this is Noir's emission contract for
    // conditional predicates), but we still re-enforce the boolean check
    // here so the gating is sound even if the assumption breaks.
    if predicate.mul_terms.is_empty()
        && predicate.linear_combinations.len() == 1
        && predicate.q_c.is_zero()
        && noir_field_to_fr(&predicate.linear_combinations[0].0) == Fr::one()
    {
        let w = predicate.linear_combinations[0].1;
        let w_idx = WitnessIndex::from_witness(w);
        let p = builder.alloc_witness(w_idx)?;
        let value = builder.maybe_witness_value(w_idx)?;
        enforce_boolean(builder, p)?;
        return Ok(CallPredicate { var: p, value });
    }

    // General path. Allocate mul-term auxes, build the full sum LC, and
    // enforce `expr - p = 0`.
    let mut mul_aux: Vec<(Fr, Variable)> = Vec::with_capacity(predicate.mul_terms.len());
    for (coeff, lhs, rhs) in &predicate.mul_terms {
        let coeff_fr = noir_field_to_fr(coeff);
        let a_idx = WitnessIndex::from_witness(*lhs);
        let b_idx = WitnessIndex::from_witness(*rhs);
        let a = builder.alloc_witness(a_idx)?;
        let b = builder.alloc_witness(b_idx)?;
        let value_fn: Box<dyn FnOnce() -> Result<Fr, SynthesisError>> = {
            let snap = builder.witness_value_snapshot(a_idx, b_idx);
            Box::new(move || {
                let (av, bv) = snap?;
                Ok(av * bv)
            })
        };
        let t = builder.alloc_aux(value_fn)?;
        builder.enforce(
            LinearCombination::from((Fr::one(), a)),
            LinearCombination::from((Fr::one(), b)),
            LinearCombination::from((Fr::one(), t)),
        )?;
        mul_aux.push((coeff_fr, t));
    }

    // Compute the predicate's proving-time value natively (or `None` in
    // setup mode), then allocate `p` carrying it.
    let p_value = evaluate_expression(builder, predicate)?;
    let p = builder.alloc_with_value(p_value)?;

    // Enforce expr - p = 0 as a single linear constraint.
    let mut sum_lc: Vec<(Fr, Variable)> = Vec::new();
    for (c, t) in &mul_aux {
        sum_lc.push((*c, *t));
    }
    for (c, w) in &predicate.linear_combinations {
        let c_fr = noir_field_to_fr(c);
        if c_fr.is_zero() {
            continue;
        }
        let v = builder.alloc_witness(WitnessIndex::from_witness(*w))?;
        sum_lc.push((c_fr, v));
    }
    let q_c_fr = noir_field_to_fr(&predicate.q_c);
    if !q_c_fr.is_zero() {
        sum_lc.push((q_c_fr, Variable::One));
    }
    sum_lc.push((-Fr::one(), p));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), LinearCombination(sum_lc))?;
    enforce_boolean(builder, p)?;
    Ok(CallPredicate {
        var: p,
        value: p_value,
    })
}

/// Evaluate an ACIR `Expression` against the builder's current witness
/// state. Returns `Ok(None)` in setup mode (no witness map present) and
/// `Ok(Some(value))` in proving mode. Returns
/// `Err(SynthesisError::AssignmentMissing)` only when a referenced witness
/// is absent from the proving-time witness map.
fn evaluate_expression(
    builder: &R1csBuilder<'_>,
    expr: &Expression<FieldElement>,
) -> Result<Option<Fr>, SynthesisError> {
    let mut acc = noir_field_to_fr(&expr.q_c);
    let mut have_values = true;
    for (coeff, lhs, rhs) in &expr.mul_terms {
        let av = builder.maybe_witness_value(WitnessIndex::from_witness(*lhs))?;
        let bv = builder.maybe_witness_value(WitnessIndex::from_witness(*rhs))?;
        match (av, bv) {
            (Some(a), Some(b)) => {
                acc += noir_field_to_fr(coeff) * a * b;
            }
            _ => {
                have_values = false;
                break;
            }
        }
    }
    if have_values {
        for (coeff, w) in &expr.linear_combinations {
            let v = builder.maybe_witness_value(WitnessIndex::from_witness(*w))?;
            match v {
                Some(val) => acc += noir_field_to_fr(coeff) * val,
                None => {
                    have_values = false;
                    break;
                }
            }
        }
    }
    if have_values {
        Ok(Some(acc))
    } else {
        Ok(None)
    }
}

/// Combine an outer call-site predicate with an inner one. `None`
/// represents the always-true predicate; `Some(p)` represents a boolean
/// gate. The combination is logical-AND, i.e. `p_outer · p_inner`, which is
/// naturally boolean (the product of two booleans is boolean), so no
/// additional range check is needed on the result.
fn combine_predicates(
    builder: &mut R1csBuilder<'_>,
    outer: Option<CallPredicate>,
    inner: Option<CallPredicate>,
) -> Result<Option<CallPredicate>, SynthesisError> {
    match (outer, inner) {
        (None, None) => Ok(None),
        (Some(p), None) | (None, Some(p)) => Ok(Some(p)),
        (Some(p1), Some(p2)) => {
            let value = match (p1.value, p2.value) {
                (Some(a), Some(b)) => Some(a * b),
                _ => None,
            };
            let v = builder.alloc_with_value(value)?;
            builder.enforce(
                LinearCombination::from((Fr::one(), p1.var)),
                LinearCombination::from((Fr::one(), p2.var)),
                LinearCombination::from((Fr::one(), v)),
            )?;
            Ok(Some(CallPredicate { var: v, value }))
        }
    }
}

fn build_linear_lc(
    builder: &mut R1csBuilder,
    terms: &[(FieldElement, acir::native_types::Witness)],
    q_c: Fr,
) -> Result<LinearCombination<Fr>, SynthesisError> {
    let mut lc = builder.const_lc(q_c);
    for (coeff, w) in terms {
        let coeff_fr = noir_field_to_fr(coeff);
        if coeff_fr.is_zero() {
            continue;
        }
        let v = builder.alloc_witness(WitnessIndex::from_witness(*w))?;
        lc = add_lc(&lc, &LinearCombination::from((coeff_fr, v)));
    }
    Ok(lc)
}

fn neg_lc(lc: &LinearCombination<Fr>) -> LinearCombination<Fr> {
    let mut out: Vec<(Fr, Variable)> = Vec::with_capacity(lc.0.len());
    for (coeff, var) in lc.0.iter() {
        out.push((-*coeff, *var));
    }
    LinearCombination(out)
}

fn add_lc(a: &LinearCombination<Fr>, b: &LinearCombination<Fr>) -> LinearCombination<Fr> {
    let mut out = a.clone();
    for (coeff, var) in b.0.iter() {
        out.0.push((*coeff, *var));
    }
    out
}

/// Public helper: opcode-coverage summary for `inspect`.
pub use crate::opcodes::summarize as summarize_opcodes;

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use acir::circuit::{Circuit, Program, PublicInputs};
    use acir::native_types::{Expression, Witness};
    use ark_relations::r1cs::ConstraintSystem;
    use std::collections::BTreeSet;

    use crate::artifact::{ArtifactMetadata, NoirArtifact};

    fn fe(n: i64) -> FieldElement {
        if n >= 0 {
            FieldElement::from(n as u128)
        } else {
            -FieldElement::from((-n) as u128)
        }
    }

    fn build_artifact(
        opcodes: Vec<Opcode<FieldElement>>,
        public: Vec<u32>,
        private: Vec<u32>,
    ) -> NoirArtifact {
        let mut public_set: BTreeSet<Witness> = BTreeSet::new();
        for p in &public {
            public_set.insert(Witness(*p));
        }
        let mut private_set: BTreeSet<Witness> = BTreeSet::new();
        for p in &private {
            private_set.insert(Witness(*p));
        }
        let circuit = Circuit {
            function_name: "main".to_string(),
            opcodes,
            private_parameters: private_set,
            public_parameters: PublicInputs(public_set),
            return_values: PublicInputs(BTreeSet::new()),
            assert_messages: vec![],
        };
        let program = Program {
            functions: vec![circuit],
            unconstrained_functions: vec![],
        };
        let public_inputs = public.into_iter().map(WitnessIndex).collect();
        // Walk opcodes to estimate witness count.
        let witness_count = program.functions[0]
            .opcodes
            .iter()
            .flat_map(|op| match op {
                Opcode::AssertZero(e) => {
                    let mut ids = vec![];
                    for (_, l, r) in &e.mul_terms {
                        ids.push(l.0);
                        ids.push(r.0);
                    }
                    for (_, w) in &e.linear_combinations {
                        ids.push(w.0);
                    }
                    ids
                }
                _ => vec![],
            })
            .max()
            .map(|m| (m as usize) + 1)
            .unwrap_or(0);
        NoirArtifact {
            circuit_name: "test".into(),
            program,
            public_inputs,
            witness_count,
            metadata: ArtifactMetadata {
                noir_version: "1.0.0-beta.21+test".into(),
                program_hash: "0".into(),
            },
        }
    }

    fn run(artifact: NoirArtifact, witness: Vec<(u32, Fr)>) -> ark_relations::r1cs::Result<bool> {
        let lowered = LoweredAcirCircuit::new(artifact).expect("lower");
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut map = WitnessMap::new();
        for (idx, v) in witness {
            map.insert(WitnessIndex(idx), v);
        }
        lowered.synthesize(cs.clone(), Some(&map))?;
        cs.is_satisfied()
    }

    fn fr(n: i64) -> Fr {
        if n >= 0 {
            Fr::from(n as u128)
        } else {
            -Fr::from((-n) as u128)
        }
    }

    /// `x + y = z` lowered as `x + y - z = 0`. Linear-only.
    #[test]
    fn x_plus_y_equals_z_satisfied() {
        let expr = Expression {
            mul_terms: vec![],
            linear_combinations: vec![
                (fe(1), Witness(1)),
                (fe(1), Witness(2)),
                (fe(-1), Witness(3)),
            ],
            q_c: fe(0),
        };
        let art = build_artifact(vec![Opcode::AssertZero(expr)], vec![3], vec![1, 2]);
        assert!(run(art, vec![(1, fr(2)), (2, fr(3)), (3, fr(5))]).unwrap());
    }

    #[test]
    fn x_plus_y_equals_z_unsatisfied() {
        let expr = Expression {
            mul_terms: vec![],
            linear_combinations: vec![
                (fe(1), Witness(1)),
                (fe(1), Witness(2)),
                (fe(-1), Witness(3)),
            ],
            q_c: fe(0),
        };
        let art = build_artifact(vec![Opcode::AssertZero(expr)], vec![3], vec![1, 2]);
        assert!(!run(art, vec![(1, fr(2)), (2, fr(3)), (3, fr(6))]).unwrap());
    }

    /// `x * y - z = 0`. Single mul term.
    #[test]
    fn x_times_y_equals_z_satisfied() {
        let expr = Expression {
            mul_terms: vec![(fe(1), Witness(1), Witness(2))],
            linear_combinations: vec![(fe(-1), Witness(3))],
            q_c: fe(0),
        };
        let art = build_artifact(vec![Opcode::AssertZero(expr)], vec![3], vec![1, 2]);
        assert!(run(art, vec![(1, fr(3)), (2, fr(4)), (3, fr(12))]).unwrap());
    }

    #[test]
    fn x_times_y_equals_z_unsatisfied() {
        let expr = Expression {
            mul_terms: vec![(fe(1), Witness(1), Witness(2))],
            linear_combinations: vec![(fe(-1), Witness(3))],
            q_c: fe(0),
        };
        let art = build_artifact(vec![Opcode::AssertZero(expr)], vec![3], vec![1, 2]);
        assert!(!run(art, vec![(1, fr(3)), (2, fr(4)), (3, fr(13))]).unwrap());
    }

    /// `x * x - y = 0` with `y` public. (Mirrors the arithmetic_square example.)
    #[test]
    fn square_equals_public() {
        // We use witness layout: w1 = x (private), w2 = y (public).
        let expr = Expression {
            mul_terms: vec![(fe(1), Witness(1), Witness(1))],
            linear_combinations: vec![(fe(-1), Witness(2))],
            q_c: fe(0),
        };
        let art = build_artifact(vec![Opcode::AssertZero(expr)], vec![2], vec![1]);
        assert!(run(art.clone(), vec![(1, fr(9)), (2, fr(81))]).unwrap());
        assert!(!run(art, vec![(1, fr(9)), (2, fr(82))]).unwrap());
    }

    /// `x * y + z - out = 0`. One mul + linears + zero constant.
    #[test]
    fn mul_plus_linear_satisfied() {
        let expr = Expression {
            mul_terms: vec![(fe(1), Witness(1), Witness(2))],
            linear_combinations: vec![(fe(1), Witness(3)), (fe(-1), Witness(4))],
            q_c: fe(0),
        };
        let art = build_artifact(vec![Opcode::AssertZero(expr)], vec![4], vec![1, 2, 3]);
        // 2 * 3 + 5 = 11
        assert!(run(art, vec![(1, fr(2)), (2, fr(3)), (3, fr(5)), (4, fr(11))]).unwrap());
    }

    /// Two mul terms: `x * y + a * b - out = 0`.
    #[test]
    fn two_mul_terms_satisfied() {
        let expr = Expression {
            mul_terms: vec![
                (fe(1), Witness(1), Witness(2)),
                (fe(1), Witness(3), Witness(4)),
            ],
            linear_combinations: vec![(fe(-1), Witness(5))],
            q_c: fe(0),
        };
        let art = build_artifact(vec![Opcode::AssertZero(expr)], vec![5], vec![1, 2, 3, 4]);
        // 2 * 3 + 4 * 5 = 6 + 20 = 26
        assert!(run(
            art,
            vec![(1, fr(2)), (2, fr(3)), (3, fr(4)), (4, fr(5)), (5, fr(26))]
        )
        .unwrap());
    }

    #[test]
    fn negative_coefficient_constant_term() {
        // -2 * x + 5 = 0  =>  x = 5/2 (not integer, but valid in the field)
        // For an integer-friendly version: 3*x + (-9) = 0 => x = 3.
        let expr = Expression {
            mul_terms: vec![],
            linear_combinations: vec![(fe(3), Witness(1))],
            q_c: fe(-9),
        };
        let art = build_artifact(vec![Opcode::AssertZero(expr)], vec![], vec![1]);
        assert!(run(art.clone(), vec![(1, fr(3))]).unwrap());
        assert!(!run(art, vec![(1, fr(4))]).unwrap());
    }

    #[test]
    fn missing_witness_value_errors_out_at_synthesis() {
        let expr = Expression {
            mul_terms: vec![],
            linear_combinations: vec![(fe(1), Witness(1)), (fe(-1), Witness(2))],
            q_c: fe(0),
        };
        let art = build_artifact(vec![Opcode::AssertZero(expr)], vec![2], vec![1]);
        let lowered = LoweredAcirCircuit::new(art).unwrap();
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut map = WitnessMap::new();
        map.insert(WitnessIndex(2), fr(0));
        // No value for Witness(1).
        let err = lowered.synthesize(cs, Some(&map)).unwrap_err();
        matches!(err, SynthesisError::AssignmentMissing);
    }

    /// A small `arithmetic_square`-shaped artifact: `x * x - y = 0`, where
    /// `y` is the public input and `x` is private.
    fn square_artifact() -> NoirArtifact {
        let expr = Expression {
            mul_terms: vec![(fe(1), Witness(1), Witness(1))],
            linear_combinations: vec![(fe(-1), Witness(2))],
            q_c: fe(0),
        };
        build_artifact(vec![Opcode::AssertZero(expr)], vec![2], vec![1])
    }

    /// The hash must be deterministic across runs and match a hardcoded value.
    /// This guards against silent format drift in `Program::serialize_program`.
    #[test]
    fn circuit_hash_is_stable() {
        let art = square_artifact();
        let lowered = LoweredAcirCircuit::new(art).expect("lower");
        let h1 = lowered.circuit_hash();
        let h2 = lowered.circuit_hash();
        assert_eq!(h1, h2, "circuit_hash must be deterministic");
        // Pinned from the first run on a clean checkout; bump only when the
        // underlying ACIR serialization format intentionally changes.
        const EXPECTED: &str = "7c9ba8846aa6fe8db3108c1ac9ecbe77930281e09f66b6c97f486d30b0f7ed20";
        assert_eq!(h1, EXPECTED, "circuit_hash drifted from pinned value");
    }

    /// Swapping the public input order must change the hash even when the
    /// opcode bytes are identical, because verifiers consume public inputs in
    /// the order recorded by the artifact.
    #[test]
    fn circuit_hash_changes_with_public_input_order() {
        // `x + y - z = 0` with two public inputs. We swap their order across
        // the two artifacts.
        let expr = Expression {
            mul_terms: vec![],
            linear_combinations: vec![
                (fe(1), Witness(1)),
                (fe(1), Witness(2)),
                (fe(-1), Witness(3)),
            ],
            q_c: fe(0),
        };
        let art_a = build_artifact(vec![Opcode::AssertZero(expr.clone())], vec![1, 2], vec![3]);
        let mut art_b = build_artifact(vec![Opcode::AssertZero(expr)], vec![1, 2], vec![3]);
        // Force a different public-input order without touching the program
        // bytes.
        art_b.public_inputs = vec![WitnessIndex(2), WitnessIndex(1)];

        let h_a = LoweredAcirCircuit::new(art_a).unwrap().circuit_hash();
        let h_b = LoweredAcirCircuit::new(art_b).unwrap().circuit_hash();
        assert_ne!(
            h_a, h_b,
            "swapping public input order must change circuit_hash"
        );
    }

    /// Adding an extra opcode (here, a trivial `0 = 0` `AssertZero`) must
    /// change the hash.
    #[test]
    fn circuit_hash_changes_with_extra_opcode() {
        let base = square_artifact();
        let mut extended = square_artifact();
        // `AssertZero(0 = 0)`: an `Expression` with no mul terms, no linear
        // terms, and a zero constant. Semantically a no-op but distinct bytes.
        let zero_expr = Expression {
            mul_terms: vec![],
            linear_combinations: vec![],
            q_c: fe(0),
        };
        extended.program.functions[0]
            .opcodes
            .push(Opcode::AssertZero(zero_expr));

        let h_base = LoweredAcirCircuit::new(base).unwrap().circuit_hash();
        let h_extended = LoweredAcirCircuit::new(extended).unwrap().circuit_hash();
        assert_ne!(
            h_base, h_extended,
            "adding an opcode must change circuit_hash"
        );
    }

    /// Build a 2-function `Program` whose `main` issues a single `Call` to a
    /// helper. The helper does `c = a * b` and returns `c`. Caller passes
    /// witnesses `a_w, b_w` and binds the return to `out_w`. `predicate` is
    /// the Expression the caller wants to gate the call by. Witnesses
    /// `[1..=witness_count]` are private, plus `out_w` is public.
    fn multi_fn_predicated_call_artifact(
        a_w: u32,
        b_w: u32,
        out_w: u32,
        pred_w: u32,
        predicate: Expression<FieldElement>,
    ) -> NoirArtifact {
        // Helper circuit: parameters [w1=a, w2=b], return w3=c, opcode
        // `1*w1*w2 - w3 = 0`.
        let helper = Circuit {
            function_name: "helper".to_string(),
            opcodes: vec![Opcode::AssertZero(Expression {
                mul_terms: vec![(fe(1), Witness(1), Witness(2))],
                linear_combinations: vec![(fe(-1), Witness(3))],
                q_c: fe(0),
            })],
            private_parameters: {
                let mut s = BTreeSet::new();
                s.insert(Witness(1));
                s.insert(Witness(2));
                s
            },
            public_parameters: PublicInputs(BTreeSet::new()),
            return_values: PublicInputs({
                let mut s = BTreeSet::new();
                s.insert(Witness(3));
                s
            }),
            assert_messages: vec![],
        };
        // Main circuit: opcodes = [Call(helper, inputs=[a_w, b_w],
        // outputs=[out_w], predicate)].
        let main = Circuit {
            function_name: "main".to_string(),
            opcodes: vec![Opcode::Call {
                id: acir::circuit::opcodes::AcirFunctionId(1),
                inputs: vec![Witness(a_w), Witness(b_w)],
                outputs: vec![Witness(out_w)],
                predicate,
            }],
            private_parameters: {
                let mut s = BTreeSet::new();
                s.insert(Witness(a_w));
                s.insert(Witness(b_w));
                s.insert(Witness(pred_w));
                s
            },
            public_parameters: PublicInputs({
                let mut s = BTreeSet::new();
                s.insert(Witness(out_w));
                s
            }),
            return_values: PublicInputs(BTreeSet::new()),
            assert_messages: vec![],
        };
        let program = Program {
            functions: vec![main, helper],
            unconstrained_functions: vec![],
        };
        NoirArtifact {
            circuit_name: "predicated_call_test".into(),
            program,
            public_inputs: vec![WitnessIndex(out_w)],
            witness_count: [a_w, b_w, out_w, pred_w].iter().max().copied().unwrap() as usize + 1,
            metadata: ArtifactMetadata {
                noir_version: "1.0.0-beta.21+test".into(),
                program_hash: "0".into(),
            },
        }
    }

    /// Run a multi-function artifact with the supplied caller-namespace
    /// witness map. Returns `Ok(true)` if the constraint system is
    /// satisfied. Used by the predicated-call tests below.
    fn run_multi(
        artifact: NoirArtifact,
        caller_witness: Vec<(u32, Fr)>,
        callee_witness: Vec<(u32, Fr)>,
    ) -> ark_relations::r1cs::Result<bool> {
        let lowered = LoweredAcirCircuit::new(artifact).expect("lower");
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut map = WitnessMap::new();
        for (idx, v) in caller_witness {
            map.insert(WitnessIndex(idx), v);
        }
        let mut callee_map: BTreeMap<WitnessIndex, Fr> = BTreeMap::new();
        for (idx, v) in callee_witness {
            callee_map.insert(WitnessIndex(idx), v);
        }
        map.callee_witnesses.insert(1, callee_map);
        lowered.synthesize(cs.clone(), Some(&map))?;
        cs.is_satisfied()
    }

    /// Predicated Call with predicate witness = 1: constraint `a*b == out`
    /// fires, witness satisfies it.
    #[test]
    fn predicated_call_with_predicate_one_enforces_constraint() {
        // predicate = 1 * w_pred.
        let predicate = Expression {
            mul_terms: vec![],
            linear_combinations: vec![(fe(1), Witness(10))],
            q_c: fe(0),
        };
        let art = multi_fn_predicated_call_artifact(1, 2, 3, 10, predicate);
        // a=2, b=3, out=6, p=1. Helper witnesses (its namespace) are bound to
        // the caller's via prepare_call aliases.
        let ok = run_multi(
            art,
            vec![(1, fr(2)), (2, fr(3)), (3, fr(6)), (10, fr(1))],
            vec![(1, fr(2)), (2, fr(3)), (3, fr(6))],
        )
        .unwrap();
        assert!(ok, "predicate=1 with valid witness must satisfy");
    }

    /// Predicated Call with predicate witness = 0: the callee's constraint
    /// is gated off, so `out` is unconstrained from the callee's perspective
    /// — any value that the caller's witness map binds will satisfy.
    #[test]
    fn predicated_call_with_predicate_zero_disables_callee_constraint() {
        let predicate = Expression {
            mul_terms: vec![],
            linear_combinations: vec![(fe(1), Witness(10))],
            q_c: fe(0),
        };
        let art = multi_fn_predicated_call_artifact(1, 2, 3, 10, predicate);
        // a=2, b=3, out=999 (NOT 6), p=0. With p=0 the gated constraint
        // `p*(a*b - out) = 0` is satisfied regardless of out's value.
        let ok = run_multi(
            art,
            vec![(1, fr(2)), (2, fr(3)), (3, fr(999)), (10, fr(0))],
            vec![(1, fr(2)), (2, fr(3)), (3, fr(999))],
        )
        .unwrap();
        assert!(
            ok,
            "predicate=0 must disable the callee's a*b==out constraint"
        );
    }

    /// Predicated Call with predicate witness = 1 but a *lying* witness for
    /// `out` — must be unsatisfied because the gated constraint fires when
    /// p=1.
    #[test]
    fn predicated_call_with_predicate_one_catches_lying_witness() {
        let predicate = Expression {
            mul_terms: vec![],
            linear_combinations: vec![(fe(1), Witness(10))],
            q_c: fe(0),
        };
        let art = multi_fn_predicated_call_artifact(1, 2, 3, 10, predicate);
        // a=2, b=3, out=999 (wrong), p=1 — gated constraint fires,
        // 1*(2*3 - 999) ≠ 0, so unsatisfied.
        let ok = run_multi(
            art,
            vec![(1, fr(2)), (2, fr(3)), (3, fr(999)), (10, fr(1))],
            vec![(1, fr(2)), (2, fr(3)), (3, fr(999))],
        )
        .unwrap();
        assert!(!ok, "predicate=1 with wrong out must reject");
    }

    /// Helper for the BlackBox/Memory-under-predicate tests. Builds a
    /// 2-function `Program` whose `main` issues a `Call` to a helper whose
    /// body is the supplied opcode list. The helper takes one private input
    /// `Witness(1)` and returns no values. The main exposes no public
    /// inputs; the caller's `pred_w` witness drives the Call's predicate
    /// (as `1 * pred_w`).
    fn predicated_helper_artifact(
        input_w: u32,
        pred_w: u32,
        helper_opcodes: Vec<Opcode<FieldElement>>,
    ) -> NoirArtifact {
        let predicate = Expression {
            mul_terms: vec![],
            linear_combinations: vec![(fe(1), Witness(pred_w))],
            q_c: fe(0),
        };
        let helper = Circuit {
            function_name: "helper".to_string(),
            opcodes: helper_opcodes,
            private_parameters: {
                let mut s = BTreeSet::new();
                s.insert(Witness(1));
                s
            },
            public_parameters: PublicInputs(BTreeSet::new()),
            return_values: PublicInputs(BTreeSet::new()),
            assert_messages: vec![],
        };
        let main = Circuit {
            function_name: "main".to_string(),
            opcodes: vec![Opcode::Call {
                id: acir::circuit::opcodes::AcirFunctionId(1),
                inputs: vec![Witness(input_w)],
                outputs: vec![],
                predicate,
            }],
            private_parameters: {
                let mut s = BTreeSet::new();
                s.insert(Witness(input_w));
                s.insert(Witness(pred_w));
                s
            },
            public_parameters: PublicInputs(BTreeSet::new()),
            return_values: PublicInputs(BTreeSet::new()),
            assert_messages: vec![],
        };
        let program = Program {
            functions: vec![main, helper],
            unconstrained_functions: vec![],
        };
        NoirArtifact {
            circuit_name: "predicated_helper_test".into(),
            program,
            public_inputs: vec![],
            witness_count: input_w.max(pred_w) as usize + 1,
            metadata: ArtifactMetadata {
                noir_version: "1.0.0-beta.21+test".into(),
                program_hash: "0".into(),
            },
        }
    }

    /// RANGE inside a predicated callee. With p=1 the range check fires
    /// (200 fits in 8 bits, so satisfies; 300 doesn't, so unsatisfies). With
    /// p=0 the gated constraint is disabled, so a 300-valued input still
    /// satisfies.
    #[test]
    fn predicated_callee_with_range_p0_disables_check() {
        use acir::circuit::opcodes::{BlackBoxFuncCall, FunctionInput};
        let helper_opcodes = vec![Opcode::BlackBoxFuncCall(BlackBoxFuncCall::RANGE {
            input: FunctionInput::Witness(Witness(1)),
            num_bits: 8,
        })];
        let art = predicated_helper_artifact(1, 10, helper_opcodes);
        // p=0, input=300 (out of 8-bit range, but gated off).
        let ok = run_multi(
            art,
            vec![(1, fr(300)), (10, fr(0))],
            vec![(1, fr(300))],
        )
        .unwrap();
        assert!(ok, "predicate=0 must disable the RANGE check");
    }

    #[test]
    fn predicated_callee_with_range_p1_catches_overflow() {
        use acir::circuit::opcodes::{BlackBoxFuncCall, FunctionInput};
        let helper_opcodes = vec![Opcode::BlackBoxFuncCall(BlackBoxFuncCall::RANGE {
            input: FunctionInput::Witness(Witness(1)),
            num_bits: 8,
        })];
        let art = predicated_helper_artifact(1, 10, helper_opcodes);
        // p=1, input=300 (out of 8-bit range, gating active → rejected).
        let ok = run_multi(
            art,
            vec![(1, fr(300)), (10, fr(1))],
            vec![(1, fr(300))],
        )
        .unwrap();
        assert!(!ok, "predicate=1 must catch out-of-range value");
    }

    #[test]
    fn predicated_callee_with_range_p1_accepts_valid() {
        use acir::circuit::opcodes::{BlackBoxFuncCall, FunctionInput};
        let helper_opcodes = vec![Opcode::BlackBoxFuncCall(BlackBoxFuncCall::RANGE {
            input: FunctionInput::Witness(Witness(1)),
            num_bits: 8,
        })];
        let art = predicated_helper_artifact(1, 10, helper_opcodes);
        let ok = run_multi(
            art,
            vec![(1, fr(200)), (10, fr(1))],
            vec![(1, fr(200))],
        )
        .unwrap();
        assert!(ok, "predicate=1, valid 8-bit input must satisfy");
    }

    /// MemoryInit + MemoryOp inside a predicated callee. Helper allocates a
    /// 2-slot block from witnesses w1, w2 (the caller-bound input is w1;
    /// w2 is a callee-local witness), pins index witness w3 to constant 0
    /// via an AssertZero (this is the constant-pin detection pattern from
    /// `docs/memory.md`), then reads slot 0 into w4. With p=1, w4 must
    /// equal w1; with p=0, the constraint is gated off and w4 is free.
    #[test]
    fn predicated_callee_with_memory_p0_disables_read() {
        let helper_opcodes = vec![
            Opcode::MemoryInit {
                block_id: acir::circuit::opcodes::BlockId(0),
                init: vec![Witness(1), Witness(2)],
                block_type: acir::circuit::opcodes::BlockType::Memory,
            },
            // Pin Witness(3) to 0 via `w3 - 0 = 0` (i.e. coeff=1, q_c=0).
            Opcode::AssertZero(Expression {
                mul_terms: vec![],
                linear_combinations: vec![(fe(1), Witness(3))],
                q_c: fe(0),
            }),
            // Read at index Witness(3) (= constant 0) into Witness(4).
            Opcode::MemoryOp {
                block_id: acir::circuit::opcodes::BlockId(0),
                op: acir::circuit::opcodes::MemOp::<FieldElement>::read_at_mem_index(
                    Witness(3),
                    Witness(4),
                ),
            },
            // Assert Witness(4) == Witness(1) (i.e. read returned slot 0's value).
            Opcode::AssertZero(Expression {
                mul_terms: vec![],
                linear_combinations: vec![(fe(1), Witness(4)), (fe(-1), Witness(1))],
                q_c: fe(0),
            }),
        ];
        let art = predicated_helper_artifact(1, 10, helper_opcodes);
        // p=0, callee w(4)=999 (lying), w(2)=20, w(3)=0. With p=0, the
        // gated assertions in the helper don't fire, so the lying w(4)
        // is OK.
        let ok = run_multi(
            art,
            vec![(1, fr(7)), (10, fr(0))],
            vec![(1, fr(7)), (2, fr(20)), (3, fr(0)), (4, fr(999))],
        )
        .unwrap();
        assert!(
            ok,
            "predicate=0 must disable the memory read's equality constraint"
        );
    }

    #[test]
    fn predicated_callee_with_memory_p1_enforces_read() {
        let helper_opcodes = vec![
            Opcode::MemoryInit {
                block_id: acir::circuit::opcodes::BlockId(0),
                init: vec![Witness(1), Witness(2)],
                block_type: acir::circuit::opcodes::BlockType::Memory,
            },
            Opcode::AssertZero(Expression {
                mul_terms: vec![],
                linear_combinations: vec![(fe(1), Witness(3))],
                q_c: fe(0),
            }),
            Opcode::MemoryOp {
                block_id: acir::circuit::opcodes::BlockId(0),
                op: acir::circuit::opcodes::MemOp::<FieldElement>::read_at_mem_index(
                    Witness(3),
                    Witness(4),
                ),
            },
            Opcode::AssertZero(Expression {
                mul_terms: vec![],
                linear_combinations: vec![(fe(1), Witness(4)), (fe(-1), Witness(1))],
                q_c: fe(0),
            }),
        ];
        let art = predicated_helper_artifact(1, 10, helper_opcodes);
        // p=1, correct read: w(4)=w(1)=7. Satisfies.
        let ok = run_multi(
            art.clone(),
            vec![(1, fr(7)), (10, fr(1))],
            vec![(1, fr(7)), (2, fr(20)), (3, fr(0)), (4, fr(7))],
        )
        .unwrap();
        assert!(ok, "predicate=1 with correct read must satisfy");
        // p=1, lying about the read: w(4)=999 ≠ w(1)=7. Unsatisfies.
        let bad = run_multi(
            art,
            vec![(1, fr(7)), (10, fr(1))],
            vec![(1, fr(7)), (2, fr(20)), (3, fr(0)), (4, fr(999))],
        )
        .unwrap();
        assert!(!bad, "predicate=1 with lying read must reject");
    }

    /// AND with `num_bits` outside `[1, 64]` must be rejected at setup time
    /// with a `BackendError::UnsupportedOpcode` carrying a width-specific help
    /// message, not panic deep inside the lowering closure.
    #[test]
    fn bitwise_and_with_oversized_width_rejected() {
        use acir::circuit::opcodes::{BlackBoxFuncCall, FunctionInput};
        use acir::native_types::Witness;
        let bb = BlackBoxFuncCall::AND {
            lhs: FunctionInput::Witness(Witness(1)),
            rhs: FunctionInput::Witness(Witness(2)),
            output: Witness(3),
            num_bits: 128,
        };
        let art = build_artifact(vec![Opcode::BlackBoxFuncCall(bb)], vec![3], vec![1, 2]);
        let err = LoweredAcirCircuit::new(art).err().expect("AND num_bits=128 must reject");
        let msg = format!("{err}");
        assert!(
            msg.contains("BlackBoxFuncCall::AND") && msg.contains("num_bits=128"),
            "error should name the opcode and offending width: {msg}"
        );
        assert!(
            msg.contains("ROADMAP step WS-B.1"),
            "error should point at ROADMAP step WS-B.1: {msg}"
        );
    }
}
