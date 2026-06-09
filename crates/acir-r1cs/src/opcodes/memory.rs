//! Lowering arms for `Opcode::MemoryInit` and `Opcode::MemoryOp` (design
//! note in `docs/memory.md`).
//!
//! `MemoryInit` allocates an Arkworks `Variable` for each init witness and
//! records the per-slot `(Variable, Option<Fr>)` pair (alias
//! [`ShadowEntry`]) in a lowering-time map. `MemoryOp` then dispatches on
//! whether its `index` witness is pinned to a compile-time constant by a
//! preceding trivial `AssertZero`:
//!
//! * **Constant-index Read** — emit one linear constraint forcing
//!   `value_witness == shadow[block_id][j].var`.
//! * **Constant-index Write** — allocate the new value witness, replace
//!   `shadow[block_id][j]` so subsequent reads inherit the post-write
//!   `(Variable, Fr)` pair.
//! * **Variable-index Read** — emit the selector argument over the shadow
//!   `Variable`s (`Σ s_j = 1`, `s_j · (index - j) = 0`, `value = Σ s_j · arr[j]`).
//!   Cost: `~2N + 2` boolean + linear constraints, plus `N` muls.
//! * **Variable-index Write** — same selector setup, plus a per-slot
//!   `arr_post[j] = (1 - s_j) · arr_pre[j] + s_j · value` update enforced as
//!   `s_j · (value - arr_pre[j]) = arr_post[j] - arr_pre[j]`. The shadow is
//!   rewritten in place with the fresh `arr_post` Variables so subsequent
//!   reads see the post-write state.
//!
//! See `docs/memory.md` for the soundness arguments and the database of
//! constant-pinning patterns recognised by [`extract_pinned_constants`].
//!
//! The `block_type` of `MemoryInit` is observed only to reject
//! `BlockType::CallData(_)` and `BlockType::ReturnData`. Both forms are
//! databus markers used for recursive proof schemes; xark does not support
//! them yet and treating them as ordinary memory is unsound for downstream
//! schemes that rely on the databus contract.

use std::collections::{BTreeMap, HashMap};

use acir::FieldElement;
use acir::circuit::Opcode;
use acir::circuit::opcodes::{BlockId, BlockType, MemOp, MemOpKind};
use acir::native_types::Witness;
use ark_bn254::Fr;
use ark_ff::{Field, One, Zero};
use ark_relations::gr1cs::{LinearCombination, SynthesisError, Variable};

use crate::artifact::WitnessIndex;
use crate::error::BackendError;
use crate::field::noir_field_to_fr;
use crate::gadgets::boolean::enforce_boolean;
use crate::r1cs_builder::R1csBuilder;

/// Forward sweep that recognises witnesses pinned to a constant by a
/// preceding trivial `AssertZero` of the shape `coeff * w + q_c = 0`.
///
/// This is the **conservative** detector described in `docs/memory.md`:
/// any witness pinned via this single-term shape is detected. Witnesses
/// indirectly pinned through mul terms or longer linear chains are missed
/// — those `MemoryOp`s fall through to the variable-index lowering path
/// (the selector argument).
pub fn extract_pinned_constants(opcodes: &[Opcode<FieldElement>]) -> BTreeMap<WitnessIndex, Fr> {
    let mut pinned: BTreeMap<WitnessIndex, Fr> = BTreeMap::new();
    for op in opcodes {
        if let Opcode::AssertZero(expr) = op {
            if !expr.mul_terms.is_empty() {
                continue;
            }
            if expr.linear_combinations.len() != 1 {
                continue;
            }
            let (coeff, w) = &expr.linear_combinations[0];
            let coeff_fr = noir_field_to_fr(coeff);
            if coeff_fr.is_zero() {
                continue;
            }
            // expr is `coeff * w + q_c = 0`, so `w = -q_c / coeff`.
            let qc_fr = noir_field_to_fr(&expr.q_c);
            let inv = match coeff_fr.inverse() {
                Some(i) => i,
                None => continue, // unreachable for nonzero Fr, but defensive.
            };
            let value = -qc_fr * inv;
            // First write wins. Multiple pins should agree (otherwise the
            // circuit is unsatisfiable anyway), and we don't want a later
            // weaker chain to overwrite an earlier exact pin.
            pinned
                .entry(WitnessIndex::from_witness(*w))
                .or_insert(value);
        }
    }
    pinned
}

/// Convert a `Fr` to a `usize` if it fits, returning `None` otherwise. Used
/// for index decoding — out-of-`usize` indices are silently rejected as
/// out-of-bounds by the caller.
fn fr_to_usize_if_small(v: &Fr) -> Option<usize> {
    let mut bytes = [0u8; 32];
    let big: num_bigint::BigUint = (*v).into();
    let be = big.to_bytes_be();
    let pad = 32 - be.len();
    bytes[pad..].copy_from_slice(&be);
    // Reject anything that doesn't fit in u64; legitimate Noir array
    // indices are tiny.
    for byte in &bytes[..24] {
        if *byte != 0 {
            return None;
        }
    }
    let mut u = 0u64;
    for byte in &bytes[24..] {
        u = (u << 8) | u64::from(*byte);
    }
    usize::try_from(u).ok()
}

/// In-circuit representation of one memory slot. The constraint system has
/// an allocated `Variable` for the slot's current value, and at proving
/// time the `Option<Fr>` carries that value for downstream native-side
/// witness solving (selector-gated updates, etc.).
pub type ShadowEntry = (Variable, Option<Fr>);

/// Lower an `Opcode::MemoryInit`. Validates the block type, then allocates
/// an Arkworks `Variable` for each init witness and records the resulting
/// per-slot `(Variable, Option<Fr>)` pair in the shadow map.
pub fn lower_memory_init(
    builder: &mut R1csBuilder<'_>,
    memory_blocks: &mut HashMap<BlockId, Vec<ShadowEntry>>,
    opcode_index: usize,
    block_id: BlockId,
    init: &[Witness],
    block_type: &BlockType,
) -> Result<(), BackendError> {
    if block_type.is_databus() {
        return Err(BackendError::UnsupportedOpcode {
            opcode: "MemoryInit[databus]".to_string(),
            index: opcode_index,
            help: "Databus memory blocks (BlockType::CallData / ReturnData) are not \
 supported by the xark backend. Recompile the Noir program \
 without --enable-databus, or file an issue if you need this \
 feature for recursive proof schemes."
                .to_string(),
        });
    }
    let mut shadow: Vec<ShadowEntry> = Vec::with_capacity(init.len());
    for w in init.iter() {
        let idx = WitnessIndex::from_witness(*w);
        let var = builder.alloc_witness(idx).map_err(synthesis_to_backend)?;
        let value = builder
            .maybe_witness_value(idx)
            .map_err(synthesis_to_backend)?;
        shadow.push((var, value));
    }
    // A given `block_id` should only be initialised once; if a duplicate
    // appears we keep the original (matches Noir's contract that block IDs
    // are unique per program).
    memory_blocks.entry(block_id).or_insert(shadow);
    Ok(())
}

/// Lower an `Opcode::MemoryOp`. Constant-index reads emit a single
/// equality constraint to the shadow witness; constant-index writes update
/// the shadow without emitting a constraint. Variable-index reads and
/// writes are lowered via the selector argument.
pub fn lower_memory_op(
    builder: &mut R1csBuilder<'_>,
    pinned_constants: &BTreeMap<WitnessIndex, Fr>,
    memory_blocks: &mut HashMap<BlockId, Vec<ShadowEntry>>,
    opcode_index: usize,
    block_id: BlockId,
    op: &MemOp,
) -> Result<(), BackendError> {
    let shadow =
        memory_blocks
            .get_mut(&block_id)
            .ok_or_else(|| BackendError::UnsupportedOpcode {
                opcode: "MemoryOp[uninitialized-block]".to_string(),
                index: opcode_index,
                help: format!(
                    "MemoryOp references block id {block_id} which was never \
 declared via MemoryInit. This is malformed ACIR; \
 regenerate the artifact with a clean `nargo execute`."
                ),
            })?;

    let index_witness = WitnessIndex::from_witness(op.index);
    let value_witness = WitnessIndex::from_witness(op.value);

    let index_fr_opt = pinned_constants.get(&index_witness).copied();
    let index_fr = match index_fr_opt {
        Some(fr) => fr,
        None => {
            // Variable-index path. Handles both reads
            // (selector argument over the shadow Variables) and writes
            // (selector-gated per-slot shadow update).
            return lower_memory_op_variable_index(
                builder,
                shadow,
                opcode_index,
                index_witness,
                value_witness,
                op,
            );
        }
    };

    let j = fr_to_usize_if_small(&index_fr).ok_or_else(|| BackendError::UnsupportedOpcode {
        opcode: "MemoryOp[out-of-range-constant-index]".to_string(),
        index: opcode_index,
        help: "Constant index does not fit in `usize`. This is almost certainly \
 a bug in the Noir source — array indices should be small \
 nonnegative integers."
            .to_string(),
    })?;

    if j >= shadow.len() {
        return Err(BackendError::UnsupportedOpcode {
            opcode: "MemoryOp[out-of-bounds-constant-index]".to_string(),
            index: opcode_index,
            help: format!(
                "Constant index {j} is out of bounds for block of length {len}. \
 This is a bug in the Noir source.",
                len = shadow.len()
            ),
        });
    }

    match op.operation {
        MemOpKind::Read => {
            let (slot_var, _slot_val) = shadow[j];
            let value_var = builder
                .alloc_witness(value_witness)
                .map_err(synthesis_to_backend)?;
            let mut diff: LinearCombination<Fr> = LinearCombination::from((Fr::one(), value_var));
            diff.0.push((-Fr::one(), slot_var));
            builder
                .enforce(builder.zero_lc(), builder.zero_lc(), neg_lc(&diff))
                .map_err(synthesis_to_backend)?;
        }
        MemOpKind::Write => {
            let value_var = builder
                .alloc_witness(value_witness)
                .map_err(synthesis_to_backend)?;
            let value_val = builder
                .maybe_witness_value(value_witness)
                .map_err(synthesis_to_backend)?;
            shadow[j] = (value_var, value_val);
        }
    }

    Ok(())
}

/// Convert a `SynthesisError` from the R1CS layer into a `BackendError`.
/// Used to propagate allocation failures (missing witness values during
/// proving) through the memory lowering path.
fn synthesis_to_backend(err: SynthesisError) -> BackendError {
    BackendError::ConstraintUnsatisfied {
        detail: format!("memory lowering: {err}"),
    }
}

/// Selector-argument lowering for variable-index memory ops (see
/// `docs/memory.md`). For an `N`-slot block we allocate
/// `N` boolean selectors `s_j`, enforce `Σ s_j = 1` and `s_j * (index - j) = 0`
/// for each `j`, then express the read result as `value = Σ s_j * arr[j]`.
/// Per-access cost: `2N + 2` boolean + linear constraints, plus `N` mul
/// constraints for the selected-slot products.
///
/// Variable-index writes use a selector-gated shadow update: each slot gets a
/// fresh `arr_post[j]` witness constrained by
/// `arr_post[j] = (1-s_j)*arr_pre[j] + s_j*value` (emitted as
/// `s_j * (value - arr_pre[j]) = arr_post[j] - arr_pre[j]`), bumping the cost
/// to `~3N` per write. See the `MemOpKind::Write` arm below.
fn lower_memory_op_variable_index(
    builder: &mut R1csBuilder<'_>,
    shadow: &mut [ShadowEntry],
    opcode_index: usize,
    index_witness: WitnessIndex,
    value_witness: WitnessIndex,
    op: &MemOp,
) -> Result<(), BackendError> {
    let n = shadow.len();
    if n == 0 {
        return Err(BackendError::UnsupportedOpcode {
            opcode: "MemoryOp[empty-block]".to_string(),
            index: opcode_index,
            help: "Variable-index access on a zero-length block is undefined.".to_string(),
        });
    }

    // Get the index value at proving time. In setup mode this is `None`; we
    // still allocate the variables, just with `None` value closures that
    // won't be invoked.
    let index_val = builder
        .maybe_witness_value(index_witness)
        .map_err(synthesis_to_backend)?;
    let active_slot: Option<usize> = index_val.and_then(|v| fr_to_usize_if_small(&v));

    if let Some(j) = active_slot {
        if j >= n {
            return Err(BackendError::UnsupportedOpcode {
                opcode: "MemoryOp[variable-index-out-of-bounds]".to_string(),
                index: opcode_index,
                help: format!(
                    "Variable-index access resolved to slot {j} but block has \
 length {n}. This is a Noir-source bug."
                ),
            });
        }
    }

    let index_var = builder
        .alloc_witness(index_witness)
        .map_err(synthesis_to_backend)?;
    let value_var = builder
        .alloc_witness(value_witness)
        .map_err(synthesis_to_backend)?;
    let value_val = builder
        .maybe_witness_value(value_witness)
        .map_err(synthesis_to_backend)?;

    // Allocate boolean selectors `s_j ∈ {0, 1}` with `Σ s_j = 1` and
    // `s_j * (index_var - j) = 0`.
    let mut selectors: Vec<Variable> = Vec::with_capacity(n);
    let mut sum_terms: Vec<(Fr, Variable)> = Vec::with_capacity(n + 1);
    for j in 0..n {
        let bit_value = active_slot.map(|active| if active == j { Fr::one() } else { Fr::zero() });
        let s_j = builder
            .alloc_with_value(bit_value)
            .map_err(synthesis_to_backend)?;
        enforce_boolean(builder, s_j).map_err(synthesis_to_backend)?;
        let j_fr = Fr::from(j as u64);
        let index_minus_j = LinearCombination(vec![(Fr::one(), index_var), (-j_fr, Variable::One)]);
        builder
            .enforce(
                LinearCombination(vec![(Fr::one(), s_j)]),
                index_minus_j,
                builder.zero_lc(),
            )
            .map_err(synthesis_to_backend)?;
        sum_terms.push((Fr::one(), s_j));
        selectors.push(s_j);
    }
    sum_terms.push((-Fr::one(), Variable::One));
    builder
        .enforce(
            builder.zero_lc(),
            builder.zero_lc(),
            LinearCombination(sum_terms),
        )
        .map_err(synthesis_to_backend)?;

    match op.operation {
        MemOpKind::Read => {
            // For each slot: `t_j = s_j · arr_pre[j]`, then `value = Σ t_j`.
            let mut t_vars: Vec<Variable> = Vec::with_capacity(n);
            for j in 0..n {
                let (arr_var, arr_val) = shadow[j];
                let t_val = match (active_slot, arr_val) {
                    (Some(active), Some(v)) => Some(if active == j { v } else { Fr::zero() }),
                    _ => None,
                };
                let t_j = builder
                    .alloc_with_value(t_val)
                    .map_err(synthesis_to_backend)?;
                builder
                    .enforce(
                        LinearCombination(vec![(Fr::one(), selectors[j])]),
                        LinearCombination(vec![(Fr::one(), arr_var)]),
                        LinearCombination(vec![(Fr::one(), t_j)]),
                    )
                    .map_err(synthesis_to_backend)?;
                t_vars.push(t_j);
            }
            let mut value_eq = vec![(Fr::one(), value_var)];
            for t in &t_vars {
                value_eq.push((-Fr::one(), *t));
            }
            builder
                .enforce(
                    builder.zero_lc(),
                    builder.zero_lc(),
                    LinearCombination(value_eq),
                )
                .map_err(synthesis_to_backend)?;
        }
        MemOpKind::Write => {
            // Per slot: allocate fresh `arr_post[j]` with proving-time value
            // `if j == active { value_val } else { arr_pre_val[j] }`.
            // Enforce `s_j * (value - arr_pre[j]) = arr_post[j] - arr_pre[j]`.
            // When `s_j == 1`: arr_post == value. When `s_j == 0`:
            // arr_post == arr_pre.
            let mut new_shadow: Vec<ShadowEntry> = Vec::with_capacity(n);
            for j in 0..n {
                let (arr_pre_var, arr_pre_val) = shadow[j];
                let post_val = match (active_slot, value_val, arr_pre_val) {
                    (Some(active), Some(v), Some(pre)) => Some(if active == j { v } else { pre }),
                    _ => None,
                };
                let arr_post_var = builder
                    .alloc_with_value(post_val)
                    .map_err(synthesis_to_backend)?;
                // LHS = s_j
                // RHS = value_var - arr_pre_var
                // OUT = arr_post_var - arr_pre_var
                let lhs = LinearCombination(vec![(Fr::one(), selectors[j])]);
                let rhs =
                    LinearCombination(vec![(Fr::one(), value_var), (-Fr::one(), arr_pre_var)]);
                let out =
                    LinearCombination(vec![(Fr::one(), arr_post_var), (-Fr::one(), arr_pre_var)]);
                builder
                    .enforce(lhs, rhs, out)
                    .map_err(synthesis_to_backend)?;
                new_shadow.push((arr_post_var, post_val));
            }
            // Replace the shadow contents in place. We can't reassign the
            // slice; we have to write through to each index.
            for (j, entry) in new_shadow.into_iter().enumerate() {
                shadow[j] = entry;
            }
        }
    }

    Ok(())
}

fn neg_lc(lc: &LinearCombination<Fr>) -> LinearCombination<Fr> {
    let mut out: Vec<(Fr, Variable)> = Vec::with_capacity(lc.0.len());
    for (coeff, var) in lc.0.iter() {
        out.push((-*coeff, *var));
    }
    LinearCombination(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use acir::native_types::{Expression, Witness};

    fn fe(n: i64) -> FieldElement {
        if n >= 0 {
            FieldElement::from(n as u128)
        } else {
            -FieldElement::from((-n) as u128)
        }
    }

    /// `w - 5 = 0` pins `w = 5`.
    #[test]
    fn pins_simple_assert_zero() {
        let expr = Expression {
            mul_terms: vec![],
            linear_combinations: vec![(fe(1), Witness(7))],
            q_c: fe(-5),
        };
        let pinned = extract_pinned_constants(&[Opcode::AssertZero(expr)]);
        let v = pinned.get(&WitnessIndex(7)).copied().expect("pinned");
        assert_eq!(v, Fr::from(5u64));
    }

    /// `3 * w - 9 = 0` pins `w = 3` (non-unit coefficient).
    #[test]
    fn pins_with_nonunit_coefficient() {
        let expr = Expression {
            mul_terms: vec![],
            linear_combinations: vec![(fe(3), Witness(2))],
            q_c: fe(-9),
        };
        let pinned = extract_pinned_constants(&[Opcode::AssertZero(expr)]);
        let v = pinned.get(&WitnessIndex(2)).copied().expect("pinned");
        assert_eq!(v, Fr::from(3u64));
    }

    /// Mul terms disqualify the pin (we don't try to solve quadratics).
    #[test]
    fn does_not_pin_when_mul_terms_present() {
        let expr = Expression {
            mul_terms: vec![(fe(1), Witness(1), Witness(1))],
            linear_combinations: vec![(fe(1), Witness(2))],
            q_c: fe(0),
        };
        let pinned = extract_pinned_constants(&[Opcode::AssertZero(expr)]);
        assert!(pinned.is_empty());
    }

    /// Multiple linear terms disqualify the pin.
    #[test]
    fn does_not_pin_when_multiple_linear_terms() {
        let expr = Expression {
            mul_terms: vec![],
            linear_combinations: vec![(fe(1), Witness(1)), (fe(1), Witness(2))],
            q_c: fe(0),
        };
        let pinned = extract_pinned_constants(&[Opcode::AssertZero(expr)]);
        assert!(pinned.is_empty());
    }

    /// Helper: allocate a `ShadowEntry` for a Noir witness index, looking up
    /// the value from the supplied map (or `None` if not present).
    fn shadow_from_witness(builder: &mut R1csBuilder<'_>, idx: WitnessIndex) -> ShadowEntry {
        let var = builder.alloc_witness(idx).unwrap();
        let val = builder.maybe_witness_value(idx).unwrap();
        (var, val)
    }

    /// End-to-end variable-index read: build a 2-slot block, set index to 1,
    /// read value matches slot 1, system satisfies.
    #[test]
    fn variable_index_read_two_slot_block_satisfies() {
        use crate::witness::WitnessMap;
        use ark_relations::gr1cs::ConstraintSystem;
        let mut witness_map = WitnessMap::<Fr>::new();
        witness_map.insert(WitnessIndex(100), Fr::from(7u64));
        witness_map.insert(WitnessIndex(101), Fr::from(13u64));
        witness_map.insert(WitnessIndex(200), Fr::from(1u64));
        witness_map.insert(WitnessIndex(201), Fr::from(13u64));

        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&witness_map));
        builder.finish_public_pass();

        let mut shadow = vec![
            shadow_from_witness(&mut builder, WitnessIndex(100)),
            shadow_from_witness(&mut builder, WitnessIndex(101)),
        ];
        let op = MemOp::read_at_mem_index(Witness(200), Witness(201));
        lower_memory_op_variable_index(
            &mut builder,
            &mut shadow,
            42,
            WitnessIndex(200),
            WitnessIndex(201),
            &op,
        )
        .unwrap();

        assert!(cs.is_satisfied().unwrap());
    }

    /// Same setup but with a lying witness (says slot 0 but reads back 13) —
    /// must be unsatisfiable.
    #[test]
    fn variable_index_read_inconsistent_witness_unsatisfied() {
        use crate::witness::WitnessMap;
        use ark_relations::gr1cs::ConstraintSystem;
        let mut witness_map = WitnessMap::<Fr>::new();
        witness_map.insert(WitnessIndex(100), Fr::from(7u64));
        witness_map.insert(WitnessIndex(101), Fr::from(13u64));
        witness_map.insert(WitnessIndex(200), Fr::from(0u64));
        witness_map.insert(WitnessIndex(201), Fr::from(13u64));

        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&witness_map));
        builder.finish_public_pass();

        let mut shadow = vec![
            shadow_from_witness(&mut builder, WitnessIndex(100)),
            shadow_from_witness(&mut builder, WitnessIndex(101)),
        ];
        let op = MemOp::read_at_mem_index(Witness(200), Witness(201));
        lower_memory_op_variable_index(
            &mut builder,
            &mut shadow,
            42,
            WitnessIndex(200),
            WitnessIndex(201),
            &op,
        )
        .unwrap();

        assert!(!cs.is_satisfied().unwrap());
    }

    /// Variable-index WRITE: write value 99 to slot 1 of a 3-slot block,
    /// then read back via variable index. Read returns the new value;
    /// constraint system satisfies.
    #[test]
    fn variable_index_write_then_read_propagates_new_value() {
        use crate::witness::WitnessMap;
        use ark_relations::gr1cs::ConstraintSystem;
        let mut witness_map = WitnessMap::<Fr>::new();
        // Block init: [10, 20, 30] at witnesses 100, 101, 102.
        witness_map.insert(WitnessIndex(100), Fr::from(10u64));
        witness_map.insert(WitnessIndex(101), Fr::from(20u64));
        witness_map.insert(WitnessIndex(102), Fr::from(30u64));
        // Write: index witness 200 = 1, value witness 201 = 99.
        witness_map.insert(WitnessIndex(200), Fr::from(1u64));
        witness_map.insert(WitnessIndex(201), Fr::from(99u64));
        // Subsequent read: index witness 202 = 1, value witness 203 = 99.
        witness_map.insert(WitnessIndex(202), Fr::from(1u64));
        witness_map.insert(WitnessIndex(203), Fr::from(99u64));

        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&witness_map));
        builder.finish_public_pass();

        let mut shadow = vec![
            shadow_from_witness(&mut builder, WitnessIndex(100)),
            shadow_from_witness(&mut builder, WitnessIndex(101)),
            shadow_from_witness(&mut builder, WitnessIndex(102)),
        ];
        let write_op = MemOp::write_to_mem_index(Witness(200), Witness(201));
        lower_memory_op_variable_index(
            &mut builder,
            &mut shadow,
            43,
            WitnessIndex(200),
            WitnessIndex(201),
            &write_op,
        )
        .unwrap();

        let read_op = MemOp::read_at_mem_index(Witness(202), Witness(203));
        lower_memory_op_variable_index(
            &mut builder,
            &mut shadow,
            44,
            WitnessIndex(202),
            WitnessIndex(203),
            &read_op,
        )
        .unwrap();

        assert!(cs.is_satisfied().unwrap());
    }

    /// Variable-index WRITE followed by a read at a DIFFERENT index must
    /// return the original (pre-write) value at that slot.
    #[test]
    fn variable_index_write_does_not_affect_other_slots() {
        use crate::witness::WitnessMap;
        use ark_relations::gr1cs::ConstraintSystem;
        let mut witness_map = WitnessMap::<Fr>::new();
        witness_map.insert(WitnessIndex(100), Fr::from(10u64));
        witness_map.insert(WitnessIndex(101), Fr::from(20u64));
        witness_map.insert(WitnessIndex(102), Fr::from(30u64));
        // Write at slot 1 = 99.
        witness_map.insert(WitnessIndex(200), Fr::from(1u64));
        witness_map.insert(WitnessIndex(201), Fr::from(99u64));
        // Read at slot 2, expecting 30 (unchanged).
        witness_map.insert(WitnessIndex(202), Fr::from(2u64));
        witness_map.insert(WitnessIndex(203), Fr::from(30u64));

        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&witness_map));
        builder.finish_public_pass();

        let mut shadow = vec![
            shadow_from_witness(&mut builder, WitnessIndex(100)),
            shadow_from_witness(&mut builder, WitnessIndex(101)),
            shadow_from_witness(&mut builder, WitnessIndex(102)),
        ];
        let write_op = MemOp::write_to_mem_index(Witness(200), Witness(201));
        lower_memory_op_variable_index(
            &mut builder,
            &mut shadow,
            43,
            WitnessIndex(200),
            WitnessIndex(201),
            &write_op,
        )
        .unwrap();

        let read_op = MemOp::read_at_mem_index(Witness(202), Witness(203));
        lower_memory_op_variable_index(
            &mut builder,
            &mut shadow,
            44,
            WitnessIndex(202),
            WitnessIndex(203),
            &read_op,
        )
        .unwrap();

        assert!(cs.is_satisfied().unwrap());
    }
}
