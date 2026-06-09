//! Brillig output-pinning coverage check.
//!
//! The trust-outputs lowering strategy used by [`brillig::lower_brillig_call`]
//! emits no R1CS constraints for the `BrilligCall` itself. Soundness rests on
//! Noir's compiler invariant `(SI)` (see `docs/brillig.md`): every Brillig
//! output witness is *also* referenced by at least one surrounding
//! `Opcode::AssertZero` / `Opcode::BlackBoxFuncCall` / `Opcode::MemoryOp`
//! that pins its value relative to other (constrained) witnesses.
//!
//! This module is a static analyser that walks the ACIR opcode stream and
//! checks that property. It returns the set of "unpinned" Brillig outputs —
//! witness indices declared as a Brillig output but *not* referenced by any
//! other constraining opcode. A non-empty set is a finding: either the Noir
//! compiler has emitted unsound ACIR (compiler bug) or the artifact has
//! been tampered with.
//!
//! Pairs with `docs/brillig.md`'s "(SI) invariant" discussion and the audit
//! plan's recommendation to mechanise the check. The check is available as
//! a library function (`check_brillig_outputs_pinned`) callable from tests
//! and from the CLI under a `--strict` flag.

use std::collections::BTreeSet;

use acir::FieldElement;
use acir::circuit::Opcode;
use acir::circuit::brillig::BrilligOutputs;
use acir::native_types::Expression;

/// Findings returned by [`check_brillig_outputs_pinned`].
#[derive(Debug, Default, Clone)]
pub struct BrilligPinningReport {
    /// Witness indices declared as Brillig outputs that are **not** referenced
    /// by any surrounding `AssertZero` / `BlackBoxFuncCall` / `MemoryOp` /
    /// `Call` input. Non-empty = `(SI)`-invariant violation.
    pub unpinned_outputs: BTreeSet<u32>,
    /// Total count of Brillig output witnesses scanned (informational).
    pub brillig_outputs_total: usize,
}

impl BrilligPinningReport {
    /// The check passed iff every output is pinned.
    pub fn is_ok(&self) -> bool {
        self.unpinned_outputs.is_empty()
    }
}

/// Walk `opcodes` and verify every `BrilligCall` output witness appears in
/// at least one constraining opcode. Returns a [`BrilligPinningReport`].
///
/// Constraining opcodes considered:
///
/// * `Opcode::AssertZero` — canonical pinning vehicle (the hint/check pattern
///   documented in `docs/brillig.md`).
/// * `Opcode::BlackBoxFuncCall` — inputs and outputs both constrain the
///   witness (gadgets always emit per-bit / per-byte constraints over their
///   inputs and outputs). Uses `BlackBoxFuncCall::{get_inputs_vec, get_outputs_vec}`
///   so we don't have to enumerate every variant by hand.
/// * `Opcode::MemoryOp` / `Opcode::MemoryInit` — values and indices
///   referenced here are pinned by the memory gadget's selector layer.
/// * `Opcode::Call` — input witnesses are passed into a callee whose body
///   itself emits constraints; outputs are returned through fresh witnesses
///   that are themselves subject to the same `(SI)` check recursively.
pub fn check_brillig_outputs_pinned(opcodes: &[Opcode<FieldElement>]) -> BrilligPinningReport {
    let mut brillig_outs: BTreeSet<u32> = BTreeSet::new();
    let mut referenced: BTreeSet<u32> = BTreeSet::new();

    for op in opcodes {
        match op {
            Opcode::BrilligCall { outputs, .. } => {
                for out in outputs {
                    match out {
                        BrilligOutputs::Simple(w) => {
                            brillig_outs.insert(w.0);
                        }
                        BrilligOutputs::Array(ws) => {
                            for w in ws {
                                brillig_outs.insert(w.0);
                            }
                        }
                    }
                }
            }
            Opcode::AssertZero(expr) => collect_expr_witnesses(expr, &mut referenced),
            Opcode::BlackBoxFuncCall(bb) => {
                for input in bb.get_inputs_vec() {
                    if !input.is_constant() {
                        referenced.insert(input.to_witness().0);
                    }
                }
                for w in bb.get_outputs_vec() {
                    referenced.insert(w.0);
                }
            }
            Opcode::MemoryOp { op: mem_op, .. } => {
                referenced.insert(mem_op.index.0);
                referenced.insert(mem_op.value.0);
            }
            Opcode::MemoryInit { init, .. } => {
                for w in init {
                    referenced.insert(w.0);
                }
            }
            Opcode::Call {
                inputs, outputs, ..
            } => {
                for w in inputs {
                    referenced.insert(w.0);
                }
                for w in outputs {
                    referenced.insert(w.0);
                }
            }
        }
    }

    let unpinned: BTreeSet<u32> = brillig_outs.difference(&referenced).copied().collect();
    BrilligPinningReport {
        unpinned_outputs: unpinned,
        brillig_outputs_total: brillig_outs.len(),
    }
}

fn collect_expr_witnesses(expr: &Expression<FieldElement>, out: &mut BTreeSet<u32>) {
    for (_, w) in &expr.linear_combinations {
        out.insert(w.0);
    }
    for (_, wa, wb) in &expr.mul_terms {
        out.insert(wa.0);
        out.insert(wb.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Empty program: no Brillig calls, no findings.
    #[test]
    fn empty_program_reports_ok() {
        let report = check_brillig_outputs_pinned(&[]);
        assert!(report.is_ok());
        assert_eq!(report.brillig_outputs_total, 0);
    }

    // Note: positive-case tests (synthesising a `BrilligCall` + surrounding
    // `AssertZero` from scratch) require accessing private constructors in
    // `acir`'s `BrilligFunctionId` and a careful `Expression` build. We
    // exercise the analyser end-to-end via the integration tests in
    // `crates/tests/`, which start from real Noir-emitted ACIR (where the
    // constructors are public-by-reflection). The unit test above covers
    // the empty-program edge case; the integration tests cover the
    // positive and negative paths against real fixtures.
}
