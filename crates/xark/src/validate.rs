//! Validate that a MIR `Body` lies within the accepted circuit subset.
//!
//! Runs before lowering and rejects unsupported statements, rvalues,
//! terminators, places, and calls with readable diagnostics. Lowering assumes a
//! validated body but still defends against surprises.

use rustc_middle::mir::{Body, Operand, Place, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::TyCtxt;

use crate::diagnostics::{CompileError, CompileResult};
use crate::lower_mir::CallRegistry;

pub fn validate<'tcx>(
    tcx: TyCtxt<'tcx>,
    registry: &CallRegistry,
    body: &Body<'tcx>,
) -> CompileResult<()> {
    for bb in body.basic_blocks.indices() {
        let data = &body.basic_blocks[bb];

        // Skip unwind/cleanup blocks. A circuit never unwinds (no panics are
        // reachable — bounds/overflow asserts follow their success edge), so
        // lowering only ever walks the non-unwind edges. These blocks exist only
        // to drop values during a panic (e.g. the `array::IntoIter` of a
        // `for x in arr`), and contain `UnwindResume`/`Drop … unwind` terminators
        // that would otherwise be spuriously rejected.
        if data.is_cleanup {
            continue;
        }

        for stmt in &data.statements {
            // Attach the statement's source span as a fallback; an inner check's
            // more precise span (if any) is preserved by `or_span`.
            (|| -> CompileResult<()> {
                match &stmt.kind {
                    StatementKind::Assign(boxed) => {
                        let (place, rvalue) = &**boxed;
                        check_place(place)?;
                        check_rvalue(rvalue)?;
                        Ok(())
                    }
                    StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::FakeRead(..)
                    | StatementKind::PlaceMention(..)
                    | StatementKind::AscribeUserType(..)
                    | StatementKind::Coverage(..)
                    | StatementKind::BackwardIncompatibleDropHint { .. } => Ok(()),
                    _ => Err(CompileError::new("unsupported statement inside circuit")),
                }
            })()
            .map_err(|e| e.or_span(stmt.source_info.span))?;
        }

        let terminator = data.terminator();
        check_terminator(tcx, registry, &terminator.kind)
            .map_err(|e| e.or_span(terminator.source_info.span))?;
    }
    Ok(())
}

fn check_place(place: &Place<'_>) -> CompileResult<()> {
    use rustc_middle::mir::ProjectionElem;
    for elem in place.projection.iter() {
        match elem {
            // Array indexing (constant indices) and tuple/overflow-check field
            // access. Lowering enforces that indices are compile-time constants.
            // `Downcast` is the enum-variant selector of `(_opt as Some).0` when
            // reading the modeled `Option` produced by iterating a constant range;
            // lowering only resolves that case and rejects genuine enum matches.
            // `Deref` is a transparent reference in the value model (e.g. `*x`
            // reading a `&Field` yielded by iterating `&arr`); lowering copies the
            // referent's slots so the deref reads them back.
            ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Field(..)
            | ProjectionElem::Downcast(..)
            | ProjectionElem::Deref => {}
            _ => {
                return Err(CompileError::new("unsupported place projection (subslice)")
                    .with_note("only fixed-size array indexing is supported"))
            }
        }
    }
    Ok(())
}

fn check_operand(operand: &Operand<'_>) -> CompileResult<()> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => check_place(place),
        Operand::Constant(_) | Operand::RuntimeChecks(_) => Ok(()),
    }
}

fn check_rvalue(rvalue: &Rvalue<'_>) -> CompileResult<()> {
    match rvalue {
        Rvalue::Use(operand, _) => check_operand(operand),
        Rvalue::UnaryOp(_, operand) => check_operand(operand),
        Rvalue::BinaryOp(_, operands) => {
            check_operand(&operands.0)?;
            check_operand(&operands.1)
        }
        // `&(*x)` reborrows are deferred to lowering, which only accepts the
        // `Field::constant("...")` string-literal chain and rejects the rest.
        Rvalue::Ref(..) | Rvalue::CopyForDeref(..) => Ok(()),
        // Array construction / repeat; lowering restricts these to `Field` arrays.
        // `Aggregate` also builds the `Range { start, end }` of a `for` loop.
        Rvalue::Aggregate(..) | Rvalue::Repeat(..) => Ok(()),
        // `discriminant(_opt)` for a modeled range-iterator `Option`; lowering
        // rejects a discriminant of any value it can't const-fold.
        Rvalue::Discriminant(..) => Ok(()),
        Rvalue::RawPtr(..) => Err(unsupported_rvalue("raw pointers")),
        // Compile-time integer widening/narrowing (e.g. `v as u64` in the
        // `From<uN> for Field` conversions); other casts stay rejected.
        Rvalue::Cast(rustc_middle::mir::CastKind::IntToInt, ..) => Ok(()),
        Rvalue::Cast(..) => Err(unsupported_rvalue(
            "casts (only compile-time integer casts)",
        )),
        _ => Err(unsupported_rvalue("this expression")),
    }
}

fn unsupported_rvalue(what: &str) -> CompileError {
    CompileError::new(format!("unsupported operation inside circuit: {what}"))
}

fn check_terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    registry: &CallRegistry,
    kind: &TerminatorKind<'tcx>,
) -> CompileResult<()> {
    match kind {
        TerminatorKind::Return | TerminatorKind::Goto { .. } => Ok(()),
        TerminatorKind::Call {
            func, destination, ..
        } => {
            check_place(destination)?;
            let Some((def_id, generic_args)) = func.const_fn_def() else {
                return Err(CompileError::new(
                    "indirect / dynamic calls are not supported inside a circuit",
                ));
            };
            // A call is acceptable if it is a recognized call (keyed on the
            // pre-resolution `DefId`, as lowering does) or an ordinary function
            // whose MIR is available to inline (checked on the resolved impl).
            // Bodies of inlined callees are validated by lowering as walked.
            let resolved = crate::lower_mir::resolve_call_def_id(tcx, def_id, generic_args);
            if registry.classify(def_id).is_none() && !tcx.is_mir_available(resolved) {
                return Err(CompileError::new(format!(
                    "unsupported function call inside circuit: `{}`",
                    tcx.def_path_str(resolved)
                ))
                .with_note(
                    "only xark field operations, assert_eq, and functions whose MIR is \
                     available can be used",
                ));
            }
            Ok(())
        }
        // Compiler-inserted bounds/overflow checks; lowering follows the success
        // edge (indices are compile-time constants).
        TerminatorKind::Assert { .. } => Ok(()),
        // Compile-time-resolvable branches (loop conditions, `if CONST`).
        // Lowering rejects any that turn out to be witness-dependent.
        TerminatorKind::SwitchInt { .. } => Ok(()),
        // The `otherwise` edge of a `for`-loop's `switchInt(discriminant)` is an
        // `unreachable` block. Lowering never follows it (the discriminant is a
        // constant 0/1); if some path ever did, `walk_body` rejects it there.
        TerminatorKind::Unreachable => Ok(()),
        // A `Drop` in circuit code comes from a non-`Copy` value — in practice the
        // by-value `array::IntoIter` of `for x in arr`. Drops have no arithmetic
        // effect; lowering follows the success edge and ignores the drop. An
        // iterator we can't model is rejected later, when its `next` is lowered.
        TerminatorKind::Drop { .. } => Ok(()),
        _ => Err(CompileError::new(
            "unsupported control-flow construct inside circuit",
        )),
    }
}
