//! Entry-point discovery and signature parsing.
//!
//! Finds the single `pub fn circuit(...)` in the crate, and recovers each
//! parameter's visibility from the *syntactic* HIR type (`Private<Field>` /
//! `Public<Field>`). Visibility cannot be read from the semantic type because
//! `Private`/`Public` are transparent aliases erased during type checking.

use rustc_hir::def_id::LocalDefId;
use rustc_hir::{FnRetTy, ItemKind, PatKind, QPath, Ty, TyKind};
use rustc_middle::ty::TyCtxt;

use xark_ir::Visibility;

use crate::diagnostics::{CompileError, CompileResult};

pub struct CircuitInput {
    pub name: String,
    pub visibility: Visibility,
}

pub struct EntryInfo {
    pub def_id: LocalDefId,
    pub inputs: Vec<CircuitInput>,
}

/// Locate `fn circuit` and parse its signature.
pub fn find_circuit<'tcx>(tcx: TyCtxt<'tcx>) -> CompileResult<EntryInfo> {
    let mut matches = Vec::new();

    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        if let ItemKind::Fn { ident, .. } = item.kind {
            if ident.name.as_str() == "circuit" {
                matches.push(item_id);
            }
        }
    }

    match matches.len() {
        0 => {
            return Err(CompileError::new("no function named `circuit` found")
                .with_help("define `pub fn circuit(...)` as the circuit entry point"))
        }
        1 => {}
        n => {
            return Err(CompileError::new(format!(
                "found {n} functions named `circuit`, expected exactly one"
            )))
        }
    }

    let item = tcx.hir_item(matches[0]);
    let ItemKind::Fn { sig, body, .. } = item.kind else {
        unreachable!("filtered to Fn items above");
    };

    // Return type must be `()`.
    check_unit_return(&sig.decl.output)?;

    // Parameter visibilities from the syntactic types.
    let mut visibilities = Vec::new();
    for input_ty in sig.decl.inputs {
        visibilities.push(parse_visibility(input_ty)?);
    }

    // Parameter names from the body's patterns.
    let hir_body = tcx.hir_body(body);
    let mut names = Vec::new();
    for (i, param) in hir_body.params.iter().enumerate() {
        let name = match param.pat.kind {
            PatKind::Binding(_, _, ident, _) => ident.name.to_string(),
            _ => format!("arg{i}"),
        };
        names.push(name);
    }

    if names.len() != visibilities.len() {
        return Err(CompileError::new(
            "internal error: parameter name/type count mismatch",
        ));
    }

    let inputs = names
        .into_iter()
        .zip(visibilities)
        .map(|(name, visibility)| CircuitInput { name, visibility })
        .collect();

    Ok(EntryInfo {
        def_id: item.owner_id.def_id,
        inputs,
    })
}

fn check_unit_return(output: &FnRetTy<'_>) -> CompileResult<()> {
    match output {
        // No `->` means implicit `()`.
        FnRetTy::DefaultReturn(_) => Ok(()),
        FnRetTy::Return(ty) => match ty.kind {
            TyKind::Tup(elems) if elems.is_empty() => Ok(()),
            _ => Err(CompileError::new(
                "circuit function must return `()`",
            )
            .with_help("remove the return type; circuits only emit constraints")),
        },
    }
}

/// Map a syntactic parameter type to a [`Visibility`].
fn parse_visibility(ty: &Ty<'_>) -> CompileResult<Visibility> {
    let last = last_path_segment(ty);
    match last {
        Some("Private") => Ok(Visibility::Private),
        Some("Public") => Ok(Visibility::Public),
        Some("Field") => Err(CompileError::new(
            "bare `Field` circuit parameter is not allowed",
        )
        .with_help("wrap it in `Private<Field>` or `Public<Field>`")),
        Some(other) => Err(CompileError::new(format!(
            "unsupported circuit parameter type `{other}`"
        ))
        .with_help("use `Private<Field>` or `Public<Field>`")),
        None => Err(CompileError::new(
            "unsupported circuit parameter type",
        )
        .with_help("use `Private<Field>` or `Public<Field>`")),
    }
}

/// Return the final path segment identifier of a `TyKind::Path`, if any.
fn last_path_segment<'a>(ty: &'a Ty<'_>) -> Option<&'a str> {
    let TyKind::Path(qpath) = &ty.kind else {
        return None;
    };
    let path = match qpath {
        QPath::Resolved(_, path) => path,
        QPath::TypeRelative(_, seg) => return Some(seg.ident.name.as_str()),
    };
    path.segments.last().map(|s| s.ident.name.as_str())
}
