//! Entry-point discovery and signature parsing.
//!
//! Finds the circuit's entry function and recovers each parameter's visibility
//! from the *syntactic* HIR type (`Private<Field>` / `Public<Field>`).
//! Visibility can't be read from the semantic type because `Private`/`Public`
//! are transparent aliases erased during type checking.
//!
//! The entry is a `fn circuit` if present; otherwise it is auto-detected as the
//! single "circuit-shaped" free function (unit return, every parameter
//! `Public<_>`/`Private<_>`), so the entry can be named after the circuit and
//! that name names the proof bundle and the generated `<Fn>Inputs` struct.

use rustc_hir::def_id::LocalDefId;
use rustc_hir::{FnRetTy, ItemId, ItemKind, PatKind, QPath, Ty, TyKind};
use rustc_middle::ty::TyCtxt;

use xark_ir::Visibility;

use crate::diagnostics::{CompileError, CompileResult};

pub struct CircuitInput {
    pub name: String,
    pub visibility: Visibility,
}

pub struct EntryInfo {
    pub def_id: LocalDefId,
    /// The entry function's name — names the proof bundle and the generated
    /// `<Fn>Inputs` struct (e.g. `cube` → `CubeInputs`).
    pub name: String,
    pub inputs: Vec<CircuitInput>,
}

/// Locate the circuit entry function and parse its signature. Prefers a
/// `fn circuit`; otherwise auto-detects the single circuit-shaped free function.
pub fn find_circuit<'tcx>(tcx: TyCtxt<'tcx>) -> CompileResult<EntryInfo> {
    let fns: Vec<(ItemId, String)> = tcx
        .hir_free_items()
        .filter_map(|item_id| match tcx.hir_item(item_id).kind {
            ItemKind::Fn { ident, .. } => Some((item_id, ident.name.to_string())),
            _ => None,
        })
        .collect();

    // A `fn circuit` is the explicit entry (back-compatible). Failing that,
    // auto-detect the single circuit-shaped fn so the entry can be named freely.
    let named: Vec<&(ItemId, String)> = fns.iter().filter(|(_, n)| n == "circuit").collect();
    let (item_id, name) = match named.len() {
        1 => (named[0].0, named[0].1.clone()),
        n if n > 1 => {
            return Err(CompileError::new(format!(
                "found {n} functions named `circuit`, expected exactly one"
            )))
        }
        _ => {
            let candidates: Vec<&(ItemId, String)> = fns
                .iter()
                .filter(|(id, _)| is_circuit_shaped(tcx, *id))
                .collect();
            match candidates.len() {
                1 => (candidates[0].0, candidates[0].1.clone()),
                0 => return Err(
                    CompileError::new("no circuit entry function found").with_help(
                        "define a `pub fn` whose parameters are all `Public<_>` / `Private<_>` \
                         (or name it `circuit`)",
                    ),
                ),
                _ => {
                    let names: Vec<&str> = candidates.iter().map(|(_, n)| n.as_str()).collect();
                    return Err(CompileError::new(format!(
                        "multiple candidate circuit functions ({}); name the entry `circuit` \
                         to disambiguate",
                        names.join(", ")
                    )));
                }
            }
        }
    };

    let item = tcx.hir_item(item_id);
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
        name,
        inputs,
    })
}

/// Whether a free function looks like a circuit entry: `pub`, unit return, at
/// least one parameter, every one a `Public<_>` / `Private<_>`. Used only to
/// auto-detect the entry when no `fn circuit` is present, so it must not error.
///
/// The `pub` requirement (matching the help text) keeps private helper functions
/// — which can legitimately take `Private<_>`/`Public<_>` params — from being
/// mistaken for the entry or colliding with it.
fn is_circuit_shaped(tcx: TyCtxt<'_>, item_id: ItemId) -> bool {
    if !tcx.visibility(item_id.owner_id.def_id).is_public() {
        return false;
    }
    let ItemKind::Fn { sig, .. } = tcx.hir_item(item_id).kind else {
        return false;
    };
    if !returns_unit(&sig.decl.output) || sig.decl.inputs.is_empty() {
        return false;
    }
    sig.decl
        .inputs
        .iter()
        .all(|ty| matches!(last_path_segment(ty), Some("Public") | Some("Private")))
}

/// Non-erroring form of [`check_unit_return`].
fn returns_unit(output: &FnRetTy<'_>) -> bool {
    match output {
        FnRetTy::DefaultReturn(_) => true,
        FnRetTy::Return(ty) => matches!(ty.kind, TyKind::Tup(elems) if elems.is_empty()),
    }
}

fn check_unit_return(output: &FnRetTy<'_>) -> CompileResult<()> {
    match output {
        // No `->` means implicit `()`.
        FnRetTy::DefaultReturn(_) => Ok(()),
        FnRetTy::Return(ty) => match ty.kind {
            TyKind::Tup([]) => Ok(()),
            _ => Err(CompileError::new("circuit function must return `()`")
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
        Some("Field") => Err(
            CompileError::new("bare `Field` circuit parameter is not allowed")
                .with_help("wrap it in `Private<Field>` or `Public<Field>`"),
        ),
        Some(other) => Err(CompileError::new(format!(
            "unsupported circuit parameter type `{other}`"
        ))
        .with_help("use `Private<Field>` or `Public<Field>`")),
        None => Err(CompileError::new("unsupported circuit parameter type")
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
