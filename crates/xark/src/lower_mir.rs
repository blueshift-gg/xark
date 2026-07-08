//! Lower a validated MIR `Body` for `circuit` into an [`R1csProgram`].
//!
//! The lowering follows the CFG from the start block through `Goto`/`Call`
//! terminators (the accepted subset is straight-line). Field arithmetic appears
//! as calls to recognized `xark` operators; additions/subtractions/negations
//! stay as linear combinations, and only genuine multiplications allocate a
//! fresh internal variable and emit a constraint.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{
    Body, Const, ConstOperand, ConstValue, Operand, Place, Rvalue, StatementKind, TerminatorKind,
    START_BLOCK,
};
use rustc_middle::ty::TyCtxt;

use xark_ir::primitive::{self, PrimitiveProgram, WitnessGen};
use xark_ir::{
    FieldSpec, LinearCombination, R1csConstraint, R1csProgram, Variable, VarId, Visibility,
};

use crate::diagnostics::{CompileError, CompileResult};
use crate::find_entry::EntryInfo;

/// Recognized circuit calls.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KnownCall {
    Add,
    Sub,
    Mul,
    Neg,
    PowU64,
    ConstrainEq,
    FieldConstantU64,
    FieldConstantU128,
    FieldConstantDecimal,
    Advice,
    HintInverse,
    HintInverseOrZero,
    HintBit,
    HintDivRem,
    // Width-generic (`Bignum`) hints: `N` limbs inferred from the array arg,
    // `bits` from the trailing `usize` arg; tuple returns.
    HintMulModDivMod,
    HintModInverse,
    HintSub2,
    Xor,
    Or,
}

/// Classify a called function by its fully-qualified path.
/// Resolve a (possibly trait-method) call to its concrete monomorphized impl
/// `DefId`. The MIR references trait methods like `<Field as From<u8>>::from`
/// as the generic `core::convert::From::from` (no MIR); resolving with the
/// call's generic args points them at the impl (which has MIR and whose def
/// path still ends in the recognized suffix). Falls back to the original id.
pub(crate) fn resolve_call_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    generic_args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Option<rustc_middle::ty::Instance<'tcx>> {
    let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
    rustc_middle::ty::Instance::try_resolve(tcx, typing_env, def_id, generic_args)
        .ok()
        .flatten()
}

pub(crate) fn resolve_call_def_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    generic_args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> DefId {
    resolve_call_instance(tcx, def_id, generic_args)
        .map(|inst| inst.def_id())
        .unwrap_or(def_id)
}

pub(crate) fn classify_call(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> Option<KnownCall> {
    let s = tcx.def_path_str(def_id);
    if s.ends_with("::assert_eq") {
        Some(KnownCall::ConstrainEq)
    // Every `Field`-method arm is gated on the path containing `Field`, so a
    // same-named method on another type (`Bool::or`, `Bignum::mul`) isn't
    // misclassified as the intrinsic; the `__xark_*` names stay unconditional.
    } else if s.contains("__xark_pow_u64") || (s.contains("Field") && s.ends_with("::bitxor")) {
        Some(KnownCall::PowU64)
    } else if s.contains("__xark_add")
        || (s.contains("Field") && s.ends_with("::add") && binop_rhs_is_field(tcx, def_id))
    {
        Some(KnownCall::Add)
    } else if s.contains("__xark_sub")
        || (s.contains("Field") && s.ends_with("::sub") && binop_rhs_is_field(tcx, def_id))
    {
        Some(KnownCall::Sub)
    } else if s.contains("__xark_mul")
        || (s.contains("Field") && s.ends_with("::mul") && binop_rhs_is_field(tcx, def_id))
    {
        Some(KnownCall::Mul)
    } else if s.contains("__xark_neg") || (s.contains("Field") && s.ends_with("::neg")) {
        Some(KnownCall::Neg)
    } else if s.contains("constant_u128") {
        Some(KnownCall::FieldConstantU128)
    } else if s.contains("constant_u64") {
        Some(KnownCall::FieldConstantU64)
    } else if s.contains("Field") && s.ends_with("::constant") {
        Some(KnownCall::FieldConstantDecimal)
    } else if s.contains("__xark_hint_inverse_or_zero")
        || (s.contains("Field") && s.ends_with("::hint_inverse_or_zero"))
    {
        // Must precede the `hint_inverse` arm: `__xark_hint_inverse` is a prefix
        // of `__xark_hint_inverse_or_zero`, so `contains` would misclassify it.
        Some(KnownCall::HintInverseOrZero)
    } else if s.contains("__xark_hint_inverse")
        || (s.contains("Field") && s.ends_with("::hint_inverse"))
    {
        Some(KnownCall::HintInverse)
    } else if s.contains("__xark_hint_bit") || (s.contains("Field") && s.ends_with("::hint_bit")) {
        Some(KnownCall::HintBit)
    } else if s.contains("__xark_hint_div_rem")
        || (s.contains("Field") && s.ends_with("::hint_div_rem"))
    {
        Some(KnownCall::HintDivRem)
    } else if s.contains("__xark_hint_mulmod_divmod")
        || (s.contains("Field") && s.ends_with("::hint_mulmod_divmod"))
    {
        Some(KnownCall::HintMulModDivMod)
    } else if s.contains("__xark_hint_sub2")
        || (s.contains("Field") && s.ends_with("::hint_sub2"))
    {
        Some(KnownCall::HintSub2)
    } else if s.contains("__xark_hint_mod_inverse")
        || (s.contains("Field") && s.ends_with("::hint_mod_inverse"))
    {
        Some(KnownCall::HintModInverse)
    } else if s.contains("__xark_xor") || (s.contains("Field") && s.ends_with("::xor")) {
        Some(KnownCall::Xor)
    } else if s.contains("__xark_or") || (s.contains("Field") && s.ends_with("::or")) {
        Some(KnownCall::Or)
    } else if s.contains("__xark_advice") || (s.contains("Field") && s.ends_with("::advice")) {
        Some(KnownCall::Advice)
    } else {
        None
    }
}

/// True if `def_id`'s second parameter is `Field`. Distinguishes the
/// `Field`-`Field` operator methods (`<Field as Mul>::mul`, which we intercept as
/// the field intrinsic) from the native-int convenience operators
/// (`<Field as Mul<u64>>::mul` etc.), which have a `u64`/`u32`/… RHS and must be
/// *inlined* — their body forwards to `self * Field::from(rhs)`.
fn binop_rhs_is_field(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> bool {
    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
    sig.inputs().get(1).is_some_and(|t| {
        matches!(t.ty_adt_def(), Some(d) if tcx.item_name(d.did()).as_str() == "Field")
    })
}

/// One inlining frame's local state. Values are keyed by `Local`, then by
/// projection path (`[]` for a scalar, `[i]`/`[i, j]` for array elements /
/// tuple fields), so slot lookups/copies stay local to a single variable
/// instead of scanning a whole-program map. Frames are pushed on inline and
/// popped on return, so live memory is bounded by call-stack depth.
#[derive(Default)]
struct Frame {
    // Path-keyed slot maps use `BTreeMap` so iteration is deterministic and
    // path-sorted — array/tuple slots reconstruct in index order regardless of
    // insertion, avoiding order-dependent lowering bugs.
    field: BTreeMap<rustc_middle::mir::Local, BTreeMap<Vec<u64>, LinearCombination>>,
    int: BTreeMap<rustc_middle::mir::Local, BTreeMap<Vec<u64>, u128>>,
    str: BTreeMap<rustc_middle::mir::Local, String>,
}

struct LoweringEnv<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Inlining frame stack; the last element is the current frame.
    frames: Vec<Frame>,
    variables: Vec<Variable>,
    var_names: Vec<String>,
    constraints: Vec<R1csConstraint>,
    next_var_id: VarId,
    internal_counter: u32,
    advice_counter: u32,
    next_constraint_id: u32,
    /// Maps an allocated multiplication-output var to `(constraint index,
    /// witness-gen index)`, while it is still eligible for merging into a
    /// following `assert_eq`.
    pending_mul: BTreeMap<VarId, (usize, usize)>,
    /// Multiplication outputs whose defining row was folded into a following
    /// `assert_eq` (the merge dropped their `Product` witness-gen and repurposed
    /// their `a·b = out` row into `a·b = target`). Maps the output var to
    /// `(a, b, witness_gen_index)` so `finish` can *revive* it — re-pin
    /// `a·b = out` and restore its `Product` — IF the var turns out to be
    /// referenced again after the merge. Without this, reusing a product after
    /// asserting it (`let t = a*b; assert_eq(t, c); assert_eq(t, d);`) leaves `t`
    /// a free witness detached from `a·b` — a silent under-constraint that a
    /// malicious prover could exploit.
    merged: BTreeMap<VarId, (LinearCombination, LinearCombination, usize)>,
    /// The witness-generation ("hint") program, in dependency order. `None`
    /// entries are ops whose output var was merged away (dropped at finish).
    witness_gen: Vec<Option<WitnessGen>>,
    /// Stack of function `DefId`s currently being inlined (recursion guard).
    inlining: Vec<DefId>,
    /// Parallel to `inlining`: the generic args of each inlined instance, used
    /// to monomorphize nested calls in a generic callee body (e.g. the blanket
    /// `Into::into`, whose body calls `From::from` with the impl's type params).
    inline_substs: Vec<rustc_middle::ty::GenericArgsRef<'tcx>>,
}

/// A value passed into or returned from an inlined function. `Fields` carries a
/// whole scalar-or-array value as `(relative-path, lc)` slots — a scalar is a
/// single `([], lc)`, an array is `([0], ..), ([1], ..), ...`.
enum ArgValue {
    Fields(Vec<(Vec<u64>, LinearCombination)>),
    Int(u128),
    Str(String),
    Unit,
}

impl<'tcx> LoweringEnv<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        LoweringEnv {
            tcx,
            frames: vec![Frame::default()],
            variables: Vec::new(),
            var_names: Vec::new(),
            constraints: Vec::new(),
            next_var_id: 0,
            internal_counter: 0,
            advice_counter: 0,
            next_constraint_id: 0,
            pending_mul: BTreeMap::new(),
            merged: BTreeMap::new(),
            witness_gen: Vec::new(),
            inlining: Vec::new(),
            inline_substs: Vec::new(),
        }
    }

    // --- frame-scoped local access -----------------------------------------

    fn frame(&self) -> &Frame {
        self.frames.last().expect("at least one frame")
    }
    fn frame_mut(&mut self) -> &mut Frame {
        self.frames.last_mut().expect("at least one frame")
    }

    fn set_field(&mut self, local: rustc_middle::mir::Local, lc: LinearCombination) {
        self.set_field_at(local, &[], lc);
    }
    fn get_field_at(&self, local: rustc_middle::mir::Local, path: &[u64]) -> Option<LinearCombination> {
        self.frame().field.get(&local)?.get(path).cloned()
    }
    fn set_field_at(&mut self, local: rustc_middle::mir::Local, path: &[u64], lc: LinearCombination) {
        self.frame_mut()
            .field
            .entry(local)
            .or_default()
            .insert(path.to_vec(), lc);
    }

    /// Resolve a place to `(base local, constant projection path)`.
    ///
    /// Only array `Index`/`ConstantIndex` projections with compile-time-constant
    /// indices are supported; the loop unroller ensures indices are constant.
    fn resolve_place(&self, place: &Place<'tcx>) -> CompileResult<(rustc_middle::mir::Local, Vec<u64>)> {
        let mut path = Vec::new();
        for elem in place.projection.iter() {
            match elem {
                rustc_middle::mir::ProjectionElem::Index(idx_local) => {
                    let idx = self.get_int(idx_local).ok_or_else(|| {
                        CompileError::new("array index must be a compile-time constant")
                            .with_note("witness-dependent indexing is not supported")
                            .with_help(
                                "use a literal index or a loop variable the unroller can fold to a \
                                 constant; for a data-dependent choice, use `select`",
                            )
                    })?;
                    path.push(idx as u64);
                }
                rustc_middle::mir::ProjectionElem::ConstantIndex {
                    offset,
                    from_end: false,
                    ..
                } => path.push(offset),
                // Tuple/struct field access (e.g. the `(u64, bool)` result of an
                // overflow-checked add).
                rustc_middle::mir::ProjectionElem::Field(field, _) => {
                    path.push(field.as_u32() as u64)
                }
                other => {
                    return Err(CompileError::new(format!(
                        "unsupported place projection: {other:?}"
                    )))
                }
            }
        }
        Ok((place.local, path))
    }
    fn get_int(&self, local: rustc_middle::mir::Local) -> Option<u128> {
        self.get_int_at(local, &[])
    }
    fn set_int(&mut self, local: rustc_middle::mir::Local, v: u128) {
        self.set_int_at(local, &[], v);
    }
    fn get_int_at(&self, local: rustc_middle::mir::Local, path: &[u64]) -> Option<u128> {
        self.frame().int.get(&local)?.get(path).copied()
    }
    fn set_int_at(&mut self, local: rustc_middle::mir::Local, path: &[u64], v: u128) {
        self.frame_mut()
            .int
            .entry(local)
            .or_default()
            .insert(path.to_vec(), v);
    }
    fn get_str(&self, local: rustc_middle::mir::Local) -> Option<String> {
        self.frame().str.get(&local).cloned()
    }
    fn set_str(&mut self, local: rustc_middle::mir::Local, s: String) {
        self.frame_mut().str.insert(local, s);
    }
    /// Drop all slots (field / int / str) tracked for `local` in the current
    /// frame — used on `StorageLive` so a reused local starts clean.
    fn clear_local(&mut self, local: rustc_middle::mir::Local) {
        let f = self.frame_mut();
        f.field.remove(&local);
        f.int.remove(&local);
        f.str.remove(&local);
    }
    /// Generic args of the innermost inlined callee (identity at the top level),
    /// applied to monomorphize nested calls before resolving them.
    fn cur_substs(&self) -> rustc_middle::ty::GenericArgsRef<'tcx> {
        self.inline_substs
            .last()
            .copied()
            .unwrap_or_else(|| rustc_middle::ty::GenericArgs::empty())
    }

    /// Enter a fresh inlining frame. Returns nothing; [`Self::exit_frame`] pops.
    fn enter_frame(&mut self) {
        self.frames.push(Frame::default());
    }
    /// Pop the current inlining frame, freeing all its locals at once.
    fn exit_frame(&mut self) {
        self.frames.pop();
        debug_assert!(!self.frames.is_empty(), "popped the root frame");
    }

    fn alloc_var(&mut self, name: String, visibility: Visibility) -> VarId {
        let id = self.next_var_id;
        self.next_var_id += 1;
        self.variables.push(Variable {
            id,
            name: name.clone(),
            visibility,
        });
        self.var_names.push(name);
        id
    }

    fn alloc_internal(&mut self) -> VarId {
        let name = format!("t{}", self.internal_counter);
        self.internal_counter += 1;
        self.alloc_var(name, Visibility::Internal)
    }

    /// Allocate a fresh private *advice* (prover-supplied witness) variable.
    fn alloc_advice(&mut self) -> VarId {
        let name = format!("w{}", self.advice_counter);
        self.advice_counter += 1;
        self.alloc_var(name, Visibility::Private)
    }

    fn fresh_constraint_id(&mut self) -> u32 {
        let id = self.next_constraint_id;
        self.next_constraint_id += 1;
        id
    }

    // --- rendering (for debug notes) ---------------------------------------

    fn render_lc(&self, lc: &LinearCombination) -> String {
        // Debug notes for large linear combinations (long bitwise chains, e.g.
        // Keccak) are expensive to format and useless to read; summarize them.
        if lc.terms.len() > 24 {
            return format!("<lc: {} terms>", lc.terms.len());
        }
        let mut s = String::new();
        let mut first = true;
        for term in &lc.terms {
            let name = &self.var_names[term.var as usize];
            let (neg, is_one, abs) = term.coeff.render_parts();
            let token = if is_one { name.clone() } else { format!("{abs}*{name}") };
            if first {
                if neg {
                    s.push('-');
                }
                s.push_str(&token);
                first = false;
            } else {
                s.push_str(&format!(" {} {token}", if neg { "-" } else { "+" }));
            }
        }
        if !lc.constant.is_zero() {
            let (neg, _, mag) = lc.constant.render_parts();
            if first {
                s.push_str(&lc.constant.decimal);
            } else {
                s.push_str(&format!(" {} {mag}", if neg { "-" } else { "+" }));
            }
        } else if first {
            s.push('0');
        }
        s
    }

    /// Render one operand of a multiplication, wrapping compound LCs in parens.
    fn render_side(&self, lc: &LinearCombination) -> String {
        let compound = lc.terms.len() + usize::from(!lc.constant.is_zero()) > 1;
        let inner = self.render_lc(lc);
        if compound {
            format!("({inner})")
        } else {
            inner
        }
    }

    // --- operand helpers ----------------------------------------------------

    fn place_local(place: &Place<'_>) -> CompileResult<rustc_middle::mir::Local> {
        if !place.projection.is_empty() {
            return Err(CompileError::new(
                "projections (fields, indexing, dereference) are not supported",
            ));
        }
        Ok(place.local)
    }

    fn operand_to_lc(&self, operand: &Operand<'tcx>) -> CompileResult<LinearCombination> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let (local, path) = self.resolve_place(place)?;
                self.get_field_at(local, &path).ok_or_else(|| {
                    CompileError::new("use of a value that is not a supported field expression")
                        .with_help(
                            "this position needs a `Field` (or `Bool`/`U<N>` wrapping one); a host \
                             `bool`/integer, or a value from an operation the circuit can't lower, \
                             can't be used here",
                        )
                })
            }
            // A `Field`-typed constant used directly as an operand — e.g.
            // `Field::from(3)` behind `a + 3` (the `Add<u64>` etc. operators) —
            // lowers to a constant linear combination.
            // A `Field`-typed constant used directly as an operand — e.g. an
            // associated `const` — lowers to a constant linear combination.
            Operand::Constant(c) => self
                .const_field_slots(c)
                .and_then(|slots| slots.into_iter().find(|(p, _)| p.is_empty()).map(|(_, lc)| lc))
                .ok_or_else(|| CompileError::new("unexpected constant in a field position")),
            Operand::RuntimeChecks(_) => Err(CompileError::new(
                "unexpected constant in a field position",
            )),
        }
    }

    /// Read an integer constant, evaluating named/associated `const`s (e.g. a
    /// `const N: usize = 3` used as a loop bound), not just literals.
    fn const_to_u128(&self, c: &ConstOperand<'tcx>) -> Option<u128> {
        if let Some(s) = c.const_.try_to_scalar_int() {
            return Some(s.to_uint(s.size()));
        }
        let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
        // Substitute const-generic params (e.g. `N` in a `mod_mul::<N>` gadget
        // used as a loop bound) with the current inlining frame's args before
        // evaluating, so const-generic gadgets const-fold instead of looking
        // witness-dependent.
        let konst = self.tcx.instantiate_and_normalize_erasing_regions(
            self.cur_substs(),
            typing_env,
            rustc_middle::ty::EarlyBinder::bind(c.const_),
        );
        let s = konst.try_eval_scalar_int(self.tcx, typing_env)?;
        Some(s.to_uint(s.size()))
    }

    /// If `c` is a compile-time array of integers (e.g. a `const P: [u128; 3]`
    /// item referenced as `_1 = const P`), populate `dest`'s per-element int
    /// slots. This lets a curve gadget declare its field constants as ordinary
    /// `const` arrays and read them with `Field::from(P[i])` — the index projection
    /// then resolves to a tracked int slot. Returns whether it applied.
    fn try_bind_const_int_array(
        &mut self,
        dest: rustc_middle::mir::Local,
        c: &ConstOperand<'tcx>,
    ) -> bool {
        use rustc_middle::ty::{self, TyKind};
        let TyKind::Array(elem_ty, _) = c.const_.ty().kind() else {
            return false;
        };
        if !elem_ty.is_integral() {
            return false;
        }
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let konst = self.tcx.instantiate_and_normalize_erasing_regions(
            self.cur_substs(),
            typing_env,
            rustc_middle::ty::EarlyBinder::bind(c.const_),
        );
        let valtree = match konst {
            Const::Ty(_, ct) => match ct.kind() {
                ty::ConstKind::Value(v) => Some(v.valtree),
                _ => None,
            },
            Const::Unevaluated(uv, _) => self
                .tcx
                .const_eval_resolve_for_typeck(
                    typing_env,
                    ty::UnevaluatedConst::new(uv.def, uv.args),
                    rustc_span::DUMMY_SP,
                )
                .ok()
                .and_then(|r| r.ok()),
            Const::Val(..) => None,
        };
        let Some(valtree) = valtree else { return false };
        let Some(branch) = valtree.try_to_branch() else { return false };
        for (i, elem) in branch.iter().enumerate() {
            let ty::ConstKind::Value(v) = elem.kind() else {
                return false;
            };
            let Some(scalar) = v.valtree.try_to_leaf() else {
                return false;
            };
            self.set_int_at(dest, &[i as u64], scalar.to_uint(scalar.size()));
        }
        true
    }

    /// The interned value-tree of a (possibly const-generic) constant operand.
    fn const_valtree(&self, c: Const<'tcx>) -> Option<rustc_middle::ty::ValTree<'tcx>> {
        use rustc_middle::ty;
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let konst = self.tcx.instantiate_and_normalize_erasing_regions(
            self.cur_substs(),
            typing_env,
            rustc_middle::ty::EarlyBinder::bind(c),
        );
        match konst {
            Const::Ty(_, ct) => match ct.kind() {
                ty::ConstKind::Value(v) => Some(v.valtree),
                _ => None,
            },
            Const::Unevaluated(uv, _) => self
                .tcx
                .const_eval_resolve_for_typeck(
                    typing_env,
                    ty::UnevaluatedConst::new(uv.def, uv.args),
                    rustc_span::DUMMY_SP,
                )
                .ok()
                .and_then(|r| r.ok()),
            Const::Val(..) => None,
        }
    }

    /// Decode a `const Field`'s value-tree — a `Field { _limbs: [u64; 4] }` — into
    /// its decimal string.
    fn field_valtree_decimal(vt: rustc_middle::ty::ValTree<'tcx>) -> Option<String> {
        use rustc_middle::ty;
        // The struct's single field `_limbs: [u64; 4]`.
        let limbs_const = *vt.try_to_branch()?.first()?;
        let ty::ConstKind::Value(lv) = limbs_const.kind() else { return None };
        let limb_consts = lv.valtree.try_to_branch()?;
        let mut limbs = [0u64; 4];
        for (i, lc) in limb_consts.iter().take(4).enumerate() {
            let ty::ConstKind::Value(x) = lc.kind() else { return None };
            let s = x.valtree.try_to_leaf()?;
            limbs[i] = s.to_uint(s.size()) as u64;
        }
        Some(limbs_to_decimal(limbs))
    }

    /// If `c` is a `const Field` or `const [Field; N]` (e.g. a curve gadget's
    /// associated `const MODULUS: [Field; 3]`), decode it into `(relative-path,
    /// constant LC)` field slots. Returns `None` if `c` is not a `Field` constant.
    fn const_field_slots(
        &self,
        c: &ConstOperand<'tcx>,
    ) -> Option<Vec<(Vec<u64>, LinearCombination)>> {
        use rustc_middle::ty::TyKind;
        let is_array = matches!(c.const_.ty().kind(), TyKind::Array(..));
        let elem_ty = match c.const_.ty().kind() {
            TyKind::Array(elem, _) => *elem,
            _ => c.const_.ty(),
        };
        if !matches!(elem_ty.ty_adt_def(), Some(d)
            if self.tcx.item_name(d.did()).as_str() == "Field")
        {
            return None;
        }
        let valtree = self.const_valtree(c.const_)?;
        let mut out = Vec::new();
        if is_array {
            for (i, elem) in valtree.try_to_branch()?.iter().enumerate() {
                let rustc_middle::ty::ConstKind::Value(v) = elem.kind() else {
                    return None;
                };
                let dec = Self::field_valtree_decimal(v.valtree)?;
                out.push((vec![i as u64], LinearCombination::constant(dec)));
            }
        } else {
            let dec = Self::field_valtree_decimal(valtree)?;
            out.push((Vec::new(), LinearCombination::constant(dec)));
        }
        Some(out)
    }

    /// Evaluate a type-level `Const` (e.g. an array length `N`) to `usize`,
    /// substituting const-generic params via the current frame's args first.
    fn eval_const_usize(&self, c: rustc_middle::ty::Const<'tcx>) -> Option<u64> {
        let c = self.tcx.instantiate_and_normalize_erasing_regions(
            self.cur_substs(),
            rustc_middle::ty::TypingEnv::fully_monomorphized(),
            rustc_middle::ty::EarlyBinder::bind(c),
        );
        c.try_to_target_usize(self.tcx)
    }


    /// Read a compile-time integer operand (constant or tracked int local,
    /// possibly a tuple-field projection like `_x.0`).
    fn operand_to_int(&self, operand: &Operand<'tcx>) -> Option<i128> {
        match operand {
            Operand::Constant(c) => self.const_to_u128(c).map(|v| v as i128),
            Operand::Copy(place) | Operand::Move(place) => {
                let (local, path) = self.resolve_place(place).ok()?;
                self.get_int_at(local, &path).map(|v| v as i128)
            }
            Operand::RuntimeChecks(_) => None,
        }
    }

    /// Read an array operand (`[Field; N]`) as its linear combinations, ordered
    /// by index. The length is inferred from the (already-monomorphized) slots —
    /// used by the width-generic `Bignum` hints.
    fn operand_to_lc_array_dyn(
        &self,
        operand: &Operand<'tcx>,
    ) -> CompileResult<Vec<LinearCombination>> {
        let (Operand::Copy(place) | Operand::Move(place)) = operand else {
            return Err(CompileError::new("expected a `[Field; N]` array argument"));
        };
        let (local, base) = self.resolve_place(place)?;
        let mut slots = self.collect_field_slots(local, &base);
        slots.sort_by_key(|(p, _)| p.first().copied().unwrap_or(0));
        Ok(slots.into_iter().map(|(_, lc)| lc).collect())
    }

    /// Read a compile-time unsigned integer operand (constant or tracked int
    /// slot). The slot model is `u128`, so this preserves the full width.
    fn operand_to_u128(&self, operand: &Operand<'tcx>) -> CompileResult<u128> {
        // An integer position (loop bound, `^` exponent, array length, `U<N>`
        // width, bit index) must be known at compile time — it shapes the
        // constraint system, which is fixed before any witness exists.
        let want_const = || {
            CompileError::new("expected a constant integer").with_help(
                "this must be a compile-time constant (loop bound, `^` exponent, array length, \
                 `U<N>` width, …), not a witness or runtime value",
            )
        };
        match operand {
            Operand::Constant(c) => self.const_to_u128(c).ok_or_else(want_const),
            Operand::Copy(place) | Operand::Move(place) => {
                let local = Self::place_local(place)?;
                self.get_int(local).ok_or_else(want_const)
            }
            Operand::RuntimeChecks(_) => Err(want_const()),
        }
    }

    /// `u64` view for `u64`-typed positions (exponents, `constant_u64` args).
    fn operand_to_u64(&self, operand: &Operand<'tcx>) -> CompileResult<u64> {
        self.operand_to_u128(operand).map(|v| v as u64)
    }

    /// Read a `&str` literal operand (for `Field::constant("...")`), resolving
    /// through the `_a = const "..."; _b = &(*_a)` reborrow chain if needed.
    fn operand_to_str(&self, operand: &Operand<'tcx>) -> CompileResult<String> {
        let want_literal = || {
            CompileError::new("`Field::constant` expects a string literal argument").with_help(
                "pass a decimal string literal, e.g. `Field::constant(\"12345\")`; for values that \
                 fit in `u128` prefer `Field::from(n)`",
            )
        };
        let c = match operand {
            Operand::Constant(c) => c,
            Operand::Copy(place) | Operand::Move(place) => {
                return self.get_str(place.local).ok_or_else(want_literal)
            }
            Operand::RuntimeChecks(_) => return Err(want_literal()),
        };
        Self::const_to_str(self.tcx, c)
    }

    fn const_to_str(tcx: TyCtxt<'tcx>, c: &ConstOperand<'tcx>) -> CompileResult<String> {
        let cv = match c.const_ {
            Const::Val(cv, _ty) => cv,
            _ => {
                return Err(CompileError::new(
                    "`Field::constant` expects a literal string (got an unevaluated constant)",
                ))
            }
        };
        // Only slice-shaped constants carry string bytes; calling the byte
        // accessor on anything else (e.g. the unit `()`) would ICE.
        if !matches!(cv, ConstValue::Slice { .. } | ConstValue::Indirect { .. }) {
            return Err(CompileError::new("not a string literal"));
        }
        let bytes = cv
            .try_get_slice_bytes_for_diagnostics(tcx)
            .ok_or_else(|| CompileError::new("could not read `Field::constant` string literal"))?;
        let s = std::str::from_utf8(bytes)
            .map_err(|_| CompileError::new("`Field::constant` literal is not valid UTF-8"))?;
        Ok(s.to_string())
    }

    // --- inlining support --------------------------------------------------

    /// Collect all field slots under `(local, base_path)` as `(relative-path, lc)`
    /// pairs — one entry for a scalar, N for an array.
    fn collect_field_slots(
        &self,
        local: rustc_middle::mir::Local,
        base: &[u64],
    ) -> Vec<(Vec<u64>, LinearCombination)> {
        let Some(slots) = self.frame().field.get(&local) else {
            return Vec::new();
        };
        slots
            .iter()
            .filter(|(p, _)| p.len() >= base.len() && p[..base.len()] == *base)
            .map(|(p, lc)| (p[base.len()..].to_vec(), lc.clone()))
            .collect()
    }

    /// Like [`Self::collect_field_slots`] but *moves* the slots out of the frame
    /// (draining them) instead of cloning. Cloning a `LinearCombination` deep-
    /// copies its `Vec<Term>`; moving is O(1). Used for `Move` operands and
    /// return values, which is the bulk of nested-array passing (e.g. Keccak's
    /// per-round state hand-off).
    fn take_field_slots(
        &mut self,
        local: rustc_middle::mir::Local,
        base: &[u64],
    ) -> Vec<(Vec<u64>, LinearCombination)> {
        let Some(map) = self.frame_mut().field.get_mut(&local) else {
            return Vec::new();
        };
        let keys: Vec<Vec<u64>> = map
            .keys()
            .filter(|p| p.len() >= base.len() && p[..base.len()] == *base)
            .cloned()
            .collect();
        let mut out = Vec::with_capacity(keys.len());
        for k in keys {
            let lc = map.remove(&k).expect("key just listed");
            out.push((k[base.len()..].to_vec(), lc));
        }
        out
    }

    /// Store an operand (a scalar `Field` or a whole `Field` array) into
    /// `(dest, base)`, copying all of its field slots at their relative paths.
    /// Used for (possibly nested) array-literal and repeat construction.
    fn store_operand_slots(
        &mut self,
        dest: rustc_middle::mir::Local,
        base: &[u64],
        operand: &Operand<'tcx>,
    ) -> CompileResult<()> {
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            let (local, src_base) = self.resolve_place(place)?;
            let slots = self.collect_field_slots(local, &src_base);
            if !slots.is_empty() {
                for (rel, lc) in slots {
                    let mut path = base.to_vec();
                    path.extend(rel);
                    self.set_field_at(dest, &path, lc);
                }
                return Ok(());
            }
        }
        // Fall back to a scalar field value (e.g. a constant element). A ZST /
        // non-circuit field (e.g. `PhantomData`, `()`) yields nothing and is
        // simply skipped rather than rejected.
        if let Ok(lc) = self.operand_to_lc(operand) {
            self.set_field_at(dest, base, lc);
        }
        Ok(())
    }

    /// Evaluate a call argument in the current frame into a passable value.
    /// Handles whole `Field` arrays, not just scalars.
    fn eval_arg(&mut self, operand: &Operand<'tcx>) -> ArgValue {
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            if let Ok((local, base)) = self.resolve_place(place) {
                let slots = self.collect_field_slots(local, &base);
                if !slots.is_empty() {
                    return ArgValue::Fields(slots);
                }
                if let Some(v) = self.get_int_at(local, &base) {
                    return ArgValue::Int(v);
                }
                if base.is_empty() {
                    if let Some(s) = self.get_str(local) {
                        return ArgValue::Str(s);
                    }
                }
                return ArgValue::Unit;
            }
        }
        if let Operand::Constant(c) = operand {
            // A `const Field` / `[Field; N]` passed directly as an argument
            // (e.g. `mod_mul(.., P::MODULUS)` with an associated-const modulus).
            if let Some(slots) = self.const_field_slots(c) {
                return ArgValue::Fields(slots);
            }
        }
        if let Ok(n) = self.operand_to_u128(operand) {
            ArgValue::Int(n)
        } else if let Ok(s) = self.operand_to_str(operand) {
            ArgValue::Str(s)
        } else {
            ArgValue::Unit
        }
    }

    /// Bind an [`ArgValue`] to a local (at `dest_path`) in the *current* frame.
    fn bind_value(&mut self, local: rustc_middle::mir::Local, dest_path: &[u64], value: ArgValue) {
        match value {
            ArgValue::Fields(slots) => {
                for (rel, lc) in slots {
                    let mut path = dest_path.to_vec();
                    path.extend(rel);
                    self.set_field_at(local, &path, lc);
                }
            }
            ArgValue::Int(n) => self.set_int_at(local, dest_path, n),
            ArgValue::Str(s) => {
                if dest_path.is_empty() {
                    self.set_str(local, s)
                }
            }
            ArgValue::Unit => {}
        }
    }

    /// Capture the return value (`_0`) of the current frame (scalar or array),
    /// draining it (the frame is about to be popped).
    fn frame_return(&mut self) -> ArgValue {
        let l0 = rustc_middle::mir::Local::from_usize(0);
        let slots = self.take_field_slots(l0, &[]);
        if !slots.is_empty() {
            ArgValue::Fields(slots)
        } else if let Some(n) = self.get_int(l0) {
            ArgValue::Int(n)
        } else if let Some(s) = self.get_str(l0) {
            ArgValue::Str(s)
        } else {
            ArgValue::Unit
        }
    }

    // --- lowering primitives -----------------------------------------------

    /// A pending mul var that a compound expression consumes can no longer be
    /// merged into a later equality.
    fn consume_pending(&mut self, lc: &LinearCombination) {
        if let Some(v) = self.as_pending_var(lc) {
            self.pending_mul.remove(&v);
        }
    }

    fn as_pending_var(&self, lc: &LinearCombination) -> Option<VarId> {
        if lc.constant.is_zero() && lc.terms.len() == 1 {
            let term = &lc.terms[0];
            if term.coeff.is_one() && self.pending_mul.contains_key(&term.var) {
                return Some(term.var);
            }
        }
        None
    }

    /// If `lc` has more than [`Self::LC_MATERIALIZE_THRESHOLD`] terms, name it as
    /// a fresh internal variable `v` (emit `lc - v = 0` and record `v = eval(lc)`)
    /// and return `v`'s LC. This bounds LC size in long bitwise chains (e.g.
    /// Keccak) so lowering stays linear instead of quadratic. Small LCs pass
    /// through unchanged, so existing gadgets are unaffected.
    const LC_MATERIALIZE_THRESHOLD: usize = 8;
    fn materialize(&mut self, lc: LinearCombination) -> LinearCombination {
        if lc.terms.len() <= Self::LC_MATERIALIZE_THRESHOLD {
            return lc;
        }
        let v = self.alloc_internal();
        let id = self.fresh_constraint_id();
        // Cheap note (materialized LCs are large by definition).
        let note = format!("{} = <lc: {} terms>", self.var_names[v as usize], lc.terms.len());
        self.witness_gen
            .push(Some(WitnessGen::Linear { out: v, lc: lc.clone() }));
        // Defining constraint: (lc - v) * 1 = 0.
        self.constraints.push(R1csConstraint::equal(
            id,
            lc,
            LinearCombination::var(v),
            &note,
        ));
        LinearCombination::var(v)
    }

    /// Emit `lhs * rhs = t` for a fresh internal `t`, returning `t`'s LC.
    fn emit_mul(&mut self, lhs: LinearCombination, rhs: LinearCombination) -> LinearCombination {
        let lhs = self.materialize(lhs);
        let rhs = self.materialize(rhs);
        let out = self.alloc_internal();
        let id = self.fresh_constraint_id();
        let note = format!(
            "{} * {} = {}",
            self.render_side(&lhs),
            self.render_side(&rhs),
            self.var_names[out as usize]
        );
        self.constraints
            .push(R1csConstraint::mul(id, lhs.clone(), rhs.clone(), out, &note));
        let c_idx = self.constraints.len() - 1;
        // Witness-gen: the mul output is computed as `eval(lhs) * eval(rhs)`.
        self.witness_gen.push(Some(WitnessGen::Product {
            out,
            left: lhs,
            right: rhs,
        }));
        let wg_idx = self.witness_gen.len() - 1;
        self.pending_mul.insert(out, (c_idx, wg_idx));
        LinearCombination::var(out)
    }

    /// Emit a fused boolean XOR: allocate `c`, emit `(2a) * b = a + b - c`, and
    /// record `c = a + b - 2ab`. `c` is a single variable, so chained XORs (e.g.
    /// Keccak's theta) don't grow linear combinations.
    fn emit_xor(&mut self, a: LinearCombination, b: LinearCombination) -> LinearCombination {
        self.consume_pending(&a);
        self.consume_pending(&b);
        let c = self.alloc_internal();
        let id = self.fresh_constraint_id();
        let a2 = a.clone().scale(&xark_ir::FieldConst::from_i64(2));
        let c_side = a.clone().add(b.clone()).sub(LinearCombination::var(c));
        let note = format!("{} = xor", self.var_names[c as usize]);
        self.constraints
            .push(R1csConstraint::general(id, a2, b.clone(), c_side, &note));
        self.witness_gen
            .push(Some(WitnessGen::Xor { out: c, a, b }));
        LinearCombination::var(c)
    }

    /// Emit a fused boolean OR: allocate `c`, emit `a * b = a + b - c`, record
    /// `c = a + b - ab`.
    fn emit_or(&mut self, a: LinearCombination, b: LinearCombination) -> LinearCombination {
        self.consume_pending(&a);
        self.consume_pending(&b);
        let c = self.alloc_internal();
        let id = self.fresh_constraint_id();
        let c_side = a.clone().add(b.clone()).sub(LinearCombination::var(c));
        let note = format!("{} = or", self.var_names[c as usize]);
        self.constraints
            .push(R1csConstraint::general(id, a.clone(), b.clone(), c_side, &note));
        self.witness_gen.push(Some(WitnessGen::Or { out: c, a, b }));
        LinearCombination::var(c)
    }

    fn emit_pow(&mut self, base: LinearCombination, n: u64) -> LinearCombination {
        match n {
            0 => LinearCombination::one(),
            1 => base,
            2 => self.emit_mul(base.clone(), base),
            3 => {
                let sq = self.emit_mul(base.clone(), base.clone());
                self.consume_pending(&sq);
                self.emit_mul(sq, base)
            }
            _ => {
                // Exponentiation by squaring.
                let mut result: Option<LinearCombination> = None;
                let mut b = base;
                let mut e = n;
                while e > 0 {
                    if e & 1 == 1 {
                        result = Some(match result {
                            None => b.clone(),
                            Some(r) => {
                                self.consume_pending(&r);
                                self.consume_pending(&b);
                                self.emit_mul(r, b.clone())
                            }
                        });
                    }
                    e >>= 1;
                    if e > 0 {
                        self.consume_pending(&b);
                        b = self.emit_mul(b.clone(), b);
                    }
                }
                result.expect("n > 0 handled above")
            }
        }
    }

    fn emit_assert_eq(&mut self, lhs: LinearCombination, rhs: LinearCombination) {
        // Merge `t = a * b; assert_eq(t, target)` into `a * b = target`.
        if let Some(v) = self.as_pending_var(&lhs) {
            self.merge_mul(v, rhs);
            return;
        }
        if let Some(v) = self.as_pending_var(&rhs) {
            self.merge_mul(v, lhs);
            return;
        }

        let diff = lhs.sub(rhs);
        let id = self.fresh_constraint_id();
        let note = format!("({}) * 1 = 0", self.render_lc(&diff));
        self.constraints
            .push(R1csConstraint::equal(id, diff, LinearCombination::zero(), &note));
    }

    /// Emit an `n`-bit range proof pinning `value` to `[0, 2^n)` — the same
    /// decomposition as `Field::to_bits::<N>`, injected at the input boundary for
    /// a `U<N>` parameter.
    fn emit_range_proof(&mut self, value: VarId, n: usize) {
        let value_lc = LinearCombination::var(value);
        let two = xark_ir::FieldConst::from_i64(2);
        let mut pow = xark_ir::FieldConst::from_i64(1);
        let mut recomp = LinearCombination::zero();
        for i in 0..n {
            let b = self.alloc_advice();
            // Witness-gen: bit `i` of the input value.
            self.witness_gen.push(Some(WitnessGen::Bit {
                out: b,
                input: value_lc.clone(),
                index: i as u32,
            }));
            // Booleanity: `b * b = b` (⟺ `b ∈ {0, 1}`).
            let id = self.fresh_constraint_id();
            let note = format!("{} in {{0,1}}", self.var_names[b as usize]);
            self.constraints.push(R1csConstraint::general(
                id,
                LinearCombination::var(b),
                LinearCombination::var(b),
                LinearCombination::var(b),
                &note,
            ));
            recomp = recomp.add(LinearCombination::var(b).scale(&pow));
            pow = pow.mul(&two);
        }
        // Recomposition pins the bits to `value` (⇒ `value < 2^n`).
        let id = self.fresh_constraint_id();
        let note = format!(
            "{}-bit range: recompose == {}",
            n, self.var_names[value as usize]
        );
        self.constraints
            .push(R1csConstraint::equal(id, recomp, value_lc, &note));
    }

    fn merge_mul(&mut self, var: VarId, target: LinearCombination) {
        let (idx, wg_idx) = self
            .pending_mul
            .remove(&var)
            .expect("caller guarantees var is pending");
        // Record enough to revive this product if it is referenced again after
        // the merge (see the `merged` field). `.a`/`.b` are the mul's operands
        // and are unchanged by the merge — only `.c` becomes `target` below.
        self.merged.insert(
            var,
            (
                self.constraints[idx].a.clone(),
                self.constraints[idx].b.clone(),
                wg_idx,
            ),
        );
        // The merged multiplication `a * b = target` is now a check, not a
        // definition — its output var is gone, so drop its witness-gen Product.
        self.witness_gen[wg_idx] = None;
        let target = target.simplified();
        let note = format!(
            "{} * {} = {}",
            self.render_side(&self.constraints[idx].a),
            self.render_side(&self.constraints[idx].b),
            self.render_side(&target),
        );
        self.constraints[idx].c = target;
        if let Some(debug) = &mut self.constraints[idx].debug {
            debug.note = Some(note);
        }
    }
}

/// Both emitted views of the lowered circuit.
pub struct LowerOutput {
    /// Fully-lowered R1CS (a·b=c) — kept for the DOT graph and debugging.
    pub r1cs: R1csProgram,
    /// Primitive IR (AssertZero expressions + witness-gen hint program) — the
    /// artifact the backend lowering consumes.
    pub primitive: PrimitiveProgram,
}

/// Flatten a circuit parameter type into its `Field` leaves, pairing each with
/// the MIR projection path (encoded exactly as [`LoweringEnv::resolve_place`]:
/// array/const index, or struct-field index), a human-readable name, and an
/// optional fixed-width bound. A scalar `Field` is one leaf at path `[]`; an
/// array/tuple/struct of `Field` collapses to `n` leaves (`g[0][1]`,
/// `pubkey.x[0]`, …). A `U<N>` is one leaf carrying `Some(N)`: its value must be
/// proven `< 2^N` (in-circuit for a private input, by the verifier for a public
/// one). Any other leaf is rejected.
fn flatten_field_leaves<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    path: &mut Vec<u64>,
    name: &str,
    out: &mut Vec<(Vec<u64>, String, Option<usize>)>,
) -> CompileResult<()> {
    // `Field` is the opaque leaf — never recurse into its private limbs.
    if let Some(d) = ty.ty_adt_def() {
        if tcx.item_name(d.did()).as_str() == "Field" {
            out.push((path.clone(), name.to_string(), None));
            return Ok(());
        }
    }
    // `U<N>` is a fixed-width leaf: one `Field` value carrying the bit width, so
    // the input path can range-prove it (private) or delegate to the verifier
    // (public). Its single `value` field sits at projection index 0.
    if let rustc_middle::ty::TyKind::Adt(def, args) = ty.kind() {
        // `def_path_str` renders the re-exported path (`xark::U`); accept that and
        // the definition path (`…::uint::U`). Matches xark's `U`, not a user type.
        let p = tcx.def_path_str(def.did());
        if p == "xark::U" || p.ends_with("::uint::U") {
            let n = args
                .const_at(0)
                .try_to_target_usize(tcx)
                .ok_or_else(|| CompileError::new("U<N>: width `N` must be a constant"))?
                as usize;
            if n < 1 || n > 253 {
                return Err(CompileError::new(format!(
                    "U<{n}> circuit input: width must be in 1..=253 (BN254 field capacity)"
                ))
                .with_help(
                    "choose `N` in 1..=253; a wider value is not uniquely representable in the \
                     scalar field",
                ));
            }
            path.push(0);
            out.push((path.clone(), name.to_string(), Some(n)));
            path.pop();
            return Ok(());
        }
        // `I<N>` is a two-field struct (value + cached sign) whose fields must be
        // kept consistent — it cannot be accepted as a raw input yet (flattening
        // it would produce two unconstrained leaves). Reject with guidance.
        if p == "xark::I" || p.ends_with("::int::I") {
            return Err(CompileError::new(
                "signed `I<N>` is not yet supported as a circuit input",
            )
            .with_help(
                "take a `Private<Field>`/`Public<Field>` and construct it in-circuit with \
                 `I::<N>::new(x)`",
            ));
        }
    }
    match ty.kind() {
        rustc_middle::ty::TyKind::Array(elem, len) => {
            let n = len
                .try_to_target_usize(tcx)
                .ok_or_else(|| CompileError::new("circuit input array length must be constant"))?;
            for i in 0..n {
                path.push(i);
                flatten_field_leaves(tcx, *elem, path, &format!("{name}[{i}]"), out)?;
                path.pop();
            }
            Ok(())
        }
        rustc_middle::ty::TyKind::Tuple(elems) => {
            for (i, elem) in elems.iter().enumerate() {
                path.push(i as u64);
                flatten_field_leaves(tcx, elem, path, &format!("{name}.{i}"), out)?;
                path.pop();
            }
            Ok(())
        }
        rustc_middle::ty::TyKind::Adt(def, args) if def.is_struct() => {
            for (i, fdef) in def.non_enum_variant().fields.iter().enumerate() {
                let fty = fdef.ty(tcx, args);
                path.push(i as u64);
                flatten_field_leaves(tcx, fty, path, &format!("{name}.{}", fdef.name), out)?;
                path.pop();
            }
            Ok(())
        }
        _ => Err(CompileError::new(format!("unsupported circuit input type `{ty}`"))
            .with_help("circuit inputs must be `Field`, or arrays/tuples/structs of `Field`")),
    }
}

/// Lower the `circuit` body into both the R1CS and the primitive IR.
pub fn lower<'tcx>(
    tcx: TyCtxt<'tcx>,
    entry: &EntryInfo,
    body: &Body<'tcx>,
    field: FieldSpec,
) -> CompileResult<LowerOutput> {
    let mut env = LoweringEnv::new(tcx);

    // Frame 0: circuit inputs become variables `0..num_inputs`, bound to params
    // `_1.._n`. Each parameter's type is flattened into its `Field` leaves — a
    // scalar `Field` is one input var; an array/tuple/struct of `Field` collapses
    // to `n` vars, each bound to the leaf's projection path so body reads resolve.
    let mut num_inputs = 0usize;
    // `U<N>` inputs whose `< 2^N` bound must be proven in-circuit, collected here
    // and emitted after the input id range is fixed.
    let mut uint_range_inputs: Vec<(VarId, usize)> = Vec::new();
    for (i, input) in entry.inputs.iter().enumerate() {
        let local = rustc_middle::mir::Local::from_usize(i + 1);
        let ty = body.local_decls[local].ty;
        let mut leaves = Vec::new();
        let mut path = Vec::new();
        flatten_field_leaves(tcx, ty, &mut path, &input.name, &mut leaves)?;
        for (leaf_path, leaf_name, range_bits) in leaves {
            let id = env.alloc_var(leaf_name, input.visibility.clone());
            env.set_field_at(local, &leaf_path, LinearCombination::var(id));
            num_inputs += 1;
            // Range-prove every `U<N>` input, public ones too: `< r` (all
            // Groth16 checks for a public input) does not imply `< 2^N`, and the
            // comparison gadget relies on the tighter bound.
            if let Some(n) = range_bits {
                uint_range_inputs.push((id, n));
            }
        }
    }
    for (id, n) in uint_range_inputs {
        env.emit_range_proof(id, n);
    }

    walk_body(&mut env, body)?;

    let program = finish(env, field, num_inputs);
    // Machine-checked soundness gate (runs on every `xark build`/`xark check`):
    // reject a circuit that leaves a hint/advice output or a public input
    // unpinned by any constraint. See `check_pinning`.
    check_pinning(&program, num_inputs)?;
    Ok(program)
}

/// Build-time structural soundness gate.
///
/// Rejects two "author forgot to constrain X" footguns:
///
/// * a **hint/advice output** (`Field::advice()`, `hint_inverse`, `hint_bit`,
///   `hint_div_rem`, `hint_mulmod_divmod`, `hint_mod_inverse`, `hint_sub2` — all
///   allocated as `Private` witnesses with id ≥ `n_inputs`) that appears in **no**
///   constraint. Such a witness is free: a malicious prover chooses it at will.
/// * a declared **public input** (`Public` visibility) that appears in **no**
///   constraint. The verifier's supplied value for it would then be unconstrained
///   — the proof "verifies" for any value.
///
/// This is a *necessary* structural check (every such value must be referenced by
/// at least one constraint), not a full under-constraint proof — the deeper
/// "referenced but two-valued" analysis is `solver::analyze_underconstrained`,
/// run over the honest witness in the gadget test suites. Together they close the
/// pinning gap from both ends.
fn check_pinning(out: &LowerOutput, n_inputs: usize) -> CompileResult<()> {
    let mut referenced: BTreeSet<VarId> = BTreeSet::new();
    for c in &out.r1cs.constraints {
        for lc in [&c.a, &c.b, &c.c] {
            for term in &lc.terms {
                referenced.insert(term.var);
            }
        }
    }
    for v in &out.r1cs.variables {
        if referenced.contains(&v.id) {
            continue;
        }
        let is_input = (v.id as usize) < n_inputs;
        match v.visibility {
            Visibility::Public => {
                return Err(CompileError::new(format!(
                    "public input `{}` is declared but no constraint references it — \
                     the verifier's value for it would be unconstrained",
                    v.name
                ))
                .with_note(
                    "bind every public input/output with an `assert_eq` (or remove it \
                     from the signature)",
                ));
            }
            // A `Private` var allocated after the inputs is a hint/advice output.
            Visibility::Private if !is_input => {
                return Err(CompileError::new(format!(
                    "hint/advice output `{}` is not pinned by any constraint — \
                     a malicious prover could choose it freely",
                    v.name
                ))
                .with_note(
                    "constrain every hint output, e.g. `assert_eq(x * hint_inverse(x), 1)`",
                ));
            }
            _ => {}
        }
    }
    Ok(())
}

/// Apply Rust `as`-cast truncation to a compile-time integer narrowed to `ty`
/// (an int/uint type): keep only the low `bits` of `v` and, for a signed target,
/// sign-extend — matching `v as iN` / `v as uN`. A non-integer target (rejected
/// for circuit code by the validator) passes the value through unchanged.
fn truncate_int_cast(v: i128, ty: rustc_middle::ty::Ty<'_>) -> u128 {
    use rustc_middle::ty::{IntTy, TyKind, UintTy};
    let (bits, signed) = match ty.kind() {
        TyKind::Uint(u) => (
            match u {
                UintTy::U8 => 8,
                UintTy::U16 => 16,
                UintTy::U32 => 32,
                UintTy::U64 => 64,
                UintTy::U128 => 128,
                UintTy::Usize => 64,
            },
            false,
        ),
        TyKind::Int(i) => (
            match i {
                IntTy::I8 => 8,
                IntTy::I16 => 16,
                IntTy::I32 => 32,
                IntTy::I64 => 64,
                IntTy::I128 => 128,
                IntTy::Isize => 64,
            },
            true,
        ),
        _ => return v as u128,
    };
    if bits >= 128 {
        return v as u128;
    }
    let mask = (1u128 << bits) - 1;
    let low = (v as u128) & mask;
    // Sign-extend a negative value in a signed target so the stored u128 is the
    // two's-complement of the narrowed `iN`.
    if signed && (low >> (bits - 1)) & 1 == 1 {
        low | !mask
    } else {
        low
    }
}

/// Maximum number of basic-block visits per body walk. Loops are unrolled by
/// re-walking the CFG; a witness-independent bound terminates well within this,
/// while an unbounded/witness-dependent loop trips it with a clear error.
const MAX_STEPS: u64 = 5_000_000;

/// Walk a body's CFG (from the start block) in the current frame, lowering each
/// statement and terminator. Loops with compile-time bounds are unrolled by
/// following back-edges; witness-dependent control flow is rejected.
fn walk_body<'tcx>(env: &mut LoweringEnv<'tcx>, body: &Body<'tcx>) -> CompileResult<()> {
    let mut bb = START_BLOCK;
    let mut steps = 0u64;
    loop {
        steps += 1;
        if steps > MAX_STEPS {
            return Err(CompileError::new(
                "loop did not terminate within the unroll budget",
            )
            .with_note("only loops with compile-time-constant bounds can be unrolled"));
        }
        let data = &body.basic_blocks[bb];

        for stmt in &data.statements {
            // Any lowering error bubbling up gets this statement's span as a
            // fallback location; a deeper error's own span (if set) is kept.
            lower_statement(env, &stmt.kind).map_err(|e| e.or_span(stmt.source_info.span))?;
        }

        let terminator = data.terminator();
        let term_span = terminator.source_info.span;
        match &terminator.kind {
            TerminatorKind::Return => break,
            TerminatorKind::Goto { target } => bb = *target,
            // Bounds/overflow checks: indices are compile-time constants (the
            // loop unroller guarantees this), so follow the success edge.
            TerminatorKind::Assert { target, .. } => bb = *target,
            // Compile-time-known branch (loop condition, match on constant).
            TerminatorKind::SwitchInt { discr, targets } => {
                let v = env
                    .operand_to_int(discr)
                    .ok_or_else(|| {
                        CompileError::new("witness-dependent control flow is not supported")
                            .with_note(
                                "branch conditions must be compile-time constants (e.g. loop bounds)",
                            )
                            .with_help(
                                "a circuit has no runtime control flow: for a data-dependent \
                                 choice use `select(cond, a, b)`; loops must have constant bounds",
                            )
                    })
                    .map_err(|e| e.or_span(term_span))?;
                bb = targets
                    .iter()
                    .find(|(val, _)| *val == v as u128)
                    .map(|(_, t)| t)
                    .unwrap_or_else(|| targets.otherwise());
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                lower_call(env, func, args, destination).map_err(|e| e.or_span(term_span))?;
                match target {
                    Some(t) => bb = *t,
                    None => {
                        return Err(CompileError::new(
                            "diverging call is not supported inside a circuit",
                        )
                        .or_span(term_span))
                    }
                }
            }
            other => {
                return Err(CompileError::new(format!(
                    "unsupported terminator `{}` inside circuit",
                    terminator_name(other)
                ))
                .or_span(term_span))
            }
        }
    }
    Ok(())
}

fn lower_statement<'tcx>(
    env: &mut LoweringEnv<'tcx>,
    kind: &StatementKind<'tcx>,
) -> CompileResult<()> {
    match kind {
        StatementKind::Assign(boxed) => {
            let (place, rvalue) = &**boxed;
            let (dest, dest_path) = env.resolve_place(place)?;
            match rvalue {
                Rvalue::Use(operand, _) => bind_use(env, dest, &dest_path, operand),
                // `_b = &(*_a)` reborrow: only supported to carry a `&str`
                // literal into `Field::constant`. Taking a reference to a `Field`
                // value is otherwise unsupported — the circuit lowering is
                // deliberately reference-free — which is what rejects `==`/`<`
                // (need `&self`) and `+=`/`-=`/… (need `&mut self`).
                Rvalue::Ref(_, _, src) | Rvalue::CopyForDeref(src) => {
                    if let Some(s) = env.get_str(src.local) {
                        env.set_str(dest, s);
                        Ok(())
                    } else {
                        Err(CompileError::new(
                            "references to a `Field` value are not supported inside a circuit",
                        )
                        .with_note(
                            "comparisons (`==` `!=` `<` `<=` `>` `>=`) and compound assignments \
                             (`+=` `-=` `*=` `/=`) are not circuit operations — use `assert_eq(a, b)` \
                             to constrain equality or `a.is_eq(b)`/`a.is_zero()` for a boolean result, \
                             and write `a = a + b` instead of `a += b`",
                        ))
                    }
                }
                // Array literal `[a, b, c]`: store each element in its slot.
                // Elements may themselves be arrays (nested arrays like
                // `[[Field; 32]; 8]`), copied slot-by-slot.
                Rvalue::Aggregate(kind, operands) => {
                    // Arrays, tuples, and plain structs all lay their components
                    // out by index: operand `i` goes to slot `[dest_path, i]`. For
                    // a struct the operands are the fields in declaration
                    // (field-index) order, which is exactly what `ProjectionElem::
                    // Field` reads back. Enums/unions (multi-variant / downcast)
                    // are not supported.
                    let supported = match &**kind {
                        rustc_middle::mir::AggregateKind::Array(_)
                        | rustc_middle::mir::AggregateKind::Tuple => true,
                        rustc_middle::mir::AggregateKind::Adt(did, ..) => {
                            env.tcx.adt_def(*did).is_struct()
                        }
                        _ => false,
                    };
                    if !supported {
                        return Err(CompileError::new(
                            "unsupported aggregate (only fixed-size `Field` arrays, tuples, \
                             and plain structs are supported)",
                        ));
                    }
                    for (i, op) in operands.iter().enumerate() {
                        let mut base = dest_path.clone();
                        base.push(i as u64);
                        env.store_operand_slots(dest, &base, op)?;
                    }
                    Ok(())
                }
                // `[x; N]` repeat (x may be a scalar or an array).
                Rvalue::Repeat(operand, count) => {
                    let n = env.eval_const_usize(*count).ok_or_else(|| {
                        CompileError::new("array repeat count must be a constant")
                    })?;
                    for i in 0..n {
                        let mut base = dest_path.clone();
                        base.push(i);
                        env.store_operand_slots(dest, &base, operand)?;
                    }
                    Ok(())
                }
                // Integer arithmetic/comparison (loop counters, bounds checks).
                Rvalue::BinaryOp(op, operands) => {
                    if let (Some(a), Some(b)) =
                        (env.operand_to_int(&operands.0), env.operand_to_int(&operands.1))
                    {
                        if let Some(r) = eval_int_binop(*op, a, b) {
                            if is_with_overflow(*op) {
                                // Result is a `(value, overflowed)` tuple.
                                let mut v_path = dest_path.clone();
                                v_path.push(0);
                                env.set_int_at(dest, &v_path, r as u128);
                                let mut o_path = dest_path.clone();
                                o_path.push(1);
                                env.set_int_at(dest, &o_path, 0);
                            } else {
                                env.set_int_at(dest, &dest_path, r as u128);
                            }
                        }
                    }
                    Ok(())
                }
                Rvalue::UnaryOp(op, operand) => {
                    if let Some(a) = env.operand_to_int(operand) {
                        let r = match op {
                            rustc_middle::mir::UnOp::Not => !a,
                            rustc_middle::mir::UnOp::Neg => -a,
                            _ => a,
                        };
                        env.set_int_at(dest, &dest_path, r as u128);
                    }
                    Ok(())
                }
                // Compile-time integer cast (`v as u64` in the `From<uN> for
                // Field` conversions, or a narrowing `as u8`/`as u16`/… used to
                // derive an index or loop bound). Truncate to the target type's
                // width per Rust `as` semantics: storing the source value verbatim
                // miscompiles any narrowing cast whose value exceeds the target
                // width (e.g. `(i * K) as u8` with `i*K >= 256` would truncate).
                Rvalue::Cast(_, operand, ty) => {
                    if let Some(v) = env.operand_to_int(operand) {
                        env.set_int_at(dest, &dest_path, truncate_int_cast(v, *ty));
                    }
                    Ok(())
                }
                other => Err(CompileError::new(format!(
                    "unsupported rvalue `{}` inside circuit",
                    rvalue_name(other)
                ))
                .with_help(
                    "a circuit supports field arithmetic (`+ - * ^`), comparisons, and the \
                     provided gadget calls; references, closures, and heap ops are not lowerable",
                )),
            }
        }
        // A fresh allocation of a local: wipe any stale slots from a previous
        // use of the same local index (MIR reuses locals, and reusing one for a
        // different type — e.g. a `Bignum` then a scalar `Field` — must not leak
        // the old struct/array slots into the new value).
        StatementKind::StorageLive(l) => {
            env.clear_local(*l);
            Ok(())
        }
        StatementKind::StorageDead(_)
        | StatementKind::Nop
        | StatementKind::ConstEvalCounter
        | StatementKind::FakeRead(..)
        | StatementKind::PlaceMention(..)
        | StatementKind::AscribeUserType(..)
        | StatementKind::Coverage(..)
        | StatementKind::BackwardIncompatibleDropHint { .. } => Ok(()),
        StatementKind::SetDiscriminant { .. } | StatementKind::Intrinsic(..) => {
            Err(CompileError::new("unsupported statement inside circuit"))
        }
    }
}

/// Bind `dest[dest_path] = <use of operand>` for a field value, an array, or an
/// integer/string constant.
/// Little-endian `[u64; 4]` (a 256-bit value) → its decimal string.
fn limbs_to_decimal(mut limbs: [u64; 4]) -> String {
    if limbs == [0u64; 4] {
        return "0".to_string();
    }
    let mut digits = Vec::new();
    while limbs != [0u64; 4] {
        let mut rem = 0u128;
        for i in (0..4).rev() {
            let cur = (rem << 64) | limbs[i] as u128;
            limbs[i] = (cur / 10) as u64;
            rem = cur % 10;
        }
        digits.push(b'0' + rem as u8);
    }
    digits.reverse();
    String::from_utf8(digits).expect("ascii digits")
}

fn bind_use<'tcx>(
    env: &mut LoweringEnv<'tcx>,
    dest: rustc_middle::mir::Local,
    dest_path: &[u64],
    operand: &Operand<'tcx>,
) -> CompileResult<()> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            let (src, src_path) = env.resolve_place(place)?;
            if let Some(lc) = env.get_field_at(src, &src_path) {
                env.set_field_at(dest, dest_path, lc);
            } else if let Some(v) = env.get_int_at(src, &src_path) {
                env.set_int_at(dest, dest_path, v);
            } else {
                // Whole-array or sub-array copy: move every field slot under
                // `(src, src_path)` to `dest` at `dest_path`. Handles e.g.
                // `let row = matrix[i]` where `row` is a whole `[Field; N]`.
                let slots = env.collect_field_slots(src, &src_path);
                if !slots.is_empty() {
                    for (rel, lc) in slots {
                        let mut path = dest_path.to_vec();
                        path.extend(rel);
                        env.set_field_at(dest, &path, lc);
                    }
                } else if src_path.is_empty() && dest_path.is_empty() {
                    if let Some(s) = env.get_str(src) {
                        env.set_str(dest, s);
                    }
                }
                // Otherwise a non-circuit temporary (e.g. unit) — ignore.
            }
            Ok(())
        }
        Operand::Constant(c) => {
            // Track integer and string constants; ignore unit/other constants.
            if dest_path.is_empty() {
                if let Some(v) = env.const_to_u128(c) {
                    env.set_int(dest, v);
                } else if env.try_bind_const_int_array(dest, c) {
                    // populated per-element int slots for a `const [uN; K]` array
                } else if let Some(slots) = env.const_field_slots(c) {
                    // a `const Field` / `[Field; N]` (e.g. an assoc const modulus)
                    for (path, lc) in slots {
                        env.set_field_at(dest, &path, lc);
                    }
                } else if let Ok(s) = LoweringEnv::const_to_str(env.tcx, c) {
                    env.set_str(dest, s);
                }
            }
            Ok(())
        }
        Operand::RuntimeChecks(_) => Ok(()),
    }
}

fn is_with_overflow(op: rustc_middle::mir::BinOp) -> bool {
    use rustc_middle::mir::BinOp::*;
    matches!(op, AddWithOverflow | SubWithOverflow | MulWithOverflow)
}

/// Evaluate a compile-time integer binary op, returning `None` for unsupported
/// operators. Comparisons yield `0`/`1`.
fn eval_int_binop(op: rustc_middle::mir::BinOp, a: i128, b: i128) -> Option<i128> {
    use rustc_middle::mir::BinOp::*;
    let v = match op {
        Add | AddUnchecked | AddWithOverflow => a + b,
        Sub | SubUnchecked | SubWithOverflow => a - b,
        Mul | MulUnchecked | MulWithOverflow => a * b,
        Div => a.checked_div(b)?,
        Rem => a.checked_rem(b)?,
        BitAnd => a & b,
        BitOr => a | b,
        BitXor => a ^ b,
        Shl | ShlUnchecked => a << b,
        Shr | ShrUnchecked => a >> b,
        Eq => (a == b) as i128,
        Ne => (a != b) as i128,
        Lt => (a < b) as i128,
        Le => (a <= b) as i128,
        Gt => (a > b) as i128,
        Ge => (a >= b) as i128,
        _ => return None,
    };
    Some(v)
}

fn lower_call<'tcx>(
    env: &mut LoweringEnv<'tcx>,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    destination: &Place<'tcx>,
) -> CompileResult<()> {
    let (def_id, generic_args) = func.const_fn_def().ok_or_else(|| {
        CompileError::new("indirect / dynamic calls are not supported inside a circuit").with_help(
            "call functions directly by name; function pointers, closures, and `dyn` dispatch \
             have no compile-time-known target to inline",
        )
    })?;

    // Monomorphize the call's generic args in the current inlining context (a
    // no-op at the concrete top level), then resolve trait methods to the impl.
    let generic_args = env.tcx.instantiate_and_normalize_erasing_regions(
        env.cur_substs(),
        rustc_middle::ty::TypingEnv::fully_monomorphized(),
        rustc_middle::ty::EarlyBinder::bind(generic_args),
    );
    let (def_id, call_args) = match resolve_call_instance(env.tcx, def_id, generic_args) {
        Some(inst) => (inst.def_id(), inst.args),
        None => (def_id, generic_args),
    };

    let dest = LoweringEnv::place_local(destination)?;

    // A recognized intrinsic is lowered directly; any other ordinary function
    // with available MIR is inlined; anything else is rejected.
    let known = match classify_call(env.tcx, def_id) {
        Some(known) => known,
        None => return inline_call(env, def_id, call_args, args, dest),
    };
    let arg = |i: usize| -> CompileResult<&Operand<'tcx>> {
        args.get(i)
            .map(|s| &s.node)
            .ok_or_else(|| CompileError::new("circuit call has too few arguments"))
    };

    match known {
        KnownCall::Add => {
            let lhs = env.operand_to_lc(arg(0)?)?;
            let rhs = env.operand_to_lc(arg(1)?)?;
            env.consume_pending(&lhs);
            env.consume_pending(&rhs);
            env.set_field(dest, lhs.add(rhs));
        }
        KnownCall::Sub => {
            let lhs = env.operand_to_lc(arg(0)?)?;
            let rhs = env.operand_to_lc(arg(1)?)?;
            env.consume_pending(&lhs);
            env.consume_pending(&rhs);
            env.set_field(dest, lhs.sub(rhs));
        }
        KnownCall::Neg => {
            let x = env.operand_to_lc(arg(0)?)?;
            env.consume_pending(&x);
            env.set_field(dest, x.neg());
        }
        KnownCall::Mul => {
            let lhs = env.operand_to_lc(arg(0)?)?;
            let rhs = env.operand_to_lc(arg(1)?)?;
            // Constant * anything is linear: fold it into the coefficients
            // instead of allocating a multiplication gate.
            let out = if lhs.is_constant() {
                env.consume_pending(&rhs);
                rhs.scale(&lhs.constant)
            } else if rhs.is_constant() {
                env.consume_pending(&lhs);
                lhs.scale(&rhs.constant)
            } else {
                env.consume_pending(&lhs);
                env.consume_pending(&rhs);
                env.emit_mul(lhs, rhs)
            };
            env.set_field(dest, out);
        }
        KnownCall::PowU64 => {
            let base = env.operand_to_lc(arg(0)?)?;
            env.consume_pending(&base);
            let n = env.operand_to_u64(arg(1)?)?;
            let out = env.emit_pow(base, n);
            env.set_field(dest, out);
        }
        KnownCall::FieldConstantU64 => {
            let v = env.operand_to_u64(arg(0)?)?;
            env.set_field(dest, LinearCombination::constant(v.to_string()));
        }
        KnownCall::FieldConstantU128 => {
            let v = env.operand_to_u128(arg(0)?)?;
            env.set_field(dest, LinearCombination::constant(v.to_string()));
        }
        KnownCall::FieldConstantDecimal => {
            let s = env.operand_to_str(arg(0)?)?;
            let field_const = xark_ir::FieldConst::from_decimal(&s).ok_or_else(|| {
                // Pinpoint the first non-decimal character (a leading `-`/`+` is
                // allowed) so the diagnostic names exactly what's wrong.
                let t = s.trim();
                let bad = t.char_indices().find(|&(i, c)| {
                    !(c.is_ascii_digit() || (i == 0 && (c == '-' || c == '+')))
                });
                match bad {
                    Some((i, c)) => CompileError::new(format!(
                        "invalid `Field` constant string {t:?}: non-numeric character {c:?} \
                         at position {i} (expected a decimal integer)"
                    )),
                    None => CompileError::new(format!(
                        "invalid `Field` constant string {t:?}: empty or not a decimal integer"
                    )),
                }
            })?;
            env.set_field(dest, LinearCombination::constant(field_const.decimal));
        }
        KnownCall::ConstrainEq => {
            let lhs = env.operand_to_lc(arg(0)?)?;
            let rhs = env.operand_to_lc(arg(1)?)?;
            env.emit_assert_eq(lhs, rhs);
        }
        KnownCall::Advice => {
            // A fresh prover-supplied private witness variable with no hint. The
            // gadget author constrains it (but the emitted witness-gen program
            // cannot compute its value — prefer the `hint_*` forms).
            let v = env.alloc_advice();
            env.set_field(dest, LinearCombination::var(v));
        }
        KnownCall::HintInverse => {
            let x = env.operand_to_lc(arg(0)?)?;
            let v = env.alloc_advice();
            env.witness_gen
                .push(Some(WitnessGen::Inverse { out: v, input: x }));
            env.set_field(dest, LinearCombination::var(v));
        }
        KnownCall::HintInverseOrZero => {
            let x = env.operand_to_lc(arg(0)?)?;
            let v = env.alloc_advice();
            env.witness_gen
                .push(Some(WitnessGen::InverseOrZero { out: v, input: x }));
            env.set_field(dest, LinearCombination::var(v));
        }
        KnownCall::HintBit => {
            let x = env.operand_to_lc(arg(0)?)?;
            let index = env.operand_to_u64(arg(1)?)? as u32;
            let v = env.alloc_advice();
            env.witness_gen.push(Some(WitnessGen::Bit {
                out: v,
                input: x,
                index,
            }));
            env.set_field(dest, LinearCombination::var(v));
        }
        KnownCall::Xor => {
            let a = env.operand_to_lc(arg(0)?)?;
            let b = env.operand_to_lc(arg(1)?)?;
            let out = env.emit_xor(a, b);
            env.set_field(dest, out);
        }
        KnownCall::Or => {
            let a = env.operand_to_lc(arg(0)?)?;
            let b = env.operand_to_lc(arg(1)?)?;
            let out = env.emit_or(a, b);
            env.set_field(dest, out);
        }
        // Width-generic hints: `N` inferred from the array args, `bits` from the
        // trailing `usize`. Returns are tuples (`[0,i]`/`[1,i]` slot paths).
        KnownCall::HintMulModDivMod => {
            let a = env.operand_to_lc_array_dyn(arg(0)?)?;
            let b = env.operand_to_lc_array_dyn(arg(1)?)?;
            let m = env.operand_to_lc_array_dyn(arg(2)?)?;
            let bits = env.operand_to_u64(arg(3)?)? as u32;
            let n = a.len();
            let q: Vec<VarId> = (0..n).map(|_| env.alloc_advice()).collect();
            let r: Vec<VarId> = (0..n).map(|_| env.alloc_advice()).collect();
            env.witness_gen.push(Some(WitnessGen::MulModDivMod {
                q: q.clone(),
                r: r.clone(),
                a,
                b,
                modulus: m,
                limb_bits: bits,
            }));
            // `(q, r)`: tuple field 0 = q array, field 1 = r array.
            for (i, &v) in q.iter().enumerate() {
                env.set_field_at(dest, &[0, i as u64], LinearCombination::var(v));
            }
            for (i, &v) in r.iter().enumerate() {
                env.set_field_at(dest, &[1, i as u64], LinearCombination::var(v));
            }
        }
        KnownCall::HintModInverse => {
            let a = env.operand_to_lc_array_dyn(arg(0)?)?;
            let m = env.operand_to_lc_array_dyn(arg(1)?)?;
            let bits = env.operand_to_u64(arg(2)?)? as u32;
            let n = a.len();
            let out: Vec<VarId> = (0..n).map(|_| env.alloc_advice()).collect();
            env.witness_gen.push(Some(WitnessGen::ModInverse {
                out: out.clone(),
                a,
                modulus: m,
                limb_bits: bits,
            }));
            for (i, &v) in out.iter().enumerate() {
                env.set_field_at(dest, &[i as u64], LinearCombination::var(v));
            }
        }
        KnownCall::HintSub2 => {
            let a = env.operand_to_lc_array_dyn(arg(0)?)?;
            let b = env.operand_to_lc_array_dyn(arg(1)?)?;
            let c = env.operand_to_lc_array_dyn(arg(2)?)?;
            let m = env.operand_to_lc_array_dyn(arg(3)?)?;
            let bits = env.operand_to_u64(arg(4)?)? as u32;
            let n = a.len();
            let qabs = env.alloc_advice();
            let r: Vec<VarId> = (0..n).map(|_| env.alloc_advice()).collect();
            env.witness_gen.push(Some(WitnessGen::Sub2 {
                qabs,
                r: r.clone(),
                a,
                b,
                c,
                modulus: m,
                limb_bits: bits,
            }));
            // `(qabs, r)`: tuple field 0 = qabs, field 1 = r array.
            env.set_field_at(dest, &[0], LinearCombination::var(qabs));
            for (i, &v) in r.iter().enumerate() {
                env.set_field_at(dest, &[1, i as u64], LinearCombination::var(v));
            }
        }
        KnownCall::HintDivRem => {
            let num = env.operand_to_lc(arg(0)?)?;
            let den = env.operand_to_lc(arg(1)?)?;
            let q = env.alloc_advice();
            let r = env.alloc_advice();
            env.witness_gen
                .push(Some(WitnessGen::DivRem { q, r, num, den }));
            // Returns `[q, r]` as a two-element array.
            env.set_field_at(dest, &[0], LinearCombination::var(q));
            env.set_field_at(dest, &[1], LinearCombination::var(r));
        }
    }
    Ok(())
}

/// Inline an ordinary function call: evaluate the arguments in the caller frame,
/// lower the callee's MIR body in a fresh frame, and bind its return value.
///
/// This is what makes gadgets "just library code": a call to `poseidon(..)` or a
/// local helper expands into the same LC/constraint lowering as inline code.
fn inline_call<'tcx>(
    env: &mut LoweringEnv<'tcx>,
    def_id: DefId,
    call_args: rustc_middle::ty::GenericArgsRef<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    dest: rustc_middle::mir::Local,
) -> CompileResult<()> {
    if !env.tcx.is_mir_available(def_id) {
        return Err(CompileError::new(format!(
            "unsupported function call inside circuit: `{}`",
            env.tcx.def_path_str(def_id)
        ))
        .with_note(
            "only xark field operations, assert_eq, and functions whose MIR is available \
             (build gadget crates with `-Zalways-encode-mir`) can be inlined",
        ));
    }

    if env.inlining.contains(&def_id) {
        return Err(CompileError::new(format!(
            "recursion is not supported: `{}` calls itself",
            env.tcx.def_path_str(def_id)
        )));
    }

    // Evaluate arguments in the *caller* frame.
    let mut arg_values: Vec<ArgValue> = Vec::with_capacity(args.len());
    for a in args {
        arg_values.push(env.eval_arg(&a.node));
    }

    // Lower the callee body in a fresh frame with params bound to the args. The
    // callee's generic args are pushed so nested calls in a generic body (e.g.
    // the blanket `Into::into`) monomorphize correctly.
    let body = env.tcx.optimized_mir(def_id);
    env.inlining.push(def_id);
    env.inline_substs.push(call_args);
    env.enter_frame();

    for (i, value) in arg_values.into_iter().enumerate() {
        let param = rustc_middle::mir::Local::from_usize(i + 1);
        env.bind_value(param, &[], value);
    }

    let walk_result = walk_body(env, body);
    let ret = env.frame_return();

    env.exit_frame();
    env.inline_substs.pop();
    env.inlining.pop();
    walk_result?;

    // Bind the return value into the caller frame.
    env.bind_value(dest, &[], ret);
    Ok(())
}

/// Finalize: drop unreferenced internal variables and assemble both programs.
fn finish(mut env: LoweringEnv<'_>, field: FieldSpec, n_inputs: usize) -> LowerOutput {
    // Revive any multiplication output that was folded into an `assert_eq` (its
    // `a·b = out` row repurposed to `a·b = target`, `Product` dropped) but is
    // still referenced by a later constraint — i.e. the product was *reused*
    // after being asserted. Re-pin `a·b = out` and restore its `Product` at its
    // original witness-gen position, so the later use stays bound to `a·b`.
    // A merged-and-not-reused output is unreferenced and pruned below, so the
    // single-use fast path — and every existing snapshot gate count — is
    // unchanged.
    {
        let mut ref_now: BTreeSet<VarId> = BTreeSet::new();
        for c in &env.constraints {
            for lc in [&c.a, &c.b, &c.c] {
                for term in &lc.terms {
                    ref_now.insert(term.var);
                }
            }
        }
        for (out, (a, b, wg_idx)) in std::mem::take(&mut env.merged) {
            if ref_now.contains(&out) {
                let id = env.fresh_constraint_id();
                env.constraints.push(R1csConstraint::mul(
                    id,
                    a.clone(),
                    b.clone(),
                    out,
                    "revived a*b = out (product reused after assert_eq merge)",
                ));
                env.witness_gen[wg_idx] = Some(WitnessGen::Product { out, left: a, right: b });
            }
        }
    }

    let mut referenced: BTreeSet<VarId> = BTreeSet::new();
    for c in &env.constraints {
        for lc in [&c.a, &c.b, &c.c] {
            for term in &lc.terms {
                referenced.insert(term.var);
            }
        }
    }

    let variables: Vec<Variable> = env
        .variables
        .into_iter()
        .filter(|v| v.visibility != Visibility::Internal || referenced.contains(&v.id))
        .collect();
    let kept: BTreeSet<VarId> = variables.iter().map(|v| v.id).collect();

    // --- primitive IR view -------------------------------------------------
    let pvars: Vec<primitive::Var> = variables
        .iter()
        .map(|v| primitive::Var {
            id: v.id,
            name: v.name.clone(),
            role: if (v.id as usize) < n_inputs {
                match v.visibility {
                    Visibility::Public => primitive::VarRole::PublicInput,
                    _ => primitive::VarRole::PrivateInput,
                }
            } else {
                primitive::VarRole::Derived
            },
        })
        .collect();

    let expressions: Vec<primitive::Expression> = env
        .constraints
        .iter()
        .map(|c| {
            expr_from_r1cs(
                &c.a,
                &c.b,
                &c.c,
                c.debug.as_ref().and_then(|d| d.note.clone()),
            )
        })
        .collect();

    let witness_gen: Vec<WitnessGen> = env
        .witness_gen
        .into_iter()
        .flatten()
        .filter(|op| kept.contains(&witness_gen_out(op)))
        .collect();

    let primitive = PrimitiveProgram {
        field: primitive_field(&field),
        vars: pvars,
        constraints: expressions,
        witness_gen,
    };

    let r1cs = R1csProgram {
        field,
        variables,
        constraints: env.constraints,
    };

    LowerOutput { r1cs, primitive }
}

/// The primary output variable of a witness-gen op.
fn witness_gen_out(op: &WitnessGen) -> VarId {
    match op {
        WitnessGen::Product { out, .. }
        | WitnessGen::Linear { out, .. }
        | WitnessGen::Xor { out, .. }
        | WitnessGen::Or { out, .. }
        | WitnessGen::Inverse { out, .. }
        | WitnessGen::InverseOrZero { out, .. }
        | WitnessGen::Bit { out, .. } => *out,
        WitnessGen::DivRem { q, .. } => *q,
        // Multi-output; represented by its first output for the "is any output
        // still referenced" filter (all limbs are used together in practice).
        WitnessGen::MulModDivMod { q, r, .. } => *q.first().or_else(|| r.first()).unwrap_or(&0),
        WitnessGen::ModInverse { out, .. } => *out.first().unwrap_or(&0),
        WitnessGen::Sub2 { qabs, .. } => *qabs,
    }
}

/// Convert the R1CS field spec to the primitive one (which needs a concrete
/// modulus; default to BN254 when unspecified, since that is the target field).
fn primitive_field(field: &FieldSpec) -> primitive::FieldSpec {
    match &field.modulus_decimal {
        Some(m) => primitive::FieldSpec {
            name: field.name.clone(),
            modulus_decimal: m.clone(),
        },
        None => primitive::FieldSpec::bn254(),
    }
}

/// Expand an R1CS constraint `a · b = c` (all linear combinations) into an
/// AssertZero-style expression `a·b − c == 0`.
fn expr_from_r1cs(
    a: &LinearCombination,
    b: &LinearCombination,
    c: &LinearCombination,
    note: Option<String>,
) -> primitive::Expression {
    use std::collections::BTreeMap;
    use xark_ir::FieldConst;

    let mut linear: BTreeMap<VarId, FieldConst> = BTreeMap::new();
    let add_lin = |var: VarId, coeff: FieldConst, linear: &mut BTreeMap<VarId, FieldConst>| {
        let e = linear.entry(var).or_insert_with(FieldConst::zero);
        *e = e.add(&coeff);
    };

    // a·b: constant·constant + a_i·b_const·x_i + a_const·b_j·x_j + a_i·b_j·x_i·x_j
    let mut constant = a.constant.mul(&b.constant);
    for ta in &a.terms {
        add_lin(ta.var, ta.coeff.mul(&b.constant), &mut linear);
    }
    for tb in &b.terms {
        add_lin(tb.var, a.constant.mul(&tb.coeff), &mut linear);
    }
    let mut mul_terms = Vec::new();
    for ta in &a.terms {
        for tb in &b.terms {
            let coeff = ta.coeff.mul(&tb.coeff);
            if !coeff.is_zero() {
                mul_terms.push(primitive::MulTerm {
                    coeff,
                    left: ta.var,
                    right: tb.var,
                });
            }
        }
    }

    // − c
    constant = constant.add(&c.constant.neg());
    for tc in &c.terms {
        add_lin(tc.var, tc.coeff.neg(), &mut linear);
    }

    let linear_terms = linear
        .into_iter()
        .filter(|(_, coeff)| !coeff.is_zero())
        .map(|(var, coeff)| primitive::LinearTerm { coeff, var })
        .collect();

    primitive::Expression {
        mul_terms,
        linear_terms,
        constant,
        note,
    }
}

fn terminator_name(kind: &TerminatorKind<'_>) -> &'static str {
    match kind {
        TerminatorKind::SwitchInt { .. } => "SwitchInt (control flow)",
        TerminatorKind::Assert { .. } => "Assert",
        TerminatorKind::Drop { .. } => "Drop",
        TerminatorKind::Unreachable => "Unreachable",
        TerminatorKind::InlineAsm { .. } => "InlineAsm",
        _ => "unsupported",
    }
}

fn rvalue_name(rvalue: &Rvalue<'_>) -> &'static str {
    match rvalue {
        Rvalue::Ref(..) => "Ref",
        Rvalue::RawPtr(..) => "RawPtr",
        Rvalue::Cast(..) => "Cast",
        Rvalue::Aggregate(..) => "Aggregate",
        Rvalue::BinaryOp(..) => "BinaryOp",
        Rvalue::UnaryOp(..) => "UnaryOp",
        _ => "unsupported",
    }
}
