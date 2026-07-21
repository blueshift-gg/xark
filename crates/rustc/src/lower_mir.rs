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
    Body, Const, ConstOperand, ConstValue, Operand, Place, Rvalue, START_BLOCK, StatementKind,
    TerminatorKind,
};
use rustc_middle::ty::TyCtxt;

use xark_ir::primitive::{self, PrimitiveProgram, WitnessGen};
use xark_ir::{
    ConstraintKind, ConstraintProfile, FieldSpec, LinearCombination, R1csConstraint, R1csProgram,
    VarId, Variable, Visibility,
};

use crate::diagnostics::{CompileError, CompileResult};
use crate::find_entry::EntryInfo;

/// A MIR-lowering slot path — the projection into a local (`[]` for a scalar,
/// `[i]`/`[i, j]` for array/tuple elements). Almost always depth ≤ 2, so inline
/// `SmallVec` storage keeps every field-slot map key and `resolve_place` result
/// off the heap — this was the dominant allocation in lowering large circuits.
type SlotPath = smallvec::SmallVec<[u64; 4]>;

/// A stable, `Ord`-able key for a canonical [`LinearCombination`]: its constant
/// plus its sorted `(coeff, var)` terms, all as canonical decimal strings
/// (`FieldConst::decimal` is always `BigInt::to_string()` output, so equal
/// values compare equal). Used to memoize bit decompositions (see `bit_cache`).
type CanonicalLcKey = (String, Vec<(String, VarId)>);

/// Build the [`CanonicalLcKey`] for `lc` (simplified → merged + sorted terms).
fn canonical_lc_key(lc: &LinearCombination) -> CanonicalLcKey {
    let lc = lc.clone().simplified();
    (
        lc.constant.decimal(),
        lc.terms
            .iter()
            .map(|t| (t.coeff.decimal().clone(), t.var))
            .collect(),
    )
}

/// Is `name` a low-level arithmetic/conversion operator impl method? These are
/// noise in a profiling function chain (`s * a` is a `mul` impl, `a + 3` an `add`
/// impl, `Field::from(n)` a `from` impl), so they are elided so the chain reads
/// at function granularity. Kept: comparison methods (`lt`/`gt`/…), `to_bits`,
/// `require_bool`, `is_zero`, and every user/library function.
fn is_operator_impl_name(name: &str) -> bool {
    matches!(
        name,
        "add" | "sub" | "mul" | "neg" | "bitxor" | "from" | "into"
    )
}

/// The [`ConstraintKind`] a function *fixes* for every constraint emitted
/// inside it (pushed onto `kind_stack` while it is inlined). `require_bool`'s
/// `b*b=b` flows through `emit_mul` but must read as a booleanity check, not a
/// multiplication; the inverse function `inv`'s `x·w == 1` pins a hint output.
fn function_kind_hint(name: &str) -> Option<ConstraintKind> {
    Some(match name {
        "require_bool" => ConstraintKind::Booleanity,
        "inv" => ConstraintKind::HintPin,
        _ => return None,
    })
}

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
    /// `witness_begin()` / `witness_end()` — open/close a **witness-only** region.
    /// Inside it, value-producing ops still emit their witness-gen (so the solver
    /// fills them) but emit **no constraints**; the vars they allocate are exempt
    /// from `check_pinning`. Used to *derive* advice (e.g. a GLV decomposition)
    /// with zero constraint cost, pinning only the final result downstream.
    WitnessBegin,
    WitnessEnd,
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
    // Comparison intrinsics returning a `bool` ({0,1} wire). They back
    // `PartialEq`/`PartialOrd` on `Field` so `==` `!=` `<` `<=` `>` `>=` are
    // circuit operations. `ULt` carries the width `N` in the call's const
    // generic arg (from a native-int RHS or an explicit `a.lt::<N>(b)`).
    Eq,
    ULt,
    BoolToField,
    // `for` desugaring (modeled, not inlined): the two `core` iterator calls plus
    // `RangeInclusive::new`. See `lower_call` for how each is folded into the
    // compile-time loop-unrolling machinery. `IntoIter`/`IterNext` handle both a
    // constant integer range and a fixed-size array (by value or by reference).
    IntoIter,
    IterNext,
    RangeInclusiveNew,
}

/// Resolve a (possibly trait-method) call to its concrete monomorphized impl
/// `Instance`. The MIR references trait methods like `<Field as From<u8>>::from`
/// as the generic `core::convert::From::from` (no MIR); resolving with the
/// call's generic args points them at the impl, which has MIR to inline. Falls
/// back to the original id. Used for inlining and MIR-availability checks — call
/// *recognition* keys on the pre-resolution id (see [`CallRegistry::classify`]).
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

/// A recognized-call registry: an exact `DefId → KnownCall` map, resolved once
/// per compile (in `after_analysis`, before validation/lowering) by
/// [`build_call_registry`]. It replaces the old fragile def-path *string*
/// matching (`s.contains("__xark_add")`, `s.ends_with("::add")`, …) with `DefId`
/// equality, so a same-named method on another type can never be misclassified.
#[derive(Clone)]
pub(crate) struct CallRegistry {
    // `DefId` is deliberately not `Ord`/`Hash`-stable across compiles, so a
    // (small, ≈two-dozen-entry) association list keyed by `Eq` is both correct
    // and deterministic. Recognition only ever does point lookups, never
    // iteration, so linear scan is fine and order is irrelevant.
    map: Vec<(DefId, KnownCall)>,
    /// `Field::to_bits` (a `Field` inherent method with no [`KnownCall`]) — the
    /// bit-cache hooks this specific decomposition method (see [`Self::is_to_bits`]).
    to_bits: Option<DefId>,
    /// The `core::ops::Range` *struct* type (the exclusive `a..b` range), used to
    /// recognize its aggregate literal (see [`Self::is_exclusive_range_ty`]).
    range_ty: Option<DefId>,
}

impl CallRegistry {
    /// Classify a called function by its **pre-resolution** `DefId` — the one
    /// from `Operand::const_fn_def`, *before* `resolve_call_instance`.
    ///
    /// Two invariants make the pre-resolution id the right key:
    ///  * The `xark` intrinsics/constants/`require_eq` are free functions or
    ///    inherent methods, so resolution is the identity (pre == post).
    ///  * The `for`-desugaring calls appear in MIR as their trait-method
    ///    (`IntoIterator::into_iter` / `Iterator::next`) `DefId`, which is the
    ///    lang-item id we register; resolving them first would point at a
    ///    concrete impl and miss.
    ///
    /// The `Field` operator/hint *methods* (`<Field as Add>::add`,
    /// `Field::hint_bit`, `PartialEq::eq`, …) are deliberately absent: they
    /// return `None` here and fall through to inlining, and every one of their
    /// bodies calls a registered `__xark_*` intrinsic, so the effect is reached
    /// there instead (all their MIR is encoded via `-Zalways-encode-mir`).
    pub(crate) fn classify(&self, def_id: DefId) -> Option<KnownCall> {
        self.map
            .iter()
            .find(|(d, _)| *d == def_id)
            .map(|(_, kc)| *kc)
    }

    fn insert(&mut self, def_id: DefId, kc: KnownCall) {
        self.map.push((def_id, kc));
    }

    /// Is this call `Field::to_bits::<N>`? (Not `from_bits`.) The bit-cache hooks
    /// this specific decomposition method so a value decomposed to the same width
    /// more than once shares one decomposition (see `docs/integer-ops.md`). Keyed
    /// on the same pre-resolution `DefId` as `classify`; for this generic inherent
    /// method resolution is the identity, so the resolved call id matches too.
    pub(crate) fn is_to_bits(&self, def_id: DefId) -> bool {
        self.to_bits == Some(def_id)
    }

    /// Is `did` the exclusive `core::ops::Range` struct? (`RangeInclusive`/
    /// `RangeFrom`/… are distinct types with distinct `DefId`s.) Used to spot the
    /// `Range { start, end }` aggregate literal of a `for a..b` loop.
    pub(crate) fn is_exclusive_range_ty(&self, did: DefId) -> bool {
        self.range_ty == Some(did)
    }
}

/// Map a bare `__xark_*` intrinsic name (a function directly in `xark`'s
/// `intrinsics` module) to its [`KnownCall`]. The sole remaining place the ABI
/// is keyed by name — but against a *known module's* enumerated children, so a
/// typo renames the intrinsic on both sides at once (the stub is unused
/// otherwise). Every entry corresponds to exactly one stub in `intrinsics.rs`.
fn intrinsic_known_call(name: &str) -> Option<KnownCall> {
    Some(match name {
        "__xark_add" => KnownCall::Add,
        "__xark_sub" => KnownCall::Sub,
        "__xark_mul" => KnownCall::Mul,
        "__xark_neg" => KnownCall::Neg,
        "__xark_pow_u64" => KnownCall::PowU64,
        "__xark_xor" => KnownCall::Xor,
        "__xark_or" => KnownCall::Or,
        "__xark_eq" => KnownCall::Eq,
        "__xark_ult" => KnownCall::ULt,
        "__xark_bool_to_field" => KnownCall::BoolToField,
        "__xark_advice" => KnownCall::Advice,
        "__xark_hint_inverse" => KnownCall::HintInverse,
        "__xark_hint_inverse_or_zero" => KnownCall::HintInverseOrZero,
        "__xark_hint_bit" => KnownCall::HintBit,
        "__xark_hint_div_rem" => KnownCall::HintDivRem,
        "__xark_hint_mulmod_divmod" => KnownCall::HintMulModDivMod,
        "__xark_hint_mod_inverse" => KnownCall::HintModInverse,
        "__xark_hint_sub2" => KnownCall::HintSub2,
        _ => return None,
    })
}

/// Resolve every recognized call to its concrete `DefId` **once** per compile.
///
/// Sources:
///  * the `__xark_*` stubs in `xark::intrinsics` (enumerated, mapped by name);
///  * the `Field` constant constructors `constant` / `constant_u64` /
///    `constant_u128` (inherent methods — no `__xark_*` intrinsic) and the free
///    `require_eq` function, all in the `xark` crate;
///  * the three `for`-loop lang items `into_iter` / `next` / `RangeInclusive::new`.
///
/// The `xark` crate is a dependency of the circuit being compiled; we find it in
/// `tcx.crates(())` and walk its `module_children` def tree.
pub(crate) fn build_call_registry(tcx: TyCtxt<'_>) -> CallRegistry {
    use rustc_hir::def::{DefKind, Res};

    let mut reg = CallRegistry {
        map: Vec::new(),
        to_bits: None,
        range_ty: None,
    };

    if let Some(cnum) = tcx
        .crates(())
        .iter()
        .copied()
        .find(|&cnum| tcx.crate_name(cnum).as_str() == "xark")
    {
        let root = cnum.as_def_id();
        for child in tcx.module_children(root) {
            let name = child.ident.name;
            match child.res {
                // The scalar equality intrinsic (`require_eq` dispatches down to it via
                // `RequireEqCircuit`); re-exported doc-hidden at the crate root.
                Res::Def(DefKind::Fn, def_id) if name.as_str() == "__xark_require_eq_scalar" => {
                    reg.insert(def_id, KnownCall::ConstrainEq);
                }
                // Witness-only region markers (re-exported at the crate root).
                Res::Def(DefKind::Fn, def_id) if name.as_str() == "witness_begin" => {
                    reg.insert(def_id, KnownCall::WitnessBegin);
                }
                Res::Def(DefKind::Fn, def_id) if name.as_str() == "witness_end" => {
                    reg.insert(def_id, KnownCall::WitnessEnd);
                }
                // The `Field` type: register its constant constructors (inherent
                // methods with no `__xark_*` intrinsic backing).
                Res::Def(DefKind::Struct, field_did) if name.as_str() == "Field" => {
                    for &impl_did in tcx.inherent_impls(field_did) {
                        for item in tcx.associated_items(impl_did).in_definition_order() {
                            // `to_bits` is tracked separately (bit-cache hook, not
                            // a `KnownCall`); the constants map to `KnownCall`s.
                            if item.name().as_str() == "to_bits" {
                                reg.to_bits = Some(item.def_id);
                                continue;
                            }
                            let kc = match item.name().as_str() {
                                "constant" => KnownCall::FieldConstantDecimal,
                                "constant_u64" => KnownCall::FieldConstantU64,
                                "constant_u128" => KnownCall::FieldConstantU128,
                                _ => continue,
                            };
                            reg.insert(item.def_id, kc);
                        }
                    }
                }
                // The `intrinsics` module: map each `__xark_*` stub by name.
                Res::Def(DefKind::Mod, mod_did) if name.as_str() == "intrinsics" => {
                    for item in tcx.module_children(mod_did) {
                        if let Res::Def(DefKind::Fn, def_id) = item.res
                            && let Some(kc) = intrinsic_known_call(item.ident.name.as_str()) {
                                reg.insert(def_id, kc);
                            }
                    }
                }
                _ => {}
            }
        }
    }

    // `for`-loop desugaring lang items. These appear in MIR as their trait /
    // inherent method `DefId` (see `CallRegistry::classify`), which is exactly
    // what the lang-item table records.
    let li = tcx.lang_items();
    if let Some(did) = li.into_iter_fn() {
        reg.insert(did, KnownCall::IntoIter);
    }
    if let Some(did) = li.next_fn() {
        reg.insert(did, KnownCall::IterNext);
    }
    if let Some(did) = li.range_inclusive_new_method() {
        reg.insert(did, KnownCall::RangeInclusiveNew);
    }
    // The exclusive `core::ops::Range` struct type (`#[lang = "Range"]`); its
    // aggregate literal marks a `for a..b` loop.
    reg.range_ty = li.range_struct();

    reg
}

/// The diagnostic for a `for` over anything but a constant integer range.
fn unsupported_iterator() -> CompileError {
    CompileError::new("only `for` over a constant integer range is supported")
        .with_note(
            "iterating arrays/slices, `.iter()`, `.enumerate()`, `.rev()`, `.step_by()`, and \
             other iterator adapters are not circuit operations",
        )
        .with_help("use `for i in 0..N { .. }` with constant `N`, or a `while` loop")
}

/// Read a range bound operand as a compile-time-constant integer, rejecting a
/// witness/non-const bound (`for i in 0..n`) with a clear diagnostic.
fn range_bound<'tcx>(env: &LoweringEnv<'tcx>, operand: &Operand<'tcx>) -> CompileResult<u128> {
    env.operand_to_int(operand).map(|v| v as u128).ok_or_else(|| {
        CompileError::new("`for` range bounds must be compile-time constants")
            .with_note("a circuit has no runtime control flow, so the loop length must be fixed")
            .with_help("use constant bounds, e.g. `for i in 0..N`; for data-dependent work require a boolean and mux with `b + cond·(a − b)`")
    })
}

/// A map keyed by MIR `Local`, stored as a dense `Vec` indexed by the local's
/// index — O(1) get/set (vs `BTreeMap`'s log-n + key comparison), and the
/// single biggest lower-phase cost. Iteration yields locals in ascending
/// `Local` order, so lowering stays byte-for-byte deterministic.
#[derive(Clone, Debug, Default)]
struct LocalMap<V> {
    slots: Vec<Option<V>>,
}
impl<V> LocalMap<V> {
    #[inline]
    fn get(&self, local: rustc_middle::mir::Local) -> Option<&V> {
        self.slots.get(local.as_usize()).and_then(Option::as_ref)
    }
    #[inline]
    fn get_mut(&mut self, local: rustc_middle::mir::Local) -> Option<&mut V> {
        self.slots
            .get_mut(local.as_usize())
            .and_then(Option::as_mut)
    }
    #[inline]
    fn remove(&mut self, local: rustc_middle::mir::Local) -> Option<V> {
        self.slots.get_mut(local.as_usize()).and_then(Option::take)
    }
    /// Get the slot for `local`, inserting `V::default()` if empty (like
    /// `BTreeMap::entry(local).or_default()`), growing the backing `Vec` as needed.
    #[inline]
    fn or_default_mut(&mut self, local: rustc_middle::mir::Local) -> &mut V
    where
        V: Default,
    {
        let i = local.as_usize();
        if i >= self.slots.len() {
            self.slots.resize_with(i + 1, || None);
        }
        self.slots[i].get_or_insert_with(V::default)
    }
    fn iter(&self) -> impl Iterator<Item = (rustc_middle::mir::Local, &V)> {
        self.slots.iter().enumerate().filter_map(|(i, o)| {
            o.as_ref()
                .map(|v| (rustc_middle::mir::Local::from_usize(i), v))
        })
    }
}

#[derive(Default)]
struct Frame {
    // Path-keyed slot maps use `BTreeMap` so iteration is deterministic and
    // path-sorted — array/tuple slots reconstruct in index order regardless of
    // insertion, avoiding order-dependent lowering bugs. The outer per-`Local`
    // map is a dense `LocalMap` (the hot path).
    field: LocalMap<BTreeMap<SlotPath, LinearCombination>>,
    int: LocalMap<BTreeMap<SlotPath, u128>>,
    str: BTreeMap<rustc_middle::mir::Local, String>,
    // `for` desugaring state, all purely compile-time:
    // - `range_iter`: a local holding a `Range`/`RangeInclusive` iterator's
    //   current cursor + bound (established by the `Range { .. }` aggregate or
    //   `RangeInclusive::new`, carried through `into_iter`/moves).
    // - `ref_alias`: a `&mut iter` reference local → the base iterator local it
    //   points at, so `next(&mut iter)` finds the state to advance.
    // - `opt_disc`: a local holding a modeled `Option` produced by `next` → its
    //   discriminant (0 = None, 1 = Some); the `Some` payload lives in int slot
    //   `[0]` so `(_opt as Some).0` reads back as a constant.
    range_iter: BTreeMap<rustc_middle::mir::Local, RangeState>,
    // A local holding a fixed-size-array iterator (`for x in arr` / `for x in
    // &arr`): the array's element values plus a cursor, modeled like a range.
    array_iter: BTreeMap<rustc_middle::mir::Local, ArrayIterState>,
    ref_alias: BTreeMap<rustc_middle::mir::Local, rustc_middle::mir::Local>,
    opt_disc: BTreeMap<rustc_middle::mir::Local, u128>,
}

/// A compile-time fixed-size-array iterator's state. `elems[i]` is element `i`'s
/// field slots as `(path-relative-to-the-element, lc)` (one entry for a scalar
/// `Field`, N for a nested `[Field; N]`), and `cursor` the next index to yield.
#[derive(Clone, Debug)]
struct ArrayIterState {
    elems: Vec<Vec<(Vec<u64>, LinearCombination)>>,
    cursor: usize,
}

/// A compile-time integer-range iterator's state. `cur` is the next value to
/// yield; `end` the (exclusive or inclusive) bound. For `RangeInclusive`,
/// `exhausted` records that the final `end` value has been yielded (matching
/// `RangeInclusive`'s internal flag, since `cur == end` is ambiguous otherwise).
#[derive(Clone, Copy, Debug)]
struct RangeState {
    cur: u128,
    end: u128,
    inclusive: bool,
    exhausted: bool,
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
    /// following `require_eq`.
    pending_mul: BTreeMap<VarId, (usize, usize)>,
    /// Mul outputs folded into a following `require_eq`, keyed to
    /// `(a, b, witness_gen_index, original_constraint_index)` so `finish` can
    /// revive `a·b = out` if the var is referenced again after the merge (and
    /// re-attribute the revived constraint from the original's profile record).
    merged: BTreeMap<VarId, (LinearCombination, LinearCombination, usize, usize)>,
    /// The witness-generation ("hint") program, in dependency order. `None`
    /// entries are ops whose output var was merged away (dropped at finish).
    witness_gen: Vec<Option<WitnessGen>>,
    /// Stack of function `DefId`s currently being inlined (recursion guard).
    inlining: Vec<DefId>,
    /// Parallel to `inlining`: the generic args of each inlined instance, used
    /// to monomorphize nested calls in a generic callee body (e.g. the blanket
    /// `Into::into`, whose body calls `From::from` with the impl's type params).
    inline_substs: Vec<rustc_middle::ty::GenericArgsRef<'tcx>>,
    /// Bit-decomposition memo: `(canonical LC of x, width N) → the N bit vars`.
    /// A `to_bits::<N>(x)` on a value already decomposed to that width reuses the
    /// stored bits, skipping the redundant `N` booleanity + 1 recomposition
    /// constraints. Circuit values are immutable in the lowering (each local is a
    /// stable LC), so cached bits never go stale (docs/integer-ops.md § Bit caching).
    bit_cache: BTreeMap<(CanonicalLcKey, usize), Vec<VarId>>,
    /// Frontend-function memoization: per `(DefId, substs)`, the
    /// constraints one inline of that monomorphization emits, captured with vars
    /// classified internal-vs-external, so a later call can be replayed (a `CALL`)
    /// instead of re-walked. Verified by byte-comparing the replay against the
    /// real walk.
    function_templates: BTreeMap<String, FunctionTemplate>,
    call_memo_total: usize,
    call_memo_ok: usize,
    /// Cache of `is_function(def_id)` keyed by `(krate, index)` — the all-Field
    /// signature check is asked per call site.
    function_is_cache: BTreeMap<(u32, u32), bool>,
    /// Nesting depth of function-body lowering. While `> 0`, cross-call caches (the
    /// bit-decomposition cache) are suppressed so a function body is a pure function
    /// of its inputs — otherwise a later call sharing a cached value would make
    /// replay diverge from a walk.
    function_depth: usize,
    /// Inside a `witness_begin()`/`witness_end()` region: value-producing ops emit
    /// their witness-gen but no constraints, and every var allocated is added to
    /// `witness_only_vars` (exempt from `check_pinning`).
    witness_only: bool,
    /// Vars allocated inside a witness-only region — pinning-exempt (their only
    /// role is to feed the witness-gen of a downstream, separately-pinned result).
    witness_only_vars: BTreeSet<VarId>,
    /// Each function call's `(key, constraint start, end, base var, plug vars,
    /// witness start, witness end)` — a `CALL` replaces both the constraint range
    /// and the witness-gen range with one small record; expansion remaps the
    /// stored def by `(base, plugs)`. Feeds the compact `circuit.xbc` builder; the
    /// witness bounds let the compact form round-trip the *witness* program, not
    /// just the constraints (a complete circuit artifact).
    #[allow(clippy::type_complexity)] // a positional encoding record, not a public type
    function_calls: Vec<(
        String,
        usize,
        usize,
        VarId,
        Vec<LinearCombination>,
        usize,
        usize,
    )>,
    /// Fold-threshold decisions from the measuring pre-pass, keyed by function key.
    /// `Some(map)` = pass 2: a function call is treated as a `CALL` only when
    /// `map[key] == true` (called `>= 2` times and body `>= N` constraints);
    /// otherwise it is inlined (folded). `None` = single pass / pass 1: template
    /// every function (original behavior, and how the pre-pass measures).
    promotions: Option<BTreeMap<String, bool>>,
    /// Per-key function call counts, tallied during the measuring pass (`lower`
    /// pass 1). Keys called `>= 2` times become templated `CALL`s; single-use
    /// functions inline so their `mul→require_eq` merges and debug notes survive.
    function_call_counts: BTreeMap<String, u32>,
    /// Exact `DefId → KnownCall` table, resolved once up front (see
    /// [`CallRegistry`]). Replaces def-path string matching in call recognition.
    registry: CallRegistry,
    // --- profiling (see `docs`/`profile.json`; kept entirely OUT of the R1CS) ---
    /// Whether to build the per-constraint [`ConstraintProfile`] buffer. Only set
    /// by `xark profile` (via the `--profile` flag); a normal build leaves this
    /// `false` so lowering does zero span-resolution work.
    profile_enabled: bool,
    /// The span of the *top-level* circuit statement/terminator currently being
    /// lowered (set only at inline depth 0, never overwritten during inline
    /// recursion — so a constraint emitted deep inside an inlined function still
    /// attributes to the user's circuit line).
    root_span: Option<rustc_span::Span>,
    /// Parallel to `constraints`: one attribution record per emitted constraint,
    /// pushed alongside it in [`Self::push_constraint`] (only when profiling).
    profile: Vec<ConstraintProfile>,
    /// Kind-override stack: a function (or an emit helper) pushes a kind here so
    /// every constraint emitted while it is on top is attributed to that kind,
    /// overriding the emit-site's natural kind (e.g. `require_bool`'s `b*b=b` goes
    /// through `emit_mul` but should read as `Booleanity`, not `Mul`).
    kind_stack: Vec<ConstraintKind>,
    /// Every var proven boolean by an emitted `v · v = v` constraint (⟺ v ∈
    /// {0,1}). Populated wherever such a constraint is pushed — range-proof bits,
    /// comparison borrow bits, `require_bool`, and any replayed function booleanity —
    /// so the `to_bits::<N>` bit-sum shortcut can recognize an input `Σ 2ⁱ·bᵢ`
    /// whose bits are ALREADY booleanity-constrained and return them directly
    /// instead of emitting a fresh (redundant) decomposition. Only genuine `v·v=v`
    /// rows enter this set — never a value assumed boolean (see `bit_sum_shortcut`).
    boolean_vars: BTreeSet<VarId>,
}

/// If `c` is exactly `v · v = v` (single term `1·v` on all three sides, zero
/// constants), return `v` — the constraint proves `v ∈ {0,1}`. Used to harvest
/// genuinely-boolean vars for the `to_bits` bit-sum shortcut.
fn booleanity_var(c: &R1csConstraint) -> Option<VarId> {
    let one_var = |lc: &LinearCombination| -> Option<VarId> {
        if lc.constant.is_zero() && lc.terms.len() == 1 && lc.terms[0].coeff.is_one() {
            Some(lc.terms[0].var)
        } else {
            None
        }
    };
    let a = one_var(&c.a)?;
    let b = one_var(&c.b)?;
    let cc = one_var(&c.c)?;
    (a == b && b == cc).then_some(a)
}

/// Core of [`LoweringEnv::bit_sum_shortcut`], factored out (no `self`) so it is
/// unit-testable: if `x` is exactly `Σ_{i=0}^{n-1} 2ⁱ·vᵢ` — zero constant, `n`
/// terms, each coeff a distinct power of two `2ⁱ` (`0 ≤ i < n`), each `vᵢ`
/// distinct and `is_boolean(vᵢ)` — return `[v₀..v_{n-1}]`, else `None`. The
/// `is_boolean` predicate is the *only* thing that makes the rewrite sound (each
/// `vᵢ` must already be pinned to `{0,1}`), so it is checked for every summand.
fn bit_sum_match(
    x: &LinearCombination,
    n: usize,
    is_boolean: impl Fn(VarId) -> bool,
) -> Option<Vec<VarId>> {
    if n == 0 || !x.constant.is_zero() || x.terms.len() != n {
        return None;
    }
    // Powers of two 2⁰..2^{n-1}; each term's coeff must match exactly one.
    let two = xark_ir::FieldConst::from_i64(2);
    let mut pow = xark_ir::FieldConst::one();
    let mut pows: Vec<xark_ir::FieldConst> = Vec::with_capacity(n);
    for _ in 0..n {
        pows.push(pow.clone());
        pow = pow.mul(&two);
    }
    let mut slot: Vec<Option<VarId>> = vec![None; n];
    let mut seen: BTreeSet<VarId> = BTreeSet::new();
    for term in &x.terms {
        let i = pows.iter().position(|p| *p == term.coeff)?;
        if slot[i].is_some() || !seen.insert(term.var) || !is_boolean(term.var) {
            return None;
        }
        slot[i] = Some(term.var);
    }
    // All `n` distinct slots filled (terms.len() == n, each a distinct index).
    slot.into_iter().collect()
}

/// A value passed into or returned from an inlined function. `Fields` carries a
/// whole scalar-or-array value as `(relative-path, lc)` slots — a scalar is a
/// single `([], lc)`, an array is `([0], ..), ([1], ..), ...`.
enum ArgValue {
    Fields(Vec<(Vec<u64>, LinearCombination)>),
    Int(u128),
    /// A whole *integer* array/tuple, as `(relative-path, value)` slots — the int
    /// analogue of `Fields`. Lets a `const [uN; M]` be passed into an inlined
    /// function and read back with native-int ops (e.g. `Field::from(bytes[i])`),
    /// mirroring how `Fields` carries a whole `Field` array across the boundary.
    Ints(Vec<(Vec<u64>, u128)>),
    Str(String),
    Unit,
}

impl<'tcx> LoweringEnv<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, registry: CallRegistry, profile_enabled: bool) -> Self {
        LoweringEnv {
            tcx,
            registry,
            profile_enabled,
            root_span: None,
            profile: Vec::new(),
            kind_stack: Vec::new(),
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
            bit_cache: BTreeMap::new(),
            function_templates: BTreeMap::new(),
            call_memo_total: 0,
            call_memo_ok: 0,
            function_is_cache: BTreeMap::new(),
            function_depth: 0,
            witness_only: false,
            witness_only_vars: BTreeSet::new(),
            function_calls: Vec::new(),
            promotions: None,
            function_call_counts: BTreeMap::new(),
            boolean_vars: BTreeSet::new(),
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
    fn get_field_at(
        &self,
        local: rustc_middle::mir::Local,
        path: &[u64],
    ) -> Option<LinearCombination> {
        self.frame()
            .field
            .get(local)
            .and_then(|m| m.get(path).cloned())
    }
    fn set_field_at(
        &mut self,
        local: rustc_middle::mir::Local,
        path: &[u64],
        lc: LinearCombination,
    ) {
        self.frame_mut()
            .field
            .or_default_mut(local)
            .insert(SlotPath::from_slice(path), lc);
    }

    /// Resolve a place to `(base local, constant projection path)`.
    ///
    /// Only array `Index`/`ConstantIndex` projections with compile-time-constant
    /// indices are supported; the loop unroller ensures indices are constant.
    fn resolve_place(
        &self,
        place: &Place<'tcx>,
    ) -> CompileResult<(rustc_middle::mir::Local, SlotPath)> {
        self.resolve_place_inner(place)
    }
    fn resolve_place_inner(
        &self,
        place: &Place<'tcx>,
    ) -> CompileResult<(rustc_middle::mir::Local, SlotPath)> {
        let mut path = SlotPath::new();
        for elem in place.projection.iter() {
            match elem {
                rustc_middle::mir::ProjectionElem::Index(idx_local) => {
                    let idx = self.get_int(idx_local).ok_or_else(|| {
                        CompileError::new("array index must be a compile-time constant")
                            .with_note("witness-dependent indexing is not supported")
                            .with_help(
                                "use a literal index or a loop variable the unroller can fold to a \
                                 constant; for a data-dependent choice, require a boolean and mux with \
                                 `b + cond·(a − b)`",
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
                // Enum-variant selector, e.g. `(_opt as Some).0` reading a
                // modeled `Option` produced by a range `next`. It selects a
                // variant but contributes nothing to the slot path (the following
                // `Field` does); a genuine non-modeled downcast simply misses.
                rustc_middle::mir::ProjectionElem::Downcast(..) => {}
                // Transparent reference: `&x` copies `x`'s slots to the reference
                // local, so a later `*r` reads them straight back. Used by
                // by-reference array iteration (`for x in &arr`, whose `next`
                // yields `&Field` that the body then dereferences).
                rustc_middle::mir::ProjectionElem::Deref => {}
                other => {
                    return Err(CompileError::new(format!(
                        "unsupported place projection: {other:?}"
                    )));
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
        self.frame().int.get(local)?.get(path).copied()
    }
    fn set_int_at(&mut self, local: rustc_middle::mir::Local, path: &[u64], v: u128) {
        self.frame_mut()
            .int
            .or_default_mut(local)
            .insert(SlotPath::from_slice(path), v);
    }
    fn get_str(&self, local: rustc_middle::mir::Local) -> Option<String> {
        self.frame().str.get(&local).cloned()
    }
    fn set_str(&mut self, local: rustc_middle::mir::Local, s: String) {
        self.frame_mut().str.insert(local, s);
    }
    /// Drop all slots (field / int / str / range-iter / option) tracked for
    /// `local` in the current frame — used on `StorageLive` so a reused local
    /// starts clean.
    fn clear_local(&mut self, local: rustc_middle::mir::Local) {
        let f = self.frame_mut();
        f.field.remove(local);
        f.int.remove(local);
        f.str.remove(&local);
        f.range_iter.remove(&local);
        f.array_iter.remove(&local);
        f.ref_alias.remove(&local);
        f.opt_disc.remove(&local);
    }

    // --- `for`-loop iterator state -----------------------------------------

    fn set_range_state(&mut self, local: rustc_middle::mir::Local, st: RangeState) {
        self.frame_mut().range_iter.insert(local, st);
    }
    /// Remove and return the range state tracked for `local` (used to *move* it
    /// through `into_iter` / `let iter = range`).
    fn take_range_state(&mut self, local: rustc_middle::mir::Local) -> Option<RangeState> {
        self.frame_mut().range_iter.remove(&local)
    }
    fn set_array_iter(&mut self, local: rustc_middle::mir::Local, st: ArrayIterState) {
        self.frame_mut().array_iter.insert(local, st);
    }
    fn take_array_iter(&mut self, local: rustc_middle::mir::Local) -> Option<ArrayIterState> {
        self.frame_mut().array_iter.remove(&local)
    }
    /// The base iterator local a place refers to: either the iterator itself
    /// (range or array), or a `&mut iter` reference resolved through `ref_alias`.
    /// The reborrow chain (`&mut iter` then `&mut (*r)`) always refers to the
    /// whole iterator, so the projection (a `Deref`) is irrelevant.
    fn iter_base_of_place(&self, place: &Place<'tcx>) -> Option<rustc_middle::mir::Local> {
        let f = self.frame();
        if f.range_iter.contains_key(&place.local) || f.array_iter.contains_key(&place.local) {
            Some(place.local)
        } else {
            f.ref_alias.get(&place.local).copied()
        }
    }
    fn set_ref_alias(&mut self, from: rustc_middle::mir::Local, to: rustc_middle::mir::Local) {
        self.frame_mut().ref_alias.insert(from, to);
    }
    fn set_opt_disc(&mut self, local: rustc_middle::mir::Local, disc: u128) {
        self.frame_mut().opt_disc.insert(local, disc);
    }
    fn get_opt_disc(&self, local: rustc_middle::mir::Local) -> Option<u128> {
        self.frame().opt_disc.get(&local).copied()
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
        if self.witness_only {
            self.witness_only_vars.insert(id);
        }
        id
    }

    fn alloc_internal(&mut self) -> VarId {
        let name = format!("t{}", self.internal_counter);
        self.internal_counter += 1;
        self.alloc_var(name, Visibility::Internal)
    }

    /// Is `def_id` a user-declared frontend function? Recognized two ways:
    /// `#[no_mangle]` (a stable symbol, non-generic only), or auto-DAG — any
    /// non-`#[inline(never)]` function with an all-Field signature. Cached per
    /// `(krate, index)`.
    fn is_function(&mut self, def_id: DefId) -> bool {
        use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
        let key = (def_id.krate.as_u32(), def_id.index.as_u32());
        if let Some(&b) = self.function_is_cache.get(&key) {
            return b;
        }
        let b = self
            .tcx
            .codegen_fn_attrs(def_id)
            .flags
            .contains(CodegenFnAttrFlags::NO_MANGLE)
            // Auto-DAG: any non-`#[inline(never)]` function with an all-Field
            // signature. The arithmetic operators (`add`/`sub`/`mul`/`neg`) and the
            // `__xark_*` intrinsics are all `#[inline(never)]`, so the free/linear
            // primitives stay inlined and every composite becomes a function.
            || (auto_dag_enabled() && !self.has_inline_never(def_id) && self.all_field_sig(def_id));
        self.function_is_cache.insert(key, b);
        b
    }

    fn has_inline_never(&self, def_id: DefId) -> bool {
        use rustc_hir::attrs::InlineAttr;
        matches!(self.tcx.codegen_fn_attrs(def_id).inline, InlineAttr::Never)
    }

    /// Are all of `def_id`'s parameters Field-like (Field / arrays / tuples /
    /// structs of Field), and its return Field-like with at least one leaf? Only
    /// such functions have materializable plugs.
    fn all_field_sig(&self, def_id: DefId) -> bool {
        if !self.tcx.is_mir_available(def_id) {
            return false;
        }
        let sig = self.tcx.fn_sig(def_id).instantiate_identity().skip_binder();
        let tys = sig.inputs_and_output;
        let n = tys.len();
        for (i, ty) in tys.iter().enumerate() {
            let mut out = Vec::new();
            let mut path = Vec::new();
            if flatten_field_leaves(self.tcx, ty, &mut path, "", &mut out).is_err() {
                return false;
            }
            if i == n - 1 && out.is_empty() {
                return false; // the return must carry at least one Field leaf
            }
        }
        true
    }

    /// Force `lc` to a single variable (a function plug): if it's already `1·v`,
    /// return `v`; otherwise allocate `v`, emit `lc·1 = v` and its witness, return
    /// `v`. The materialization that gives functions stable single-var ports.
    fn materialize_to_var(&mut self, lc: LinearCombination) -> VarId {
        if lc.constant.is_zero() && lc.terms.len() == 1 && lc.terms[0].coeff.is_one() {
            return lc.terms[0].var;
        }
        let v = self.alloc_internal();
        let id = self.fresh_constraint_id();
        self.witness_gen.push(Some(WitnessGen::Linear {
            out: v,
            lc: lc.clone(),
        }));
        self.push_constraint(
            ConstraintKind::Other,
            R1csConstraint::equal(id, lc, LinearCombination::var(v), ""),
        );
        v
    }

    /// If `x` is exactly the `n`-bit sum `Σ_{i=0}^{n-1} 2ⁱ·vᵢ` — zero constant,
    /// exactly `n` terms, each coefficient a *distinct* power of two `2ⁱ`
    /// (`0 ≤ i < n`), and every `vᵢ` a *distinct* var already proven boolean by a
    /// `v·v=v` row (see `boolean_vars`) — return `[v₀..v_{n-1}]`.
    ///
    /// Then `to_bits::<n>(x)` returns those bits directly: with every `vᵢ ∈ {0,1}`
    /// and `x = Σ 2ⁱ·vᵢ`, the `vᵢ` ARE `x`'s canonical `n`-bit decomposition
    /// (exact — an `n`-bit sum lives in `[0, 2ⁿ)`, no overflow), so returning them
    /// is a lossless rewrite, NOT a new constraint. Strictly gated on genuine
    /// booleanity: a non-boolean summand, a repeated var, or a stray coefficient
    /// all yield `None` (never assume a value is boolean).
    fn bit_sum_shortcut(&self, x: &LinearCombination, n: usize) -> Option<Vec<VarId>> {
        bit_sum_match(x, n, |v| self.boolean_vars.contains(&v))
    }

    /// Allocate a fresh var `w` constrained equal to `v` (`v · 1 = w`), for
    /// forcing a distinct plug when the same var would otherwise appear twice.
    fn copy_var(&mut self, v: VarId) -> VarId {
        let w = self.alloc_internal();
        let id = self.fresh_constraint_id();
        self.witness_gen.push(Some(WitnessGen::Linear {
            out: w,
            lc: LinearCombination::var(v),
        }));
        self.push_constraint(
            ConstraintKind::Other,
            R1csConstraint::equal(id, LinearCombination::var(v), LinearCombination::var(w), ""),
        );
        w
    }

    /// Replay a captured function at this call site by **symbolic substitution**:
    /// substitute each plug var with the caller's argument linear combination
    /// (`plugs[i]`) and shift every internal (`>= base_var`) to a fresh block, then
    /// append the substituted constraints and witness ops. No plug materialization,
    /// so no `plug = arg` equality rows enter the flat R1CS. Byte-identical to
    /// re-walking with the args substituted, by construction. Returns the outputs
    /// as substituted linear combinations (a passthrough output that is an input
    /// plug returns the plug LC, not the meaningless template plug var).
    fn replay_function(
        &mut self,
        key: &str,
        plugs: &[LinearCombination],
    ) -> Vec<(Vec<u64>, LinearCombination)> {
        let t = self.function_templates.get(key).expect("template present");
        let base = self.next_var_id;
        let base_var = t.base_var;
        // Template plug var → its position, so a plug-var term substitutes the
        // caller's `plugs[i]` (scaled by the term's coefficient).
        let plug_index: BTreeMap<VarId, usize> = t
            .plug_vars
            .iter()
            .copied()
            .enumerate()
            .map(|(i, v)| (v, i))
            .collect();
        // Clone the template out of the borrow before mutating self.
        let t_constraints = t.constraints.clone();
        let t_witness = t.witness.clone();
        let var_kinds = t.var_kinds.clone();
        let t_outputs = t.outputs.clone();

        // Substitute an LC: plug var → caller plug LC (scaled); internal var →
        // base-shifted var; anything else (defensive) left as-is.
        let subst_lc = |l: &LinearCombination| -> LinearCombination {
            let mut constant = l.constant.clone();
            let mut terms: Vec<xark_ir::Term> = Vec::new();
            for term in &l.terms {
                if term.var >= base_var {
                    terms.push(xark_ir::Term {
                        coeff: term.coeff.clone(),
                        var: base + (term.var - base_var),
                    });
                } else if let Some(&idx) = plug_index.get(&term.var) {
                    let piece = plugs[idx].clone().scale(&term.coeff);
                    constant = constant.add(&piece.constant);
                    terms.extend(piece.terms);
                } else {
                    terms.push(term.clone());
                }
            }
            LinearCombination { constant, terms }.simplified()
        };
        // Witness out/id fields are always fresh internals → simple base shift.
        let remap_id = |v: VarId| -> VarId {
            if v >= base_var {
                base + (v - base_var)
            } else {
                v
            }
        };
        let cons: Vec<[LinearCombination; 3]> = t_constraints
            .iter()
            .map(|c| [subst_lc(&c.a), subst_lc(&c.b), subst_lc(&c.c)])
            .collect();
        let mut wits: Vec<WitnessGen> = t_witness;
        let outputs: Vec<(Vec<u64>, LinearCombination)> = t_outputs
            .iter()
            .map(|(p, lc)| (p.clone(), subst_lc(lc)))
            .collect();
        for w in &mut wits {
            subst_witness_vars(w, &remap_id, &subst_lc);
        }
        // Re-allocate the body's vars in the SAME order (internal/advice interleave)
        // so ids, visibilities and t{}/w{} names all match the monotonic walk.
        for kind in &var_kinds {
            let name = match kind {
                Visibility::Private => {
                    let n = format!("w{}", self.advice_counter);
                    self.advice_counter += 1;
                    n
                }
                _ => {
                    let n = format!("t{}", self.internal_counter);
                    self.internal_counter += 1;
                    n
                }
            };
            self.var_names.push(name.clone());
            self.variables.push(Variable {
                id: self.next_var_id,
                name,
                visibility: kind.clone(),
            });
            self.next_var_id += 1;
        }
        for [a, b, c] in cons {
            let id = self.fresh_constraint_id();
            let mut rc = R1csConstraint::general(id, a, b, c, "");
            rc.debug = None; // function constraints are note-free (match capture)
            self.push_constraint(ConstraintKind::Other, rc);
        }
        for w in wits {
            self.witness_gen.push(Some(w));
        }
        // Outputs are already substituted linear combinations.
        outputs
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

    // --- constraint emission + profiling -----------------------------------

    /// Push a constraint into the R1CS *and* (when profiling) record its
    /// attribution — the top-level user source line ([`Self::root_span`]), the
    /// function call-chain, and its kind — into the parallel [`Self::profile`]
    /// buffer. This is the single choke point every emit helper routes through,
    /// so `profile` stays index-aligned with `constraints` (`profile[i].id ==
    /// constraints[i].id == i`). The R1CS constraint itself is untouched by
    /// profiling, so `r1cs.json` / `circuit.json` stay byte-identical.
    fn push_constraint(&mut self, kind: ConstraintKind, c: R1csConstraint) {
        // Witness-only region: suppress every constraint (any op reached here is a
        // pin we deliberately omit — the derived result is pinned downstream). The
        // constraint-free `emit_mul` path handles the mul-merge bookkeeping.
        if self.witness_only {
            return;
        }
        if self.profile_enabled {
            let kind = self.kind_stack.last().copied().unwrap_or(kind);
            let prof = self.constraint_profile(c.id, kind);
            self.profile.push(prof);
        }
        // Harvest booleanity: an emitted `v·v=v` (range-proof bits, cmp borrow
        // bits, replayed-function booleanity) proves `v ∈ {0,1}` (see `boolean_vars`).
        if let Some(v) = booleanity_var(&c) {
            self.boolean_vars.insert(v);
        }
        self.constraints.push(c);
    }

    /// Build the [`ConstraintProfile`] for constraint `id` at the current point
    /// in lowering (root span + inline chain + kind). Called only when profiling.
    fn constraint_profile(&self, id: u32, kind: ConstraintKind) -> ConstraintProfile {
        let (file, line, col) = self.resolve_root_loc();
        ConstraintProfile {
            id,
            file,
            line,
            col,
            chain: self.function_chain(),
            kind,
        }
    }

    /// Resolve [`Self::root_span`] to `(file, 1-based line, 1-based col)`. An
    /// unset or dummy span yields `("", 0, 0)`.
    fn resolve_root_loc(&self) -> (String, u32, u32) {
        let Some(span) = self.root_span else {
            return (String::new(), 0, 0);
        };
        if span.is_dummy() {
            return (String::new(), 0, 0);
        }
        let sm = self.tcx.sess.source_map();
        let loc = sm.lookup_char_pos(span.lo());
        // `prefer_local_unconditionally` yields the local (un-remapped) path —
        // relative to the compile cwd (the crate dir), which `xark profile`
        // resolves against `source_root`. `line` is 1-based; `col_display` 0-based.
        let file = loc.file.name.prefer_local_unconditionally().to_string();
        (file, loc.line as u32, loc.col_display as u32 + 1)
    }

    /// The function call-chain (outermost → innermost) at the current emit point:
    /// each inlined callee's short name, with low-level arithmetic/conversion
    /// operator impls (`add`/`sub`/`mul`/`neg`/`bitxor`/`from`/`into`) elided so
    /// the chain reads at function granularity (e.g. `lt → to_bits → require_bool`).
    fn function_chain(&self) -> Vec<String> {
        self.inlining
            .iter()
            .map(|&did| self.tcx.item_name(did).to_string())
            .filter(|n| !is_operator_impl_name(n))
            .collect()
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
            let token = if is_one {
                name.clone()
            } else {
                format!("{abs}*{name}")
            };
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
                s.push_str(&lc.constant.decimal());
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
                            "this position needs a `Field` or a `bool` wire; a host integer, or a \
                             value from an operation the circuit can't lower, can't be used here",
                        )
                })
            }
            // A `bool` constant (`true` / `false`) — e.g. the `true` in
            // `require_eq(a < b, true)` inside `require_lt`'s body.
            Operand::Constant(c) if c.const_.ty().is_bool() => match c.const_.try_to_scalar_int() {
                Some(s) if s.to_uint(s.size()) == 1 => Ok(LinearCombination::one()),
                _ => Ok(LinearCombination::zero()),
            },
            // A `Field`-typed constant used directly as an operand — e.g.
            // `Field::from(3)` behind `a + 3`, or an associated `const` —
            // lowers to a constant linear combination.
            Operand::Constant(c) => self
                .const_field_slots(c)
                .and_then(|slots| {
                    slots
                        .into_iter()
                        .find(|(p, _)| p.is_empty())
                        .map(|(_, lc)| lc)
                })
                .ok_or_else(|| CompileError::new("unexpected constant in a field position")),
            Operand::RuntimeChecks(_) => {
                Err(CompileError::new("unexpected constant in a field position"))
            }
        }
    }

    /// Read an integer constant, evaluating named/associated `const`s (e.g. a
    /// `const N: usize = 3` used as a loop bound), not just literals.
    fn const_to_u128(&self, c: &ConstOperand<'tcx>) -> Option<u128> {
        if let Some(s) = c.const_.try_to_scalar_int() {
            return Some(s.to_uint(s.size()));
        }
        let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
        // Substitute const-generic params (e.g. `N` in a `mod_mul::<N>` function
        // used as a loop bound) with the current inlining frame's args before
        // evaluating, so const-generic functions const-fold instead of looking
        // witness-dependent.
        let konst = self.tcx.instantiate_and_normalize_erasing_regions(
            self.cur_substs(),
            typing_env,
            rustc_middle::ty::EarlyBinder::bind(c.const_),
        );
        let s = konst.try_eval_scalar_int(self.tcx, typing_env)?;
        Some(s.to_uint(s.size()))
    }

    /// Read the *pointee* of a reference-to-integer constant, e.g. the promoted
    /// `&100u32` that `x < 100u32` desugars into. The comparison traits
    /// (`PartialEq`/`PartialOrd`) take `&Rhs` — unlike the by-value arithmetic
    /// operators (`Add<u32>` etc.) — so a native-int constant RHS arrives as a
    /// promoted `&uN` rather than by value. This evaluates the reference and
    /// reads the referenced integer so `bind_use` can carry it as an ordinary
    /// int slot (which `lower_ref`/`operand_to_int` then read back through the
    /// `*rhs` deref).
    fn const_ref_int_to_u128(&self, c: &ConstOperand<'tcx>) -> Option<u128> {
        use rustc_middle::mir::interpret::alloc_range;
        use rustc_middle::ty::{self, TyKind};
        let TyKind::Ref(_, inner, _) = c.const_.ty().kind() else {
            return None;
        };
        if !inner.is_integral() {
            return None;
        }
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let konst = self.tcx.instantiate_and_normalize_erasing_regions(
            self.cur_substs(),
            typing_env,
            rustc_middle::ty::EarlyBinder::bind(c.const_),
        );
        let cv = konst.eval(self.tcx, typing_env, c.span).ok()?;
        let ConstValue::Scalar(scalar) = cv else {
            return None;
        };
        let ptr = scalar.to_pointer(&self.tcx).discard_err()?;
        let ptr = ptr.into_pointer_or_addr().ok()?;
        let (prov, offset) = ptr.prov_and_relative_offset();
        let alloc = self.tcx.global_alloc(prov.alloc_id()).unwrap_memory();
        let size = self
            .tcx
            .layout_of(typing_env.as_query_input(*inner))
            .ok()?
            .size;
        let val = alloc
            .inner()
            .read_scalar(&self.tcx, alloc_range(offset, size), false)
            .ok()?;
        val.to_uint(size).discard_err()
    }

    /// If `c` is a compile-time array of integers (e.g. a `const P: [u128; 3]`
    /// item referenced as `_1 = const P`), populate `dest`'s per-element int
    /// slots. This lets a curve function declare its field constants as ordinary
    /// `const` arrays and read them with `Field::from(P[i])` — the index projection
    /// then resolves to a tracked int slot. Returns whether it applied.
    fn try_bind_const_int_array(
        &mut self,
        dest: rustc_middle::mir::Local,
        c: &ConstOperand<'tcx>,
    ) -> bool {
        let Some(slots) = self.const_int_array_slots(c) else {
            return false;
        };
        for (i, v) in slots {
            self.set_int_at(dest, &[i as u64], v);
        }
        true
    }

    /// The per-element `(index, value)` int slots of a compile-time integer array
    /// constant (e.g. a `const P: [u128; 3]`), or `None` if `c` is not one. Shared
    /// by [`Self::try_bind_const_int_array`] (assignment binding) and [`Self::eval_arg`]
    /// (so a `const [uN; M]` can also be passed *by value* into an inlined helper).
    fn const_int_array_slots(&self, c: &ConstOperand<'tcx>) -> Option<Vec<(usize, u128)>> {
        use rustc_middle::ty::{self, TyKind};
        let TyKind::Array(elem_ty, _) = c.const_.ty().kind() else {
            return None;
        };
        if !elem_ty.is_integral() {
            return None;
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
        let branch = valtree?.try_to_branch()?;
        let mut out = Vec::with_capacity(branch.len());
        for (i, elem) in branch.iter().enumerate() {
            let ty::ConstKind::Value(v) = elem.kind() else {
                return None;
            };
            let scalar = v.valtree.try_to_leaf()?;
            out.push((i, scalar.to_uint(scalar.size())));
        }
        Some(out)
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
        let ty::ConstKind::Value(lv) = limbs_const.kind() else {
            return None;
        };
        let limb_consts = lv.valtree.try_to_branch()?;
        let mut limbs = [0u64; 4];
        for (i, lc) in limb_consts.iter().take(4).enumerate() {
            let ty::ConstKind::Value(x) = lc.kind() else {
                return None;
            };
            let s = x.valtree.try_to_leaf()?;
            limbs[i] = s.to_uint(s.size()) as u64;
        }
        Some(limbs_to_decimal(limbs))
    }

    /// If `c` is a `const Field` or `const [Field; N]` (e.g. a curve function's
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
        // integer positions (loop bound, exponent, length, comparison width, …)
        // must be compile-time constants
        let want_const = || {
            CompileError::new("expected a constant integer").with_help(
                "this must be a compile-time constant (loop bound, `^` exponent, array length, \
                 comparison width `N`, …), not a witness or runtime value",
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
                return self.get_str(place.local).ok_or_else(want_literal);
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
                ));
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
        let Some(slots) = self.frame().field.get(local) else {
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
        let Some(map) = self.frame_mut().field.get_mut(local) else {
            return Vec::new();
        };
        let keys: Vec<SlotPath> = map
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

    /// Collect a whole integer array/tuple's slots (int analogue of
    /// [`Self::collect_field_slots`]), as `(path-relative-to-`base`, value)`.
    fn collect_int_slots(
        &self,
        local: rustc_middle::mir::Local,
        base: &[u64],
    ) -> Vec<(Vec<u64>, u128)> {
        let Some(slots) = self.frame().int.get(local) else {
            return Vec::new();
        };
        slots
            .iter()
            .filter(|(p, _)| p.len() >= base.len() && p[..base.len()] == *base)
            .map(|(p, v)| (p[base.len()..].to_vec(), *v))
            .collect()
    }

    /// Evaluate a call argument in the current frame into a passable value.
    /// Handles whole `Field` arrays, not just scalars.
    fn eval_arg(&mut self, operand: &Operand<'tcx>) -> ArgValue {
        if let Operand::Copy(place) | Operand::Move(place) = operand
            && let Ok((local, base)) = self.resolve_place(place) {
                let slots = self.collect_field_slots(local, &base);
                if !slots.is_empty() {
                    return ArgValue::Fields(slots);
                }
                if let Some(v) = self.get_int_at(local, &base) {
                    return ArgValue::Int(v);
                }
                // A whole integer array/tuple (slots at `base + [i]`) — e.g. a
                // `const [u8; 32]` passed by value into a helper that indexes it.
                let int_slots = self.collect_int_slots(local, &base);
                if !int_slots.is_empty() {
                    return ArgValue::Ints(int_slots);
                }
                if base.is_empty()
                    && let Some(s) = self.get_str(local) {
                        return ArgValue::Str(s);
                    }
                return ArgValue::Unit;
            }
        if let Operand::Constant(c) = operand {
            // A `const Field` / `[Field; N]` passed directly as an argument
            // (e.g. `mod_mul(.., P::MODULUS)` with an associated-const modulus).
            if let Some(slots) = self.const_field_slots(c) {
                return ArgValue::Fields(slots);
            }
            // A `const [uN; M]` passed by value into an inlined helper that
            // indexes it (e.g. `Digest::from(SHA256_ABC)` for `const [u8; 32]`).
            if let Some(slots) = self.const_int_array_slots(c) {
                return ArgValue::Ints(
                    slots
                        .into_iter()
                        .map(|(i, v)| (vec![i as u64], v))
                        .collect(),
                );
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
            ArgValue::Ints(slots) => {
                for (rel, v) in slots {
                    let mut path = dest_path.to_vec();
                    path.extend(rel);
                    self.set_int_at(local, &path, v);
                }
            }
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
    /// through unchanged, so existing functions are unaffected.
    const LC_MATERIALIZE_THRESHOLD: usize = 8;
    fn materialize(&mut self, lc: LinearCombination) -> LinearCombination {
        if lc.terms.len() <= Self::LC_MATERIALIZE_THRESHOLD {
            return lc;
        }
        let v = self.alloc_internal();
        let id = self.fresh_constraint_id();
        // Cheap note (materialized LCs are large by definition).
        let note = format!(
            "{} = <lc: {} terms>",
            self.var_names[v as usize],
            lc.terms.len()
        );
        self.witness_gen.push(Some(WitnessGen::Linear {
            out: v,
            lc: lc.clone(),
        }));
        // Defining constraint: (lc - v) * 1 = 0.
        self.push_constraint(
            ConstraintKind::Other,
            R1csConstraint::equal(id, lc, LinearCombination::var(v), &note),
        );
        LinearCombination::var(v)
    }

    /// Emit `lhs * rhs = t` for a fresh internal `t`, returning `t`'s LC.
    fn emit_mul(&mut self, lhs: LinearCombination, rhs: LinearCombination) -> LinearCombination {
        let lhs = self.materialize(lhs);
        let rhs = self.materialize(rhs);
        let out = self.alloc_internal();
        // Witness-only: compute the product (so the solver fills `out`) but emit
        // no product constraint and no merge state — `out` is pinning-exempt scratch.
        if self.witness_only {
            self.witness_gen.push(Some(WitnessGen::Product {
                out,
                left: lhs,
                right: rhs,
            }));
            return LinearCombination::var(out);
        }
        let id = self.fresh_constraint_id();
        let note = format!(
            "{} * {} = {}",
            self.render_side(&lhs),
            self.render_side(&rhs),
            self.var_names[out as usize]
        );
        self.push_constraint(
            ConstraintKind::Mul,
            R1csConstraint::mul(id, lhs.clone(), rhs.clone(), out, &note),
        );
        let c_idx = self.constraints.len() - 1;
        // Witness-gen: the mul output is computed as `eval(lhs) * eval(rhs)`.
        self.witness_gen.push(Some(WitnessGen::Product {
            out,
            left: lhs,
            right: rhs,
        }));
        let wg_idx = self.witness_gen.len() - 1;
        // Always register the mul for the `mul → require_eq` merge. Intra-function
        // merges now fold `a*b=t; require(t==x)` → `a*b=x` *inside* a function body
        // (the caller's merge state is saved/cleared on entry so cross-boundary
        // folds stay suppressed, and body-local merges are revived at capture if
        // still referenced — keeping the template self-contained).
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
        let c_side = a.clone() + b.clone() - LinearCombination::var(c);
        let note = format!("{} = xor", self.var_names[c as usize]);
        self.push_constraint(
            ConstraintKind::Xor,
            R1csConstraint::general(id, a2, b.clone(), c_side, &note),
        );
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
        let c_side = a.clone() + b.clone() - LinearCombination::var(c);
        let note = format!("{} = or", self.var_names[c as usize]);
        self.push_constraint(
            ConstraintKind::Or,
            R1csConstraint::general(id, a.clone(), b.clone(), c_side, &note),
        );
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

    /// Whether `lc` references any witness-only var (a mul must not be merged so as
    /// to output such a var — see [`Self::emit_require_eq`]).
    fn is_witness_only_lc(&self, lc: &LinearCombination) -> bool {
        !self.witness_only_vars.is_empty()
            && lc
                .terms
                .iter()
                .any(|t| self.witness_only_vars.contains(&t.var))
    }

    fn emit_require_eq(&mut self, lhs: LinearCombination, rhs: LinearCombination) {
        // Merge `t = a * b; require_eq(t, target)` into `a * b = target` — but never
        // when `target` is a witness-only var: it already has a witness-gen op, so
        // rewriting a constraint to output it would doubly-define it (the value
        // from its own witness-gen vs. from `a·b`). Fall through to a clean equality.
        if let Some(v) = self.as_pending_var(&lhs)
            && !self.is_witness_only_lc(&rhs) {
                self.merge_mul(v, rhs);
                return;
            }
        if let Some(v) = self.as_pending_var(&rhs)
            && !self.is_witness_only_lc(&lhs) {
                self.merge_mul(v, lhs);
                return;
            }

        let diff = lhs - rhs;
        let id = self.fresh_constraint_id();
        let note = format!("({}) * 1 = 0", self.render_lc(&diff));
        self.push_constraint(
            ConstraintKind::Equality,
            R1csConstraint::equal(id, diff, LinearCombination::zero(), &note),
        );
    }

    /// Emit an `n`-bit range proof over a (possibly compound) linear combination:
    /// decompose `value` into `n` boolean bits and pin their recomposition to
    /// `value` (⇒ `value < 2^n`).
    fn emit_range_proof_lc(&mut self, value: LinearCombination, n: usize) {
        let two = xark_ir::FieldConst::from_i64(2);
        let mut pow = xark_ir::FieldConst::from_i64(1);
        let mut recomp = LinearCombination::zero();
        // Allocate all `n` bit variables up front (a contiguous block), then emit
        // a single batched `Bits` witness-gen op: the shared `input` LC is stored
        // once instead of re-serialized per bit. The R1CS is unchanged — the same
        // booleanity + recomposition constraints, in the same order, over the same
        // var ids — so only `circuit.json`'s hint program shrinks.
        let bit_vars: Vec<u32> = (0..n).map(|_| self.alloc_advice()).collect();
        self.witness_gen.push(Some(WitnessGen::Bits {
            outs: bit_vars.clone(),
            input: value.clone(),
        }));
        for &b in &bit_vars {
            // Booleanity: `b * b = b` (⟺ `b ∈ {0, 1}`).
            let id = self.fresh_constraint_id();
            let note = format!("{} in {{0,1}}", self.var_names[b as usize]);
            self.push_constraint(
                ConstraintKind::Booleanity,
                R1csConstraint::general(
                    id,
                    LinearCombination::var(b),
                    LinearCombination::var(b),
                    LinearCombination::var(b),
                    &note,
                ),
            );
            recomp = recomp + LinearCombination::var(b).scale(&pow);
            pow = pow.mul(&two);
        }
        // Recomposition pins the bits to `value` (⇒ `value < 2^n`).
        let id = self.fresh_constraint_id();
        let note = format!("{n}-bit range: recompose == <lc>");
        self.push_constraint(
            ConstraintKind::Equality,
            R1csConstraint::equal(id, recomp, value, &note),
        );
    }

    /// Equality-to-zero function: a `{0,1}` lc that is `1` iff `input == 0`.
    /// `out = 1 − input·inv` with `input·out == 0` (the inverse-or-zero hint
    /// yields `0` when `input == 0`). Backs `==` on `Field`.
    fn emit_is_zero(&mut self, input: LinearCombination) -> LinearCombination {
        let inv = self.alloc_advice();
        self.witness_gen.push(Some(WitnessGen::InverseOrZero {
            out: inv,
            input: input.clone(),
        }));
        let prod = self.emit_mul(input.clone(), LinearCombination::var(inv));
        let out = LinearCombination::one() - prod;
        let input_out = self.emit_mul(input, out.clone());
        self.emit_require_eq(input_out, LinearCombination::zero());
        out
    }

    /// Unsigned `a < b` for `a, b ∈ [0, 2^n)`: a `{0,1}` lc. Borrow trick:
    /// `top = bitₙ(a − b + 2ⁿ)`, `lt = 1 − top`, range-prove
    /// `r = a − b + lt·2ⁿ ∈ [0, 2ⁿ)` (which pins `lt`). Needs `n ≤ 252`.
    fn emit_less_than(
        &mut self,
        n: usize,
        a: LinearCombination,
        b: LinearCombination,
    ) -> CompileResult<LinearCombination> {
        if n > 252 {
            return Err(CompileError::new(
                "comparison requires N ≤ 252 so 2^(N+1) ≤ BN254 field order",
            )
            .with_help("use a narrower fixed width; `2^(N+1)` must stay below the field order"));
        }
        let two_pow_n = pow2_lc(n);
        let diff_plus = a.clone() - b.clone() + two_pow_n.clone();
        let top = self.alloc_advice();
        self.witness_gen.push(Some(WitnessGen::Bit {
            out: top,
            input: diff_plus,
            index: n as u32,
        }));
        // Booleanity: `top * top == top` (⟺ `top ∈ {0, 1}`). Attributed to the
        // comparison (its structural borrow bit), not a bare booleanity.
        let id = self.fresh_constraint_id();
        let note = format!(
            "{} = cmp borrow bit ∈ {{0,1}}",
            self.var_names[top as usize]
        );
        self.kind_stack.push(ConstraintKind::Comparison);
        self.push_constraint(
            ConstraintKind::Comparison,
            R1csConstraint::general(
                id,
                LinearCombination::var(top),
                LinearCombination::var(top),
                LinearCombination::var(top),
                &note,
            ),
        );
        let lt = LinearCombination::one() - LinearCombination::var(top);
        // `r = a − b + lt·2ⁿ`; range-proving `r ∈ [0, 2ⁿ)` pins `lt`. The `lt·2ⁿ`
        // product is part of the comparison; the range proof is a RangeCheck.
        let lt_pow = self.emit_mul(lt.clone(), two_pow_n);
        self.kind_stack.pop();
        let r = (a.clone() - b.clone()) + lt_pow;
        self.kind_stack.push(ConstraintKind::RangeCheck);
        self.emit_range_proof_lc(r, n);
        self.kind_stack.pop();
        Ok(lt)
    }

    fn merge_mul(&mut self, var: VarId, target: LinearCombination) {
        let (idx, wg_idx) = self
            .pending_mul
            .remove(&var)
            .expect("caller guarantees var is pending");
        // record operands so the product can be revived if referenced again (see `merged`)
        self.merged.insert(
            var,
            (
                self.constraints[idx].a.clone(),
                self.constraints[idx].b.clone(),
                wg_idx,
                idx,
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
        // `require_bool(b)` folds `b*b=t; require(t==b)` → `b*b=b` here (an in-place
        // rewrite, so `push_constraint` never sees the final form): harvest it.
        if let Some(v) = booleanity_var(&self.constraints[idx]) {
            self.boolean_vars.insert(v);
        }
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
    /// Per-constraint profiling attribution, index-aligned with
    /// `r1cs.constraints`. Empty unless profiling was requested (`--profile`).
    /// Emitted to a **separate** `profile.json`; never mixed into the R1CS.
    pub profile: Vec<ConstraintProfile>,
    /// When `XARK_FUNCTION_ARTIFACT` is set and the circuit has function calls, the
    /// complete DAG-compact `VERSION_FUNCTION` container (see [`build_function_blob`]).
    /// The writer uses this as `circuit.xbc` verbatim instead of `roll_loops`.
    pub function_xbc: Option<Vec<u8>>,
    /// Vars allocated inside a `witness_only` region — exempt from `check_pinning`
    /// (pure witness-gen scratch feeding a downstream, separately-pinned result).
    pub witness_only_vars: BTreeSet<VarId>,
}

/// Flatten a circuit parameter type into its `Field` leaves, pairing each with
/// the MIR projection path (encoded exactly as [`LoweringEnv::resolve_place`]:
/// array/const index, or struct-field index) and a human-readable name. A
/// scalar `Field` is one leaf at path `[]`; an array/tuple/struct of `Field`
/// collapses to `n` leaves. Any other leaf is rejected.
fn flatten_field_leaves<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    path: &mut Vec<u64>,
    name: &str,
    out: &mut Vec<(Vec<u64>, String)>,
) -> CompileResult<()> {
    // `Field` is the opaque leaf — never recurse into its private limbs.
    if let Some(d) = ty.ty_adt_def()
        && tcx.item_name(d.did()).as_str() == "Field" {
            out.push((path.clone(), name.to_string()));
            return Ok(());
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
        _ => Err(
            CompileError::new(format!("unsupported circuit input type `{ty}`")).with_help(
                "a circuit input must satisfy the `CircuitInput` contract — be convertible to \
                 `[Field; N]` as a zero-cost move, i.e. a `Field` or an array/tuple/struct of \
                 `Field`. `#[derive(CircuitInput)]` implements it for a Field-composed struct.",
            ),
        ),
    }
}

/// Lower the `circuit` body into both the R1CS and the primitive IR.
pub fn lower<'tcx>(
    tcx: TyCtxt<'tcx>,
    entry: &EntryInfo,
    body: &Body<'tcx>,
    field: FieldSpec,
    registry: CallRegistry,
    profile_enabled: bool,
) -> CompileResult<LowerOutput> {
    // Cache-all pre-pass. Pass 1 templates every function (`promotions == None`) to
    // capture each distinct body once and tally per-key call counts. Pass 2 then
    // reuses those templates and REPLAYS every function called `>= 2` times as a
    // SYMBOLIC `CALL` (substituting the caller's arg LCs into the cached body — no
    // plug materialization, so no `plug = arg` equality rows), while functions called
    // once inline (fold) so their `mul→require_eq` merges and debug notes survive.
    let (mut measure, _) = run_pass(
        tcx,
        entry,
        body,
        registry.clone(),
        profile_enabled,
        None,
        BTreeMap::new(),
    )?;
    let promotions: BTreeMap<String, bool> = measure
        .function_call_counts
        .iter()
        .map(|(k, &c)| (k.clone(), c >= 2))
        .collect();
    // Hand pass 1's captured templates to pass 2 so cached calls replay from their
    // first occurrence.
    let templates = std::mem::take(&mut measure.function_templates);
    drop(measure);

    let (env, num_inputs) = run_pass(
        tcx,
        entry,
        body,
        registry,
        profile_enabled,
        Some(promotions),
        templates,
    )?;
    let program = finish(env, field, num_inputs);
    // reject any hint/advice output or public input left unpinned (see `check_pinning`)
    check_pinning(&program, num_inputs)?;
    Ok(program)
}

/// One lowering pass: bind the circuit inputs, walk the body, return the env and
/// input count. `promotions` selects function-fold behavior (see [`lower`] and
/// [`LoweringEnv::promotions`]). Called once normally, or twice under the fold
/// pre-pass (measure with `None`, then build with `Some`).
fn run_pass<'tcx>(
    tcx: TyCtxt<'tcx>,
    entry: &EntryInfo,
    body: &Body<'tcx>,
    registry: CallRegistry,
    profile_enabled: bool,
    promotions: Option<BTreeMap<String, bool>>,
    templates: BTreeMap<String, FunctionTemplate>,
) -> CompileResult<(LoweringEnv<'tcx>, usize)> {
    let mut env = LoweringEnv::new(tcx, registry, profile_enabled);
    env.promotions = promotions;
    // Pre-load templates captured by an earlier pass so every cached call replays
    // from its first occurrence (no first-call special-case): pass 2 gets pass 1's
    // templates, so a promoted function is a symbolic `CALL` even the first time.
    env.function_templates = templates;

    // Frame 0: circuit inputs become variables `0..num_inputs`, bound to params
    // `_1.._n`. Each parameter's type is flattened into its `Field` leaves — a
    // scalar `Field` is one input var; an array/tuple/struct of `Field` collapses
    // to `n` vars, each bound to the leaf's projection path so body reads resolve.
    let mut num_inputs = 0usize;
    for (i, input) in entry.inputs.iter().enumerate() {
        let local = rustc_middle::mir::Local::from_usize(i + 1);
        let ty = body.local_decls[local].ty;
        let mut leaves = Vec::new();
        let mut path = Vec::new();
        flatten_field_leaves(tcx, ty, &mut path, &input.name, &mut leaves)?;
        for (leaf_path, leaf_name) in leaves {
            let id = env.alloc_var(leaf_name, input.visibility.clone());
            env.set_field_at(local, &leaf_path, LinearCombination::var(id));
            num_inputs += 1;
        }
    }

    walk_body(&mut env, body)?;
    Ok((env, num_inputs))
}

/// Build-time structural soundness gate: reject a hint/advice output or a public
/// input that no constraint references (a free witness / unconstrained public
/// value). A necessary structural check, not a full under-constraint proof (see
/// `solver::analyze_underconstrained`).
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
        // Witness-only scratch: intentionally unpinned. Safe to exempt — a var in
        // zero constraints cannot affect proof validity (its only use is in the
        // witness-gen program that computes a downstream, pinned result).
        if out.witness_only_vars.contains(&v.id) {
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
                    "bind every public input/output with an `require_eq` (or remove it \
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
                    "constrain every hint output, e.g. `require_eq(x * hint_inverse(x), 1)`",
                ));
            }
            _ => {}
        }
    }
    Ok(())
}

/// Apply Rust `as`-cast truncation of a compile-time integer to `ty`: keep the
/// low `bits`, sign-extend for a signed target. Non-integer target passes through.
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
    // sign-extend a negative value in a signed target
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

/// The fallback error for a `SwitchInt` on a witness discriminant that cannot
/// be lowered to a branchless mux (e.g. more than 2 targets, or a non-bool
/// discriminant).
fn fallback_witness_control_flow_error(term_span: rustc_span::Span) -> CompileError {
    CompileError::new("witness-dependent control flow is not supported")
        .with_note("branch conditions must be compile-time constants (e.g. loop bounds)")
        .with_help(
            "for a data-dependent choice, require a boolean and \
             mux with `Field::from(cond) * a + Field::from(!cond) * b`; \
             loops must have constant bounds",
        )
        .or_span(term_span)
}

/// One `if`-arm's join block plus the field values it assigned (keyed by
/// `(local, projection path)`), used to mux converging arms.
type ArmAssignments = (
    rustc_middle::mir::BasicBlock,
    BTreeMap<(rustc_middle::mir::Local, SlotPath), LinearCombination>,
);

/// Walk one unconditional basic-block arm of an `if cond { a } else { b }` and
/// collect every `_dest = place` assignment. The arm must be pure: no
/// constraints, no witness-gen, no calls — only value copies and aggregates.
/// Returns the join-block (the `Goto` target) and the per-`(dest_local, dest_path)`
/// lc mapping.
fn collect_arm_assignments<'tcx>(
    env: &mut LoweringEnv<'tcx>,
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
) -> CompileResult<ArmAssignments> {
    // Snapshot field state before processing any arm blocks.
    let saved_fields = env.frame_mut().field.clone();
    let n_constraints_before = env.constraints.len();
    let n_witness_before = env.witness_gen.len();

    // Walk through one or more basic blocks, following `Assert` terminators
    // (bounds checks on compile-time indices) until we reach the real `Goto`.
    let mut cur_bb = bb;
    let join_bb;
    loop {
        let data = &body.basic_blocks[cur_bb];

        // Validate + lower this block's statements.
        for stmt in &data.statements {
            match &stmt.kind {
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop => {}
                StatementKind::Assign(boxed) => {
                    let (_, rvalue) = &**boxed;
                    match rvalue {
                        Rvalue::Use(_, _) => {}
                        Rvalue::Ref(
                            _,
                            rustc_middle::mir::BorrowKind::Shared
                            | rustc_middle::mir::BorrowKind::Fake(_),
                            _,
                        ) => {}
                        Rvalue::CopyForDeref(_) => {}
                        Rvalue::Repeat(..) => {}
                        Rvalue::BinaryOp(..) | Rvalue::UnaryOp(..) => {}
                        Rvalue::Aggregate(kind, _) => {
                            let ok = match &**kind {
                                rustc_middle::mir::AggregateKind::Array(_)
                                | rustc_middle::mir::AggregateKind::Tuple => true,
                                rustc_middle::mir::AggregateKind::Adt(did, ..) => {
                                    env.tcx.adt_def(*did).is_struct()
                                }
                                _ => false,
                            };
                            if !ok {
                                return Err(CompileError::new(
                                    "unsupported aggregate in conditional arm",
                                )
                                .with_help(
                                    "only tuples, arrays, and plain structs are supported",
                                ));
                            }
                        }
                        _ => {
                            return Err(CompileError::new(format!(
                                "{} inside a conditional arm is not supported",
                                rvalue_name(rvalue)
                            ))
                            .with_help(
                                "only plain value copies and tuple/struct aggregates are allowed; \
                                 move arithmetic and calls before the `if`",
                            ));
                        }
                    }
                }
                _ => {
                    return Err(
                        CompileError::new("unsupported statement in conditional arm")
                            .with_help("no calls, no control flow"),
                    );
                }
            }
        }

        // Process the terminator.
        let term = data.terminator();
        match &term.kind {
            TerminatorKind::Goto { target } => {
                join_bb = *target;
                break;
            }
            // Bounds checks on compile-time indices — always succeed, skip.
            TerminatorKind::Assert { target, .. } => {
                cur_bb = *target;
            }
            other => {
                return Err(CompileError::new(format!(
                    "conditional arm ends with `{}` instead of `goto` — \
                     arms cannot contain calls, returns, or nested control flow",
                    terminator_name(other)
                ))
                .with_help(
                    "move function calls and assertions before the `if`; only \
                     plain value assignments are allowed in each arm",
                ));
            }
        }
    }

    // Now lower all traversed blocks (a second pass, but kept simple).
    let mut cur_bb = bb;
    loop {
        let data = &body.basic_blocks[cur_bb];
        for stmt in &data.statements {
            lower_statement(env, &stmt.kind).map_err(|e| {
                e.with_help("error inside a conditional arm — ensure only value copies are used")
            })?;
        }
        let term = data.terminator();
        match &term.kind {
            TerminatorKind::Goto { .. } => break,
            TerminatorKind::Assert { target, .. } => cur_bb = *target,
            _ => unreachable!("already validated"),
        }
    }

    // Arms must be pure — no constraints or witness entries emitted.
    if env.constraints.len() != n_constraints_before || env.witness_gen.len() != n_witness_before {
        env.frame_mut().field = saved_fields;
        return Err(
            CompileError::new("conditional arm must not emit constraints or hints").with_help(
                "only value assignments are allowed in `if`/`else` arms; \
             move arithmetic and calls before the `if`",
            ),
        );
    }

    // Collect the field slots that were added or changed by this arm.
    let mut map = BTreeMap::new();
    for (local, slots) in env.frame().field.iter() {
        match saved_fields.get(local) {
            None => {
                for (path, lc) in slots {
                    map.insert((local, path.clone()), lc.clone());
                }
            }
            Some(old)
                if old.len() != slots.len()
                    || old.keys().collect::<BTreeSet<_>>()
                        != slots.keys().collect::<BTreeSet<_>>() =>
            {
                for (path, lc) in slots {
                    map.insert((local, path.clone()), lc.clone());
                }
            }
            _ => { /* unchanged */ }
        }
    }

    // Restore pre-arm state.
    env.frame_mut().field = saved_fields;
    Ok((join_bb, map))
}

/// Walk a body's CFG (from the start block) in the current frame, lowering each
/// statement and terminator. Loops with compile-time bounds are unrolled by
/// following back-edges; witness-dependent control flow is rejected.
fn walk_body<'tcx>(env: &mut LoweringEnv<'tcx>, body: &Body<'tcx>) -> CompileResult<()> {
    let mut bb = START_BLOCK;
    let mut steps = 0u64;
    loop {
        steps += 1;
        if steps > MAX_STEPS {
            return Err(
                CompileError::new("loop did not terminate within the unroll budget")
                    .with_note("only loops with compile-time-constant bounds can be unrolled"),
            );
        }
        let data = &body.basic_blocks[bb];

        for stmt in &data.statements {
            // Track the top-level (depth-0) circuit statement span as the profile
            // "user line" for any constraints it triggers — but never overwrite
            // it while inlining a function, so deep constraints still attribute to
            // the user's circuit line (see `LoweringEnv::root_span`).
            if env.inlining.is_empty() {
                env.root_span = Some(stmt.source_info.span);
            }
            // Any lowering error bubbling up gets this statement's span as a
            // fallback location; a deeper error's own span (if set) is kept.
            lower_statement(env, &stmt.kind).map_err(|e| e.or_span(stmt.source_info.span))?;
        }

        let terminator = data.terminator();
        let term_span = terminator.source_info.span;
        if env.inlining.is_empty() {
            env.root_span = Some(term_span);
        }
        match &terminator.kind {
            TerminatorKind::Return => break,
            TerminatorKind::Goto { target } => bb = *target,
            // Bounds/overflow checks: indices are compile-time constants (the
            // loop unroller guarantees this), so follow the success edge.
            TerminatorKind::Assert { target, .. } => bb = *target,
            // The by-value `array::IntoIter` of `for x in arr` is dropped after
            // the loop; the drop has no circuit effect, so follow its edge.
            TerminatorKind::Drop { target, .. } => bb = *target,
            // Compile-time-known branch (loop condition, match on constant), or
            // witness boolean `if` lowered to branchless muxes.
            TerminatorKind::SwitchInt { discr, targets } => {
                if let Some(v) = env.operand_to_int(discr) {
                    bb = targets
                        .iter()
                        .find(|(val, _)| *val == v as u128)
                        .map(|(_, t)| t)
                        .unwrap_or_else(|| targets.otherwise());
                } else {
                    // Try witness bool → branchless mux.
                    let targs: Vec<(u128, _)> = targets.iter().collect();
                    let (then_bb, else_bb) = if targs.len() == 2
                        && targs.iter().any(|(v, _)| *v == 0)
                        && targs.iter().any(|(v, _)| *v == 1)
                    {
                        // Both arms explicit: `[(0, else), (1, then)]`
                        let else_bb = targs
                            .iter()
                            .find(|(v, _)| *v == 0)
                            .map(|(_, bb)| *bb)
                            .unwrap();
                        let then_bb = targs
                            .iter()
                            .find(|(v, _)| *v == 1)
                            .map(|(_, bb)| *bb)
                            .unwrap();
                        (then_bb, else_bb)
                    } else if targs.len() == 1 {
                        let (val, bb) = targs[0];
                        if val == 0 {
                            // `[(0, else)]` + `otherwise → then`
                            (targets.otherwise(), bb)
                        } else if val == 1 {
                            // `[(1, then)]` + `otherwise → else`
                            (bb, targets.otherwise())
                        } else {
                            return Err(fallback_witness_control_flow_error(term_span));
                        }
                    } else {
                        return Err(fallback_witness_control_flow_error(term_span));
                    };
                    {
                        let cond_lc = env
                            .operand_to_lc(discr)
                            .map_err(|_| fallback_witness_control_flow_error(term_span))?;
                        let (then_join, then_map) = collect_arm_assignments(env, body, then_bb)?;
                        let (else_join, else_map) = collect_arm_assignments(env, body, else_bb)?;
                        if then_join != else_join {
                            return Err(CompileError::new(
                                "`if`/`else` arms must converge on the same join block",
                            )
                            .with_help(
                                "both arms must end at the same point; \
                                 consider extracting differing control flow",
                            ));
                        }
                        // Only mux locals assigned in both arms; a local only
                        // present in one arm is a dead intra-arm temp.
                        let common: BTreeSet<_> = then_map
                            .keys()
                            .filter(|k| else_map.contains_key(*k))
                            .cloned()
                            .collect();
                        if common.is_empty() {
                            return Err(CompileError::new("`if`/`else` arms share no assignments")
                                .with_help("both arms must assign the same bindings"));
                        }
                        for key in &common {
                            let then_lc = &then_map[key];
                            let else_lc = &else_map[key];
                            let diff = then_lc.clone() - else_lc.clone();
                            let mux = else_lc.clone() + env.emit_mul(cond_lc.clone(), diff);
                            env.set_field_at(key.0, &key.1, mux);
                        }
                        bb = then_join;
                    }
                }
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
                        .or_span(term_span));
                    }
                }
            }
            other => {
                let err = CompileError::new(format!(
                    "{} is not supported inside a circuit",
                    terminator_name(other)
                ));
                let err = match other {
                    TerminatorKind::SwitchInt { .. } => err.with_help(
                        "a circuit can't branch on a witness value — use a branchless \
                         select, e.g. `if_false + Field::from(cond) * (if_true - if_false)`, \
                         or make the condition a compile-time constant",
                    ),
                    TerminatorKind::Assert { .. } => err.with_help(
                        "native `assert!` / `assert_eq!` don't constrain the circuit — call \
                         `require_eq(a, b)` (the circuit primitive) to emit an equality constraint",
                    ),
                    _ => err,
                };
                return Err(err.or_span(term_span));
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
                // `_b = &(*_a)` reborrow: supported to carry a `&str` literal into
                // `Field::constant`, or a *shared* borrow of a `Field`-bearing
                // value (transparent in the value model). A `&mut` borrow of a
                // `Field` is still rejected (rejects `+=`/`-=` write-back), except
                // the `&mut iter` reborrow of a `for`-loop iterator.
                Rvalue::Ref(_, kind, src) => lower_ref(
                    env,
                    dest,
                    src,
                    matches!(
                        kind,
                        rustc_middle::mir::BorrowKind::Shared
                            | rustc_middle::mir::BorrowKind::Fake(_)
                    ),
                ),
                // `CopyForDeref` is always a read (a projection copy), so it is
                // transparent like a shared borrow.
                Rvalue::CopyForDeref(src) => lower_ref(env, dest, src, true),
                // Array literal `[a, b, c]`: store each element in its slot.
                // Elements may themselves be arrays (nested arrays like
                // `[[Field; 32]; 8]`), copied slot-by-slot.
                Rvalue::Aggregate(kind, operands) => {
                    // `for i in a..b`: the exclusive `Range { start, end }` literal.
                    // Model it as a compile-time range-iterator on `dest` (bounds
                    // must be constants) rather than a struct of int fields.
                    if let rustc_middle::mir::AggregateKind::Adt(did, ..) = &**kind
                        && env.registry.is_exclusive_range_ty(*did) {
                            let mut it = operands.iter();
                            let start = range_bound(env, it.next().expect("Range.start"))?;
                            let end = range_bound(env, it.next().expect("Range.end"))?;
                            env.set_range_state(
                                dest,
                                RangeState {
                                    cur: start,
                                    end,
                                    inclusive: false,
                                    exhausted: false,
                                },
                            );
                            return Ok(());
                        }
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
                // Integer arithmetic/comparison (loop counters, bounds checks), and
                // boolean-wire ops on `{0,1}` comparison results.
                Rvalue::BinaryOp(op, operands) => {
                    if let (Some(a), Some(b)) = (
                        env.operand_to_int(&operands.0),
                        env.operand_to_int(&operands.1),
                    ) {
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
                        return Ok(());
                    }
                    // Otherwise these are boolean ops on `{0,1}` wires (the
                    // results of circuit comparisons).
                    use rustc_middle::mir::BinOp::*;
                    match op {
                        BitAnd => {
                            let a = env.operand_to_lc(&operands.0)?;
                            let b = env.operand_to_lc(&operands.1)?;
                            env.consume_pending(&a);
                            env.consume_pending(&b);
                            let out = env.emit_mul(a, b);
                            env.set_field(dest, out);
                        }
                        BitOr => {
                            let a = env.operand_to_lc(&operands.0)?;
                            let b = env.operand_to_lc(&operands.1)?;
                            let out = env.emit_or(a, b);
                            env.set_field(dest, out);
                        }
                        BitXor => {
                            let a = env.operand_to_lc(&operands.0)?;
                            let b = env.operand_to_lc(&operands.1)?;
                            let out = env.emit_xor(a, b);
                            env.set_field(dest, out);
                        }
                        Eq => {
                            let a = env.operand_to_lc(&operands.0)?;
                            let b = env.operand_to_lc(&operands.1)?;
                            let out = env.emit_is_zero(a - b);
                            env.set_field(dest, out);
                        }
                        Ne => {
                            let a = env.operand_to_lc(&operands.0)?;
                            let b = env.operand_to_lc(&operands.1)?;
                            let out = env.emit_xor(a, b);
                            env.set_field(dest, out);
                        }
                        _ => {
                            return Err(CompileError::new(format!(
                                "the `{}` operator on witness values is not a circuit operation",
                                binop_symbol(*op)
                            ))
                            .with_help(
                                "bitwise (`& | ^`) and equality (`== !=`) ops on `bool` wires are \
                                 supported; other operators need field arithmetic or a comparison \
                                 function",
                            ))
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
                        return Ok(());
                    }
                    // Boolean NOT on a `{0,1}` wire: `1 − x`.
                    if matches!(op, rustc_middle::mir::UnOp::Not) {
                        let x = env.operand_to_lc(operand)?;
                        env.set_field(dest, LinearCombination::one() - x);
                        return Ok(());
                    }
                    Err(CompileError::new(format!(
                        "the `{}` operator on a witness value is not a circuit operation",
                        unop_symbol(*op)
                    )))
                }
                // `discriminant(_opt)` on a modeled `Option` from a range `next`:
                // yield its constant discriminant (0 = None, 1 = Some) so the
                // following `switchInt` resolves at compile time.
                Rvalue::Discriminant(place) => {
                    let (local, _) = env.resolve_place(place)?;
                    let disc = env.get_opt_disc(local).ok_or_else(|| {
                        CompileError::new("`discriminant` of a value the circuit can't model")
                            .with_note(
                                "only the `Option` produced by iterating a constant integer range \
                                 is supported; matching on other enums is not a circuit operation",
                            )
                    })?;
                    env.set_int_at(dest, &dest_path, disc);
                    Ok(())
                }
                // Compile-time integer cast (`From<uN> for Field`, or a narrowing
                // `as uN`). Truncate to the target width per Rust `as` semantics.
                Rvalue::Cast(_, operand, ty) => {
                    if let Some(v) = env.operand_to_int(operand) {
                        env.set_int_at(dest, &dest_path, truncate_int_cast(v, *ty));
                    }
                    Ok(())
                }
                other => Err(CompileError::new(format!(
                    "{} is not supported inside a circuit",
                    rvalue_name(other)
                ))
                .with_help(
                    "a circuit supports field arithmetic (`+` `-` `*` `/`, `.pow(n)`), comparisons, \
                     and the provided gadget calls; references, closures, casts, and heap ops \
                     are not lowerable",
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

/// Bind `dest[dest_path] = <use of operand>` for a field value, an array, or an
/// integer/string constant.
fn bind_use<'tcx>(
    env: &mut LoweringEnv<'tcx>,
    dest: rustc_middle::mir::Local,
    dest_path: &[u64],
    operand: &Operand<'tcx>,
) -> CompileResult<()> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            let (src, src_path) = env.resolve_place(place)?;
            // Carry an iterator through `let iter = <into_iter result>`
            // (`_6 = move _4`) — for both a range and a fixed-size array.
            if src_path.is_empty() && dest_path.is_empty() {
                if let Some(st) = env.take_range_state(src) {
                    env.set_range_state(dest, st);
                    return Ok(());
                }
                if let Some(st) = env.take_array_iter(src) {
                    env.set_array_iter(dest, st);
                    return Ok(());
                }
            }
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
                } else if src_path.is_empty() && dest_path.is_empty()
                    && let Some(s) = env.get_str(src) {
                        env.set_str(dest, s);
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
                } else if let Some(v) = env.const_ref_int_to_u128(c) {
                    // a promoted `&uN` (e.g. the `&100u32` a `Field`-vs-const
                    // comparison desugars into): carry the referenced integer.
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

/// Lower `dest = &src` / `dest = &(*src)`.
///
/// - A `&mut iter` reborrow of a `for`-loop iterator records an alias so a later
///   `next(move r)` finds the base state.
/// - A *shared* borrow of a `Field`-bearing value is transparent: copy the
///   referent's field slots to `dest`, so `*dest` (or `into_iter(&arr)`) reads
///   them back. `shared` is false for `&mut` borrows — copying those would
///   silently drop the write-back (e.g. `acc += b`), so they stay rejected.
/// - The `&str` reborrow chain of `Field::constant("...")` is carried through.
fn lower_ref<'tcx>(
    env: &mut LoweringEnv<'tcx>,
    dest: rustc_middle::mir::Local,
    src: &Place<'tcx>,
    shared: bool,
) -> CompileResult<()> {
    if let Some(base) = env.iter_base_of_place(src) {
        env.set_ref_alias(dest, base);
        return Ok(());
    }
    if shared {
        let (sl, spath) = env.resolve_place(src)?;
        let slots = env.collect_field_slots(sl, &spath);
        if !slots.is_empty() {
            for (rel, lc) in slots {
                env.set_field_at(dest, &rel, lc);
            }
            return Ok(());
        }
        // A shared borrow of a tracked integer (e.g. the `&(*_7)` reborrow of a
        // promoted `&uN` in a `Field`-vs-const comparison) carries the integer
        // through transparently, so a later `*r` reads it back.
        if let Some(v) = env.get_int_at(sl, &spath) {
            env.set_int(dest, v);
            return Ok(());
        }
    }
    if let Some(s) = env.get_str(src.local) {
        env.set_str(dest, s);
        return Ok(());
    }
    Err(
        CompileError::new("a mutable borrow of a `Field` value is not supported inside a circuit")
            .with_note(
                "comparisons (`==` `!=` `<` `<=` `>` `>=`) are circuit operations that return a \
         `bool` wire; compound assignments (`+=` `-=` `*=` `/=`) are not — write \
         `a = a + b` instead of `a += b`",
            ),
    )
}

/// `2^n` as a `Field` constant linear combination (zero constraints).
fn pow2_lc(n: usize) -> LinearCombination {
    let mut p = xark_ir::FieldConst::from_i64(1);
    let two = xark_ir::FieldConst::from_i64(2);
    let mut i = 0;
    while i < n {
        p = p.mul(&two);
        i += 1;
    }
    LinearCombination::constant(p.decimal().clone())
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
    let orig_def_id = def_id;
    let (def_id, call_args) = match resolve_call_instance(env.tcx, def_id, generic_args) {
        Some(inst) => (inst.def_id(), inst.args),
        None => (def_id, generic_args),
    };

    let dest = LoweringEnv::place_local(destination)?;

    // A recognized intrinsic is lowered directly; any other ordinary function
    // with available MIR is inlined; anything else is rejected. Recognition keys
    // on the *pre-resolution* `DefId` (see `CallRegistry::classify`); inlining
    // uses the resolved id + args.
    let known = match env.registry.classify(orig_def_id) {
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
            env.set_field(dest, lhs + rhs);
        }
        KnownCall::Sub => {
            let lhs = env.operand_to_lc(arg(0)?)?;
            let rhs = env.operand_to_lc(arg(1)?)?;
            env.consume_pending(&lhs);
            env.consume_pending(&rhs);
            env.set_field(dest, lhs - rhs);
        }
        KnownCall::Neg => {
            let x = env.operand_to_lc(arg(0)?)?;
            env.consume_pending(&x);
            env.set_field(dest, -x);
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
                let bad = t
                    .char_indices()
                    .find(|&(i, c)| !(c.is_ascii_digit() || (i == 0 && (c == '-' || c == '+'))));
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
            env.set_field(dest, LinearCombination::constant(field_const.decimal()));
        }
        KnownCall::ConstrainEq => {
            let lhs = env.operand_to_lc(arg(0)?)?;
            let rhs = env.operand_to_lc(arg(1)?)?;
            env.emit_require_eq(lhs, rhs);
        }
        // Open/close a witness-only region (both return `()`, so no `dest`).
        KnownCall::WitnessBegin => {
            env.witness_only = true;
        }
        KnownCall::WitnessEnd => {
            env.witness_only = false;
        }
        KnownCall::Advice => {
            // A fresh prover-supplied private witness variable with no hint. The
            // function author constrains it (but the emitted witness-gen program
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
        // Comparison intrinsics returning a `bool` (`{0,1}` wire). Back the
        // `PartialEq`/`PartialOrd` impls on `Field`; the width `N` for `ULt`
        // comes from the call's const generic arg.
        KnownCall::Eq => {
            let a = env.operand_to_lc(arg(0)?)?;
            let b = env.operand_to_lc(arg(1)?)?;
            let out = env.emit_is_zero(a - b);
            env.set_field(dest, out);
        }
        KnownCall::ULt => {
            let n = call_args
                .const_at(0)
                .try_to_target_usize(env.tcx)
                .ok_or_else(|| CompileError::new("comparison width `N` must be a constant"))?
                as usize;
            let a = env.operand_to_lc(arg(0)?)?;
            let b = env.operand_to_lc(arg(1)?)?;
            let out = env.emit_less_than(n, a, b)?;
            env.set_field(dest, out);
        }
        KnownCall::BoolToField => {
            // identity: a `bool` and a `{0,1}` `Field` wire are the same variable
            let x = env.operand_to_lc(arg(0)?)?;
            env.set_field(dest, x);
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
        // `RangeInclusive::new(a, b)` → the inclusive range-iterator state.
        KnownCall::RangeInclusiveNew => {
            let start = range_bound(env, arg(0)?)?;
            let end = range_bound(env, arg(1)?)?;
            env.set_range_state(
                dest,
                RangeState {
                    cur: start,
                    end,
                    inclusive: true,
                    exhausted: false,
                },
            );
        }
        // `into_iter` is the identity for both a `Range` and a fixed-size array.
        // Carry the range state, or capture the array's element slots as an array
        // iterator. A non-range/array argument (e.g. `for x in v.iter()`, a slice
        // iterator we can't const-model) has neither → reject with a clear error.
        KnownCall::IntoIter => {
            let src = match arg(0)? {
                Operand::Copy(p) | Operand::Move(p) => LoweringEnv::place_local(p)?,
                _ => return Err(unsupported_iterator()),
            };
            if let Some(st) = env.take_range_state(src) {
                env.set_range_state(dest, st);
            } else {
                // Fixed-size array (`for x in arr` / `for x in &arr`, whose `&arr`
                // copied the slots here transparently). Group the flat field slots
                // by element index into per-element slot lists.
                let slots = env.collect_field_slots(src, &[]);
                if slots.is_empty() {
                    return Err(unsupported_iterator());
                }
                let mut groups: BTreeMap<u64, Vec<(Vec<u64>, LinearCombination)>> = BTreeMap::new();
                for (path, lc) in slots {
                    let Some((first, rest)) = path.split_first() else {
                        // A scalar (empty path) isn't iterable.
                        return Err(unsupported_iterator());
                    };
                    groups.entry(*first).or_default().push((rest.to_vec(), lc));
                }
                let elems: Vec<_> = groups.into_values().collect();
                env.set_array_iter(dest, ArrayIterState { elems, cursor: 0 });
            }
        }
        // `<_ as Iterator>::next(&mut iter)` — model one step: advance the
        // compile-time cursor and produce a modeled `Option` (`Some(v)`/`None`) so
        // the following `discriminant`/`switchInt` fold to constants. `Some`'s
        // payload lives in the option local's slot `[0]` (an int for a range, the
        // element's field slots for an array), read back via `(_opt as Some).0`.
        KnownCall::IterNext => {
            let base = env
                .iter_base_of_place(match arg(0)? {
                    Operand::Copy(p) | Operand::Move(p) => p,
                    _ => return Err(unsupported_iterator()),
                })
                .ok_or_else(unsupported_iterator)?;
            if let Some(mut st) = env.take_range_state(base) {
                let yields = if st.exhausted {
                    false
                } else if st.inclusive {
                    st.cur <= st.end
                } else {
                    st.cur < st.end
                };
                if yields {
                    env.set_opt_disc(dest, 1);
                    env.set_int_at(dest, &[0], st.cur);
                    // For an inclusive range, yielding `end` exhausts it (rather
                    // than overflowing past `end`).
                    if st.inclusive && st.cur == st.end {
                        st.exhausted = true;
                    } else {
                        st.cur += 1;
                    }
                } else {
                    env.set_opt_disc(dest, 0);
                }
                env.set_range_state(base, st);
            } else {
                let mut st = env.take_array_iter(base).expect("iter_base implies state");
                if st.cursor < st.elems.len() {
                    env.set_opt_disc(dest, 1);
                    // Store the element's slots under the `Some` payload path `[0]`.
                    let elem = st.elems[st.cursor].clone();
                    for (rel, lc) in elem {
                        let mut p = vec![0u64];
                        p.extend(rel);
                        env.set_field_at(dest, &p, lc);
                    }
                    st.cursor += 1;
                } else {
                    env.set_opt_disc(dest, 0);
                }
                env.set_array_iter(base, st);
            }
        }
    }
    Ok(())
}

/// A user-declared **frontend function**, captured once: the constraints and
/// witness-gen ops one inline of a monomorphization emits, with vars addressed
/// relative to the call (`Slot`). A later call to the same function is *replayed* —
/// a bytecode `CALL` — instead of re-walked: internal vars shift by the call's
/// var base, plug vars (the materialized single-var inputs) map positionally to
/// the new call's plugs.
struct FunctionTemplate {
    /// First-call constraints (notes stripped) — replayed with vars remapped.
    constraints: Vec<R1csConstraint>,
    /// First-call witness-gen ops — replayed with vars remapped.
    witness: Vec<WitnessGen>,
    /// First call's var base and its plug vars (the materialized single-var
    /// inputs). On replay, `plug_vars[i]` → the new call's `plugs[i]`, and every
    /// internal (`>= base_var`) shifts to the new base.
    base_var: VarId,
    plug_vars: Vec<VarId>,
    /// The kind of each var the body allocated, in allocation order (internal vs
    /// advice interleave as the body runs — replay must reproduce that order so
    /// var ids, visibilities, and `t{}`/`w{}` names all match the walk).
    var_kinds: Vec<Visibility>,
    /// The return, as `(leaf path, first-call output LC)` — substituted on replay.
    /// Kept as a linear combination (not materialized to a fresh word var) so an
    /// output that is a bit-sum `Σ 2ⁱ·rᵢ` reaches the caller as that sum, letting
    /// the caller's `to_bits` bit-sum shortcut fire (no redundant decomposition).
    /// A single-var output is just the LC `1·v`.
    outputs: Vec<(Vec<u64>, LinearCombination)>,
}

/// Apply `f` to every `VarId` a witness-gen op reads or writes.
fn remap_witness_vars(w: &mut WitnessGen, f: &dyn Fn(VarId) -> VarId) {
    let lc = |l: &mut LinearCombination, f: &dyn Fn(VarId) -> VarId| {
        for t in &mut l.terms {
            t.var = f(t.var);
        }
    };
    let lcs = |v: &mut [LinearCombination], f: &dyn Fn(VarId) -> VarId| {
        for l in v {
            lc(l, f);
        }
    };
    let ids = |v: &mut [VarId], f: &dyn Fn(VarId) -> VarId| {
        for x in v {
            *x = f(*x);
        }
    };
    match w {
        WitnessGen::Product { out, left, right } => {
            *out = f(*out);
            lc(left, f);
            lc(right, f);
        }
        WitnessGen::Linear { out, lc: l } => {
            *out = f(*out);
            lc(l, f);
        }
        WitnessGen::Xor { out, a, b } | WitnessGen::Or { out, a, b } => {
            *out = f(*out);
            lc(a, f);
            lc(b, f);
        }
        WitnessGen::Inverse { out, input } | WitnessGen::InverseOrZero { out, input } => {
            *out = f(*out);
            lc(input, f);
        }
        WitnessGen::Bit { out, input, .. } => {
            *out = f(*out);
            lc(input, f);
        }
        WitnessGen::Bits { outs, input } => {
            ids(outs, f);
            lc(input, f);
        }
        WitnessGen::DivRem { q, r, num, den } => {
            *q = f(*q);
            *r = f(*r);
            lc(num, f);
            lc(den, f);
        }
        WitnessGen::MulModDivMod {
            q,
            r,
            a,
            b,
            modulus,
            ..
        } => {
            ids(q, f);
            ids(r, f);
            lcs(a, f);
            lcs(b, f);
            lcs(modulus, f);
        }
        WitnessGen::ModInverse {
            out, a, modulus, ..
        } => {
            ids(out, f);
            lcs(a, f);
            lcs(modulus, f);
        }
        WitnessGen::Sub2 {
            qabs,
            r,
            a,
            b,
            c,
            modulus,
            ..
        } => {
            *qabs = f(*qabs);
            ids(r, f);
            lcs(a, f);
            lcs(b, f);
            lcs(c, f);
            lcs(modulus, f);
        }
    }
}

/// Like [`remap_witness_vars`], but *substitutes* linear combinations for the LC
/// input fields (plug vars → caller plug LCs) while var-remapping the `out`/id
/// fields (always fresh internals). `f` shifts internal out/id vars; `s`
/// substitutes an LC input. Used by symbolic function replay so witness ops read the
/// caller's argument LCs directly, with no plug materialization.
fn subst_witness_vars(
    w: &mut WitnessGen,
    f: &dyn Fn(VarId) -> VarId,
    s: &dyn Fn(&LinearCombination) -> LinearCombination,
) {
    let ids = |v: &mut [VarId]| {
        for x in v {
            *x = f(*x);
        }
    };
    let subst = |v: &mut [LinearCombination]| {
        for l in v {
            *l = s(l);
        }
    };
    match w {
        WitnessGen::Product { out, left, right } => {
            *out = f(*out);
            *left = s(left);
            *right = s(right);
        }
        WitnessGen::Linear { out, lc: l } => {
            *out = f(*out);
            *l = s(l);
        }
        WitnessGen::Xor { out, a, b } | WitnessGen::Or { out, a, b } => {
            *out = f(*out);
            *a = s(a);
            *b = s(b);
        }
        WitnessGen::Inverse { out, input } | WitnessGen::InverseOrZero { out, input } => {
            *out = f(*out);
            *input = s(input);
        }
        WitnessGen::Bit { out, input, .. } => {
            *out = f(*out);
            *input = s(input);
        }
        WitnessGen::Bits { outs, input } => {
            ids(outs);
            *input = s(input);
        }
        WitnessGen::DivRem { q, r, num, den } => {
            *q = f(*q);
            *r = f(*r);
            *num = s(num);
            *den = s(den);
        }
        WitnessGen::MulModDivMod {
            q,
            r,
            a,
            b,
            modulus,
            ..
        } => {
            ids(q);
            ids(r);
            subst(a);
            subst(b);
            subst(modulus);
        }
        WitnessGen::ModInverse {
            out, a, modulus, ..
        } => {
            ids(out);
            subst(a);
            subst(modulus);
        }
        WitnessGen::Sub2 {
            qabs,
            r,
            a,
            b,
            c,
            modulus,
            ..
        } => {
            *qabs = f(*qabs);
            ids(r);
            subst(a);
            subst(b);
            subst(c);
            subst(modulus);
        }
    }
}

/// Is a captured function body *pure* — does it reference only its plug vars and
/// its own freshly-allocated internals (`>= base`)? If it touches any earlier var
/// (a cached bit-decomposition, a cross-boundary mul-merge, …) it is not a
/// function of its inputs alone and can't be replayed correctly, so it must stay
/// walked. This is what makes auto-selected functions safe.
fn function_is_pure(
    constraints: &[R1csConstraint],
    witness: &[Option<WitnessGen>],
    base: VarId,
    plugs: &[VarId],
) -> bool {
    let plug_set: BTreeSet<VarId> = plugs.iter().copied().collect();
    let ok = |v: VarId| v >= base || plug_set.contains(&v);
    for c in constraints {
        for lc in [&c.a, &c.b, &c.c] {
            if lc.terms.iter().any(|t| !ok(t.var)) {
                return false;
            }
        }
    }
    for w in witness.iter().flatten() {
        let bad = std::cell::Cell::new(false);
        let mut wc = w.clone();
        remap_witness_vars(&mut wc, &|v| {
            if !ok(v) {
                bad.set(true);
            }
            v
        });
        if bad.get() {
            return false;
        }
    }
    true
}

/// Compact (DAG/function) codegen — capture reusable functions, replay them, and
/// write the DAG-compact `circuit.xbc`. This is the primary codegen: it is
/// R1CS-neutral (the artifact expands byte-identically, so vks/proofs are
/// unchanged) while cutting build time and artifact size.
fn compact_enabled() -> bool {
    true
}
fn call_memo_enabled() -> bool {
    compact_enabled()
}

// --- FUNCTION/CALL bytecode (constraint stream) --------------------------------
// A compact DAG encoding: each distinct function body stored once, calls as small
// records. Expansion (`expand_function_bytecode`) reproduces the flat constraint
// stream byte-for-byte. Same varint density as the flat `.xbc`, so file sizes are
// directly comparable.
fn put_uv(buf: &mut Vec<u8>, mut v: u64) {
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            buf.push(b);
            break;
        }
        buf.push(b | 0x80);
    }
}
fn put_iv(buf: &mut Vec<u8>, v: i64) {
    put_uv(buf, ((v << 1) ^ (v >> 63)) as u64); // zigzag
}
fn put_fc(buf: &mut Vec<u8>, fc: &xark_ir::FieldConst) {
    match fc.as_i64() {
        Some(v) => {
            buf.push(0);
            put_iv(buf, v);
        }
        None => {
            buf.push(1);
            let s = fc.decimal();
            put_uv(buf, s.len() as u64);
            buf.extend_from_slice(s.as_bytes());
        }
    }
}
fn put_lc_g(buf: &mut Vec<u8>, lc: &LinearCombination) {
    put_fc(buf, &lc.constant);
    put_uv(buf, lc.terms.len() as u64);
    for t in &lc.terms {
        put_fc(buf, &t.coeff);
        put_uv(buf, u64::from(t.var));
    }
}
fn put_row_g(buf: &mut Vec<u8>, c: &R1csConstraint) {
    put_lc_g(buf, &c.a);
    put_lc_g(buf, &c.b);
    put_lc_g(buf, &c.c);
}
fn put_ids_g(buf: &mut Vec<u8>, ids: &[VarId]) {
    put_uv(buf, ids.len() as u64);
    for &v in ids {
        put_uv(buf, u64::from(v));
    }
}
fn put_lcs_g(buf: &mut Vec<u8>, lcs: &[LinearCombination]) {
    put_uv(buf, lcs.len() as u64);
    for lc in lcs {
        put_lc_g(buf, lc);
    }
}
/// Serialize one `WitnessGen` op with the same local primitives the function
/// encoder uses for constraints (`put_fc`/`put_lc_g`/`put_uv`), so the compact
/// blob is self-contained and decodable by [`get_witness_g`].
fn put_witness_g(buf: &mut Vec<u8>, w: &WitnessGen) {
    match w {
        WitnessGen::Product { out, left, right } => {
            buf.push(0);
            put_uv(buf, u64::from(*out));
            put_lc_g(buf, left);
            put_lc_g(buf, right);
        }
        WitnessGen::Linear { out, lc } => {
            buf.push(1);
            put_uv(buf, u64::from(*out));
            put_lc_g(buf, lc);
        }
        WitnessGen::Xor { out, a, b } => {
            buf.push(2);
            put_uv(buf, u64::from(*out));
            put_lc_g(buf, a);
            put_lc_g(buf, b);
        }
        WitnessGen::Or { out, a, b } => {
            buf.push(3);
            put_uv(buf, u64::from(*out));
            put_lc_g(buf, a);
            put_lc_g(buf, b);
        }
        WitnessGen::Inverse { out, input } => {
            buf.push(4);
            put_uv(buf, u64::from(*out));
            put_lc_g(buf, input);
        }
        WitnessGen::InverseOrZero { out, input } => {
            buf.push(5);
            put_uv(buf, u64::from(*out));
            put_lc_g(buf, input);
        }
        WitnessGen::Bit { out, input, index } => {
            buf.push(6);
            put_uv(buf, u64::from(*out));
            put_lc_g(buf, input);
            put_uv(buf, u64::from(*index));
        }
        WitnessGen::Bits { outs, input } => {
            buf.push(7);
            put_ids_g(buf, outs);
            put_lc_g(buf, input);
        }
        WitnessGen::DivRem { q, r, num, den } => {
            buf.push(8);
            put_uv(buf, u64::from(*q));
            put_uv(buf, u64::from(*r));
            put_lc_g(buf, num);
            put_lc_g(buf, den);
        }
        WitnessGen::MulModDivMod {
            q,
            r,
            a,
            b,
            modulus,
            limb_bits,
        } => {
            buf.push(9);
            put_ids_g(buf, q);
            put_ids_g(buf, r);
            put_lcs_g(buf, a);
            put_lcs_g(buf, b);
            put_lcs_g(buf, modulus);
            put_uv(buf, u64::from(*limb_bits));
        }
        WitnessGen::ModInverse {
            out,
            a,
            modulus,
            limb_bits,
        } => {
            buf.push(10);
            put_ids_g(buf, out);
            put_lcs_g(buf, a);
            put_lcs_g(buf, modulus);
            put_uv(buf, u64::from(*limb_bits));
        }
        WitnessGen::Sub2 {
            qabs,
            r,
            a,
            b,
            c,
            modulus,
            limb_bits,
        } => {
            buf.push(11);
            put_uv(buf, u64::from(*qabs));
            put_ids_g(buf, r);
            put_lcs_g(buf, a);
            put_lcs_g(buf, b);
            put_lcs_g(buf, c);
            put_lcs_g(buf, modulus);
            put_uv(buf, u64::from(*limb_bits));
        }
    }
}

/// One item in a function body / top-level stream: a flat constraint, or a nested
/// CALL to another function def (its base/plugs in the *enclosing* def's coords).
enum GItem {
    Row(usize), // index into the flat constraint stream
    Call(u32, VarId, Vec<LinearCombination>),
}

// --- rolled CALL blocks (Stage 3: loop fusion for calls) ---------------------
// A loop that invokes cached function(s) each iteration emits one CALL item per
// invocation. With symbolic plugs those calls are AFFINE in the loop-carried vars
// (fixed per-iteration var stride), so a periodic run of CALL items compresses to
// a single rolled-CALL-block token — the CALL analogue of the flat-opcode roll
// (`bytecode::roll_and_encode_ops`), which only compresses runs of inline rows.
//
// A block has a `period` of `p` call templates (the loop body's calls, in order)
// repeated `count` times. Iteration `k` of template `j` reconstructs a plain CALL
// whose `base_var` and whose every plug-LC term var advance by that operand's
// constant step: `operand0 + k·step`. Coeffs and constants are loop-invariant
// (identical every iteration) so they are stored once. Expansion is BYTE-IDENTICAL
// to the unrolled CALLs — the encoder only rolls after verifying, iteration by
// iteration, that every operand reproduces exactly under the affine rule.
const MAX_CALL_PERIOD: usize = 1024;

/// One affine plug-LC template inside a rolled call: the loop-invariant constant
/// and, per term, its loop-invariant coeff plus the term var's `(var0, step)`.
struct PlugTemplate {
    constant: xark_ir::FieldConst,
    terms: Vec<(xark_ir::FieldConst, u32, i64)>, // (coeff, var0, var_step)
}
/// One call template in a rolled block (one call of the loop body).
struct CallTemplate {
    def: u32,
    base0: u32,
    base_step: i64,
    plugs: Vec<PlugTemplate>,
}
/// A rolled run of `count` repetitions of a `period`-length body of call templates.
struct RolledCall {
    count: u32,
    body: Vec<CallTemplate>,
}
/// The result of rolling a maximal run of consecutive CALL items: either a single
/// call (index into the enclosing item slice) or a rolled block.
enum CallTok {
    Single(usize),
    Rolled(RolledCall),
}

/// A call's structural signature (loop-invariant part): `def` + per-plug
/// `(constant, coeffs)`, serialized to bytes for fast exact comparison. Two calls
/// can share a rolled template iff their signatures are byte-equal.
fn call_sig(it: &GItem) -> Vec<u8> {
    let mut b = Vec::new();
    if let GItem::Call(d, _, plugs) = it {
        put_uv(&mut b, u64::from(*d));
        put_uv(&mut b, plugs.len() as u64);
        for lc in plugs {
            put_fc(&mut b, &lc.constant);
            put_uv(&mut b, lc.terms.len() as u64);
            for t in &lc.terms {
                put_fc(&mut b, &t.coeff);
            }
        }
    }
    b
}
/// A call's affine operands, in a fixed order: `base_var` then every plug-LC term
/// var (plug order, term order). These are the values that step per iteration.
fn call_operands(it: &GItem) -> Vec<i64> {
    let mut v = Vec::new();
    if let GItem::Call(_, base, plugs) = it {
        v.push(i64::from(*base));
        for lc in plugs {
            for t in &lc.terms {
                v.push(i64::from(t.var));
            }
        }
    }
    v
}

/// Try to roll the period-`p` block at `start` (in `sigs`/`ops`, the precomputed
/// signatures/operands of a maximal call run). Returns the maximal repeat count
/// (`≥ 2`) whose every operand reproduces `operand0 + k·step` exactly with matching
/// signatures, or `None`.
fn try_call_repeat(sigs: &[Vec<u8>], ops: &[Vec<i64>], start: usize, p: usize) -> Option<usize> {
    let n = sigs.len();
    if p == 0 || start + 2 * p > n {
        return None;
    }
    // Blocks 0 and 1 must be signature-identical, position by position.
    for j in 0..p {
        if sigs[start + p + j] != sigs[start + j]
            || ops[start + p + j].len() != ops[start + j].len()
        {
            return None;
        }
    }
    // Per-position, per-operand step from iteration 0 → 1.
    let steps: Vec<Vec<i64>> = (0..p)
        .map(|j| {
            ops[start + j]
                .iter()
                .zip(&ops[start + p + j])
                .map(|(a, b)| b - a)
                .collect()
        })
        .collect();
    // Extend while each further block reproduces exactly under the affine rule.
    let mut count = 2usize;
    while start + (count + 1) * p <= n {
        let base = start + count * p;
        let k = count as i64;
        let mut ok = true;
        for j in 0..p {
            if sigs[base + j] != sigs[start + j] || ops[base + j].len() != ops[start + j].len() {
                ok = false;
                break;
            }
            let matches = ops[start + j]
                .iter()
                .zip(&steps[j])
                .zip(&ops[base + j])
                .all(|((o0, s), actual)| o0 + k * s == *actual);
            if !matches {
                ok = false;
                break;
            }
        }
        if !ok {
            break;
        }
        count += 1;
    }
    Some(count)
}

/// Build a [`RolledCall`] for the period-`p`, `count`-repetition block at `start`
/// of `calls` (references to the run's consecutive CALL items). Iteration 0 gives
/// the loop-invariant coeffs/constants and the `var0`s; the per-operand step is the
/// iteration-0→1 delta.
fn build_rolled_call(calls: &[&GItem], start: usize, p: usize) -> RolledCall {
    let mut body = Vec::with_capacity(p);
    for j in 0..p {
        let GItem::Call(def, base0, plugs0) = calls[start + j] else {
            unreachable!("call run holds only Call items")
        };
        let o0 = call_operands(calls[start + j]);
        let o1 = call_operands(calls[start + p + j]);
        let steps: Vec<i64> = o0.iter().zip(&o1).map(|(a, b)| b - a).collect();
        // Operand index 0 is base; the rest map, in order, to plug term vars.
        let base_step = steps[0];
        let mut oi = 1usize;
        let plug_templates: Vec<PlugTemplate> = plugs0
            .iter()
            .map(|lc| {
                let terms = lc
                    .terms
                    .iter()
                    .map(|t| {
                        let step = steps[oi];
                        oi += 1;
                        (t.coeff.clone(), t.var, step)
                    })
                    .collect();
                PlugTemplate {
                    constant: lc.constant.clone(),
                    terms,
                }
            })
            .collect();
        body.push(CallTemplate {
            def: *def,
            base0: *base0,
            base_step,
            plugs: plug_templates,
        });
    }
    // count is recovered by the caller; store it there.
    RolledCall { count: 0, body }
}

/// Roll a maximal run of consecutive CALL items into `CallTok`s: greedily grab, at
/// each position, the block whose rolled span (`period · count`) is largest (ties
/// → smallest period), leaving un-rollable calls as singles. Correctness is
/// intrinsic: a block is only rolled after `try_call_repeat` proves every operand
/// reproduces exactly, so expansion is byte-identical to the flat calls.
fn roll_call_run(calls: &[&GItem]) -> Vec<CallTok> {
    let n = calls.len();
    let sigs: Vec<Vec<u8>> = calls.iter().map(|c| call_sig(c)).collect();
    let ops: Vec<Vec<i64>> = calls.iter().map(|c| call_operands(c)).collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < n {
        let maxp = ((n - i) / 2).min(MAX_CALL_PERIOD);
        let mut best: Option<(usize, usize)> = None; // (span, period)
        for p in 1..=maxp {
            if let Some(count) = try_call_repeat(&sigs, &ops, i, p) {
                let span = p * count;
                match best {
                    Some((bs, _)) if bs >= span => {}
                    _ => best = Some((span, p)),
                }
            }
        }
        if let Some((span, p)) = best {
            let count = span / p;
            let mut rolled = build_rolled_call(calls, i, p);
            rolled.count = count as u32;
            out.push(CallTok::Rolled(rolled));
            i += span;
        } else {
            out.push(CallTok::Single(i));
            i += 1;
        }
    }
    out
}

/// Serialize a rolled-CALL-block token body (tag already written): `count`,
/// `period`, then each call template `(def, base0, base_step, plugs)` where a plug
/// is `(constant, [(coeff, var0, var_step)])`. Mirrors `function_decode`'s
/// `parse_rolled_call`.
fn put_rolled_call(buf: &mut Vec<u8>, r: &RolledCall) {
    put_uv(buf, u64::from(r.count));
    put_uv(buf, r.body.len() as u64);
    for t in &r.body {
        put_uv(buf, u64::from(t.def));
        put_uv(buf, u64::from(t.base0));
        put_iv(buf, t.base_step);
        put_uv(buf, t.plugs.len() as u64);
        for pt in &t.plugs {
            put_fc(buf, &pt.constant);
            put_uv(buf, pt.terms.len() as u64);
            for (coeff, var0, step) in &pt.terms {
                put_fc(buf, coeff);
                put_uv(buf, u64::from(*var0));
                put_iv(buf, *step);
            }
        }
    }
}

// --- Complete DAG-compact circuit artifact (VERSION_FUNCTION = 8) --------------
// A self-contained container that expands to a full `CircuitProgram` (constraints
// + witness program + variable table): the sole `circuit.xbc` format.
// Header `MAGIC + 1u16`; the payload is function defs + top-level item streams
// (rows, function calls, and rolled periodic runs — see below).

/// The circuit-artifact container version. Version 1 is the sole format: the
/// DAG-function container that also rolls periodic runs of inline rows. (The former
/// flat=6 / loop=7 / function=8 encodings were collapsed into this.)
const VERSION_FUNCTION: u16 = 1;

fn vis_byte(v: &Visibility) -> u8 {
    match v {
        Visibility::Public => 0,
        Visibility::Private => 1,
        Visibility::Internal => 2,
    }
}
fn put_str(buf: &mut Vec<u8>, s: &str) {
    put_uv(buf, s.len() as u64);
    buf.extend_from_slice(s.as_bytes());
}
/// Serialize a constraint item stream. Item tags: `0` = a single inline row,
/// `1` = a function call, `2` = a **rolled** run of ≥2 consecutive rows (periodic
/// loops of primitives compress here, so the single container needn't carry them
/// unrolled). A maximal run of consecutive `Row`s becomes one token: length 1 →
/// tag 0, length ≥2 → tag 0x02 with a length-prefixed rolled-op blob.
fn ser_c_items(buf: &mut Vec<u8>, items: &[GItem], flat: &[R1csConstraint]) {
    // Plan tokens first: maximal Row-runs (each one token) and maximal Call-runs
    // (each rolled into `CallTok`s — a rolled block is one token, a single call is
    // one token). The token count must be written before the tokens themselves.
    enum CTok<'a> {
        RowRun(usize, usize), // items[start..end], all Row
        Call(&'a GItem),      // one CALL item
        Rolled(RolledCall),   // a rolled CALL block
    }
    let mut plan: Vec<CTok> = Vec::new();
    let mut i = 0;
    while i < items.len() {
        match &items[i] {
            GItem::Row(_) => {
                let start = i;
                while matches!(items.get(i), Some(GItem::Row(_))) {
                    i += 1;
                }
                plan.push(CTok::RowRun(start, i));
            }
            GItem::Call(..) => {
                let start = i;
                while matches!(items.get(i), Some(GItem::Call(..))) {
                    i += 1;
                }
                let calls: Vec<&GItem> = items[start..i].iter().collect();
                for tok in roll_call_run(&calls) {
                    match tok {
                        CallTok::Single(k) => plan.push(CTok::Call(calls[k])),
                        CallTok::Rolled(r) => plan.push(CTok::Rolled(r)),
                    }
                }
            }
        }
    }
    put_uv(buf, plan.len() as u64);

    for tok in &plan {
        match tok {
            CTok::Call(GItem::Call(d, base, plugs)) => {
                buf.push(1);
                put_uv(buf, u64::from(*d));
                put_uv(buf, u64::from(*base));
                put_lcs_g(buf, plugs);
            }
            CTok::Call(GItem::Row(_)) => unreachable!("CTok::Call holds a Call item"),
            CTok::Rolled(r) => {
                buf.push(3);
                put_rolled_call(buf, r);
            }
            CTok::RowRun(start, end) => {
                let (start, end) = (*start, *end);
                if end - start == 1 {
                    let GItem::Row(idx) = &items[start] else {
                        unreachable!()
                    };
                    buf.push(0);
                    put_row_g(buf, &flat[*idx]);
                } else {
                    let ops: Vec<xark_ir::bytecode::Opcode> = items[start..end]
                        .iter()
                        .map(|it| {
                            let GItem::Row(idx) = it else { unreachable!() };
                            // v8 rows drop debug notes (decoder sets `note: None`),
                            // so the rolled form matches the inline form exactly.
                            let r = &flat[*idx];
                            xark_ir::bytecode::Opcode::Constraint(xark_ir::R1csRow {
                                a: r.a.clone(),
                                b: r.b.clone(),
                                c: r.c.clone(),
                                note: None,
                            })
                        })
                        .collect();
                    let blob = xark_ir::bytecode::roll_and_encode_ops(ops);
                    buf.push(2);
                    put_uv(buf, blob.len() as u64);
                    buf.extend_from_slice(&blob);
                }
            }
        }
    }
}
/// Flush an accumulated run of consecutive witness ops as one token: tag `0` for
/// a single op, tag `2` for a rolled run of ≥2 (empties `run`).
fn flush_w_run(buf: &mut Vec<u8>, run: &mut Vec<xark_ir::bytecode::Opcode>) {
    match run.len() {
        0 => {}
        1 => {
            buf.push(0);
            if let xark_ir::bytecode::Opcode::Witness(w) = &run[0] {
                put_witness_g(buf, w);
            }
            run.clear();
        }
        _ => {
            let blob = xark_ir::bytecode::roll_and_encode_ops(std::mem::take(run));
            buf.push(2);
            put_uv(buf, blob.len() as u64);
            buf.extend_from_slice(&blob);
        }
    }
}

/// Serialize a witness item stream. Item tags: `0` = one witness op, `1` = a
/// function call, `2` = a rolled run of ≥2 witness ops, `3` = a rolled CALL block.
/// `Row`s with no witness-gen are holes (skipped, transparent to a run); a `Call`
/// ends the current run, and a maximal run of consecutive `Call`s is rolled the
/// same way the constraint stream rolls them (byte-identical CALL decisions).
fn ser_w_items_std(buf: &mut Vec<u8>, items: &[GItem], flat_w: &[Option<WitnessGen>]) {
    enum WTok<'a> {
        WitRun(Vec<xark_ir::bytecode::Opcode>), // ≥1 witness ops
        Call(&'a GItem),
        Rolled(RolledCall),
    }
    let mut plan: Vec<WTok> = Vec::new();
    let mut run: Vec<xark_ir::bytecode::Opcode> = Vec::new();
    let mut i = 0;
    while i < items.len() {
        match &items[i] {
            GItem::Row(idx) => {
                if let Some(w) = &flat_w[*idx] {
                    run.push(xark_ir::bytecode::Opcode::Witness(w.clone()));
                }
                i += 1;
            }
            GItem::Call(..) => {
                if !run.is_empty() {
                    plan.push(WTok::WitRun(std::mem::take(&mut run)));
                }
                let start = i;
                while matches!(items.get(i), Some(GItem::Call(..))) {
                    i += 1;
                }
                let calls: Vec<&GItem> = items[start..i].iter().collect();
                for tok in roll_call_run(&calls) {
                    match tok {
                        CallTok::Single(k) => plan.push(WTok::Call(calls[k])),
                        CallTok::Rolled(r) => plan.push(WTok::Rolled(r)),
                    }
                }
            }
        }
    }
    if !run.is_empty() {
        plan.push(WTok::WitRun(std::mem::take(&mut run)));
    }

    put_uv(buf, plan.len() as u64);
    for tok in &mut plan {
        match tok {
            WTok::WitRun(run) => flush_w_run(buf, run),
            WTok::Call(GItem::Call(d, base, plugs)) => {
                buf.push(1);
                put_uv(buf, u64::from(*d));
                put_uv(buf, u64::from(*base));
                put_lcs_g(buf, plugs);
            }
            WTok::Call(GItem::Row(_)) => unreachable!("WTok::Call holds a Call item"),
            WTok::Rolled(r) => {
                buf.push(3);
                put_rolled_call(buf, r);
            }
        }
    }
}

/// Build the complete VERSION_FUNCTION artifact from a finished lowering: header +
/// field + var table (as call-scattered kinds + a small explicit remainder) +
/// function defs (each with its var-kinds and both item streams) + top-level
/// streams. Expands via [`expand_function_blob`] to a byte-identical `CircuitProgram`.
fn build_function_blob(env: &LoweringEnv, field: &FieldSpec, num_inputs: usize) -> Vec<u8> {
    let flat = &env.constraints;
    let flat_w = &env.witness_gen;
    // Symbolic replays never nest (a replay dumps its template's flat constraints,
    // making no further calls), so every recorded call range is DISJOINT. Sort by
    // (constraint start, end) — since constraints and witness ops are appended in
    // lockstep, this also orders the witness spans.
    let mut ranges = env.function_calls.clone();
    ranges.sort_by(|a, b| a.1.cmp(&b.1).then(a.2.cmp(&b.2)));

    // One def per distinct replayed key. The def BODY is the canonical template (in
    // its own capture coords: `base_var` + `plug_vars`); each CALL substitutes the
    // caller's plug LCs into it on expand. Templates are flat (nested functions were
    // inlined at capture), so a def has no nested calls.
    let mut def_idx: BTreeMap<String, u32> = BTreeMap::new();
    let mut def_keys: Vec<String> = Vec::new();
    for r in &ranges {
        if env.function_templates.contains_key(&r.0) {
            def_idx.entry(r.0.clone()).or_insert_with(|| {
                def_keys.push(r.0.clone());
                (def_keys.len() - 1) as u32
            });
        }
    }

    let mut b = Vec::new();
    b.extend_from_slice(&xark_ir::bytecode::MAGIC);
    b.extend_from_slice(&VERSION_FUNCTION.to_le_bytes());
    put_str(&mut b, &field.name);
    put_str(&mut b, field.modulus_decimal.as_deref().unwrap_or(""));
    put_uv(&mut b, env.variables.len() as u64);
    // The var *table* is trivial to reconstruct: the first `num_inputs` vars are
    // the signature inputs (Public/Private, matched by name at prove time), and
    // EVERY other var is `Derived` — including hint/advice vars, which carry
    // `Visibility::Private` but are computed by the witness program, not supplied.
    // So we store only the inputs (role + name); the rest are `v{id}` / Derived.
    put_uv(&mut b, num_inputs as u64);
    for id in 0..num_inputs {
        b.push(vis_byte(&env.variables[id].visibility));
        put_str(&mut b, &env.variables[id].name);
    }
    // --- function defs: one canonical template body each ------------------------
    put_uv(&mut b, def_keys.len() as u64);
    for key in &def_keys {
        let t = env
            .function_templates
            .get(key)
            .expect("def key has a template");
        put_uv(&mut b, u64::from(t.base_var));
        put_ids_g(&mut b, &t.plug_vars);
        // Output vars — the internal vars a caller reads after the call. Recorded
        // so a per-template R1CS minimizer can PIN them (like plugs) as the def's
        // interface while eliminating the rest. Outputs are LCs (a bit-sum word is
        // `Σ 2ⁱ·rᵢ`), so pin every var they reference; the expansion itself does
        // not consume this field (the top stream references these vars directly).
        let mut outs: Vec<VarId> = t
            .outputs
            .iter()
            .flat_map(|(_, lc)| lc.terms.iter().map(|t| t.var))
            .collect();
        outs.sort_unstable();
        outs.dedup();
        put_ids_g(&mut b, &outs);
        // Body = the template's own constraints / witness ops, as inline rows (they
        // roll if periodic). No nested CALLs — templates are already flat.
        let c_items: Vec<GItem> = (0..t.constraints.len()).map(GItem::Row).collect();
        ser_c_items(&mut b, &c_items, &t.constraints);
        let w_flat: Vec<Option<WitnessGen>> = t.witness.iter().cloned().map(Some).collect();
        let w_items: Vec<GItem> = (0..t.witness.len()).map(GItem::Row).collect();
        ser_w_items_std(&mut b, &w_items, &w_flat);
    }

    // --- top-level streams: rows interspersed with the disjoint CALLs ----------
    #[allow(clippy::type_complexity)]
    let call_ranges: Vec<&(
        String,
        usize,
        usize,
        VarId,
        Vec<LinearCombination>,
        usize,
        usize,
    )> = ranges
        .iter()
        .filter(|r| def_idx.contains_key(&r.0))
        .collect();
    let mut top_c: Vec<GItem> = Vec::new();
    {
        let (mut i, mut k) = (0usize, 0usize);
        while i < flat.len() {
            if k < call_ranges.len() && call_ranges[k].1 == i {
                let r = call_ranges[k];
                top_c.push(GItem::Call(def_idx[&r.0], r.3, r.4.clone()));
                i = r.2;
                k += 1;
            } else {
                top_c.push(GItem::Row(i));
                i += 1;
            }
        }
    }
    let mut top_w: Vec<GItem> = Vec::new();
    {
        let (mut i, mut k) = (0usize, 0usize);
        while i < flat_w.len() {
            if k < call_ranges.len() && call_ranges[k].5 == i {
                let r = call_ranges[k];
                top_w.push(GItem::Call(def_idx[&r.0], r.3, r.4.clone()));
                i = r.6;
                k += 1;
            } else {
                top_w.push(GItem::Row(i));
                i += 1;
            }
        }
    }
    ser_c_items(&mut b, &top_c, flat);
    ser_w_items_std(&mut b, &top_w, flat_w);
    // Keep-set exception for the decoder's prune. `finish` drops every UNREFERENCED
    // `Internal` var but retains `Private` (advice/hint outputs) even unreferenced.
    // The decoder drops all unreferenced non-input vars, so we hand it the only
    // exceptions — unreferenced advice — to keep. Almost always empty (a live hint
    // is pinned by a constraint, hence referenced), so this costs ~1 byte.
    let mut referenced: BTreeSet<VarId> = BTreeSet::new();
    for c in flat {
        for lc in [&c.a, &c.b, &c.c] {
            for t in &lc.terms {
                referenced.insert(t.var);
            }
        }
    }
    let keep_extra: Vec<VarId> = (num_inputs..env.variables.len())
        .filter(|&id| {
            !referenced.contains(&(id as u32))
                // unreferenced advice, or witness-only scratch (Internal but live
                // via the witness-gen program) — both retained by `finish`.
                && (env.variables[id].visibility == Visibility::Private
                    || env.witness_only_vars.contains(&(id as u32)))
        })
        .map(|id| id as u32)
        .collect();
    put_ids_g(&mut b, &keep_extra);
    b
}

/// The DAG-compact `VERSION_FUNCTION` container is the sole `circuit.xbc` artifact,
/// built for every circuit (it rolls periodic runs of inline rows, so needs no flat
/// fallback). Retained as a function (always `true`) because function capture is
/// gated on it in a couple of places.
fn function_artifact_enabled() -> bool {
    true
}
fn auto_dag_enabled() -> bool {
    compact_enabled()
}
/// Whether to actually *replay* cached functions (skip the walk). Off = still
/// recognize functions (materialize plugs, strip notes, capture) but walk every
/// call — the byte-identity reference to diff replay against.
fn function_replay_enabled() -> bool {
    compact_enabled()
}

/// Inline an ordinary function call: evaluate the arguments in the caller frame,
/// lower the callee's MIR body in a fresh frame, and bind its return value. This
/// is what makes functions "just library code": a call to `poseidon(..)` or a
/// local helper expands into the same LC/constraint lowering as inline code.
fn inline_call<'tcx>(
    env: &mut LoweringEnv<'tcx>,
    def_id: DefId,
    call_args: rustc_middle::ty::GenericArgsRef<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    dest: rustc_middle::mir::Local,
) -> CompileResult<()> {
    if !env.tcx.is_mir_available(def_id) {
        let path = env.tcx.def_path_str(def_id);
        // `assert!`/`assert_eq!`/`panic!` expand to a `core::panicking::panic*` call.
        // Those are the single most common "I wrote normal Rust" mistake, so steer
        // the author to the circuit primitive instead of the generic MIR-availability
        // note (which is really about calling into un-encoded gadget crates).
        if path.contains("panic") {
            return Err(
                CompileError::new("native `assert!` / `panic!` don't constrain a circuit")
                    .with_help(
                    "use `require_eq(a, b)` to constrain equality (it emits an R1CS constraint); \
                 `assert!(a == b)` instead computes a `bool` wire and then panics, which a \
                 circuit can't do",
                ),
            );
        }
        return Err(CompileError::new(format!(
            "unsupported function call inside circuit: `{path}`"
        ))
        .with_note(
            "only xark field operations, require_eq, and functions whose MIR is available \
             (build function crates with `-Zalways-encode-mir`) can be inlined",
        ));
    }

    if env.inlining.contains(&def_id) {
        return Err(CompileError::new(format!(
            "recursion is not supported: `{}` calls itself",
            env.tcx.def_path_str(def_id)
        )));
    }

    // Bit-cache: `Field::to_bits::<N>(x)` is memoized on `(canonical(x), N)`.
    // A hit returns the cached bit vars and emits nothing (skipping the `N`
    // booleanity + 1 recomposition constraints); a miss falls through to the
    // ordinary inline below (so the miss path is *byte-identical* to the
    // un-cached lowering) and captures the produced bits afterward.
    // Only memoize *witness* decompositions (non-constant LCs). A constant's bits
    // are all pinned to fixed values, so caching them saves little and — crucially
    // — decomposing the same constant twice is the one repeat some existing functions
    // do (BLAKE2s/3 decompose `Field::from(0u8)` etc. more than once), which must
    // stay byte-identical. The optimization that matters is amortizing a *witness*
    // value's range check across repeated width-`N` ops (docs/integer-ops.md).
    let bit_cache_key: Option<(CanonicalLcKey, usize)> = if env.registry.is_to_bits(def_id) {
        let n = call_args
            .const_at(0)
            .try_to_target_usize(env.tcx)
            .ok_or_else(|| CompileError::new("`to_bits::<N>`: width `N` must be a constant"))?
            as usize;
        // `self` is the sole argument; its LC in the caller frame is the key.
        let x = env.operand_to_lc(&args[0].node)?;
        if x.is_constant() {
            // Const-fold: the input's value is known at compile time, so its bits
            // are fixed. The `N` booleanity (`bitᵢ² == bitᵢ`) and the recomposition
            // (`Σ bitᵢ·2ⁱ == c`) constraints the witness path emits are then all
            // tautologies — satisfied by the known bits and by nothing else — so
            // dropping them removes zero degrees of freedom: what was provable
            // stays provable, and no witness is admitted that wasn't before. It is
            // a pure constraint-count reduction with no soundness change. We bind
            // each `dest` bit slot to its constant `0`/`1` LC and emit nothing.
            //
            // If the constant does not fit in `N` bits, the recomposition could
            // never hold (an `N`-bit sum lives in `[0, 2ᴺ)`), so the circuit was
            // already unprovable at prove time; rejecting it here is strictly
            // better — a clean compile error instead of a silent dead end.
            let bits = x.constant.to_bits_le(n).ok_or_else(|| {
                CompileError::new(format!(
                    "constant `{}` does not fit in {n} bits",
                    x.constant.decimal()
                ))
                .with_note("`Field::to_bits::<N>` of a constant requires `0 <= value < 2^N`")
            })?;
            for (i, &b) in bits.iter().enumerate() {
                let lc = if b {
                    LinearCombination::one()
                } else {
                    LinearCombination::zero()
                };
                env.set_field_at(dest, &[i as u64], lc);
            }
            return Ok(());
        } else {
            // Bit-sum shortcut: if `x` is already `Σ 2ⁱ·bᵢ` over genuinely
            // booleanity-constrained bits, those bits ARE its canonical `n`-bit
            // decomposition — bind them directly and emit nothing (no fresh advice,
            // booleanity, or recomposition). This recovers the redundant
            // decomposition a caller would otherwise do on a function's recomposed
            // word output (see `bit_sum_shortcut`; lossless, not a new constraint).
            if let Some(bits) = env.bit_sum_shortcut(&x, n) {
                for (i, &v) in bits.iter().enumerate() {
                    env.set_field_at(dest, &[i as u64], LinearCombination::var(v));
                }
                return Ok(());
            }
            let key = (canonical_lc_key(&x), n);
            // The bit cache makes a `to_bits` return vars from an *earlier* call —
            // fine when inlining, but it breaks function purity (a function body would
            // reference vars outside its own args/internals, which replay can't
            // reproduce per call). One of several such cross-call memoizations.
            if env.function_depth == 0
                && let Some(bits) = env.bit_cache.get(&key).cloned() {
                    for (i, &v) in bits.iter().enumerate() {
                        env.set_field_at(dest, &[i as u64], LinearCombination::var(v));
                    }
                    return Ok(());
                }
            Some(key)
        }
    } else {
        None
    };

    // === Frontend-function path ===
    // A callee whose args are all Field values (auto-DAG, or `#[no_mangle]`)
    // is a cached function: every field leaf materializes to a single-var plug (a
    // point / bignum is several leaves), the body is lowered once, and reused calls
    // REPLAY (a bytecode CALL). Multi-leaf inputs *and* outputs are supported.
    let is_function_call = call_memo_enabled() && env.is_function(def_id);
    let mut arg_values: Vec<ArgValue> = args.iter().map(|a| env.eval_arg(&a.node)).collect();
    // First-occurrence capture materializes single-var plugs (`plug_vars`); a
    // symbolic replay instead passes the caller's arg LCs straight in (`plug_lcs`).
    let mut plug_vars: Vec<VarId> = Vec::new();
    let mut plug_lcs: Vec<LinearCombination> = Vec::new();
    // A function call is one whose args are all `Field` values. Its key
    // `def|substs|p<arity>` is fixed by the *arity* (total field leaves), which is
    // known before materializing plugs — so the fold pre-pass can count/measure a
    // key and pass 2 can decide whether to template it, both using the same key.
    let all_fields = is_function_call
        && arg_values
            .iter()
            .all(|av| matches!(av, ArgValue::Fields(_)));
    let function_key = if all_fields {
        let plug_arity: usize = arg_values
            .iter()
            .map(|av| {
                if let ArgValue::Fields(l) = av {
                    l.len()
                } else {
                    0
                }
            })
            .sum();
        let key = format!("{def_id:?}|{call_args:?}|p{plug_arity}");
        // Tally this call for the fold decision (only in the measuring pass; pass 2
        // consults the precomputed `promotions`).
        if env.promotions.is_none() {
            *env.function_call_counts.entry(key.clone()).or_insert(0) += 1;
        }
        // Promote to a CALL only when the pre-pass approved it (called `>= 2`
        // times). In the measuring pass (`promotions == None`) template everything
        // so every key is seen. Not promoted → inline (fold) this call: leave args
        // unmaterialized and fall through to the plain walk below (keeps its
        // `mul→require_eq` merges + notes).
        // Never promote inside a witness-only region: a symbolic replay bypasses
        // the normal emit path (its constraints/vars are remapped directly), so the
        // constraint-suppression + var-recording hooks wouldn't fire. Inlining
        // (the fold path) walks the body through those hooks — the region stays
        // constraint-free and every var is recorded pinning-exempt.
        let promote = !env.witness_only
            && match &env.promotions {
                None => true,
                Some(p) => p.get(&key).copied().unwrap_or(false),
            };
        if promote {
            // A cached template (pass 2 always, or a later pass-1 occurrence) →
            // symbolic replay: pass the caller's arg LCs straight in (sorted by
            // path for a stable plug order), no materialization. Otherwise (first
            // occurrence, template absent) materialize each leaf to a distinct
            // single-var plug so the walked body is a pure function of its plugs and
            // can be captured.
            let will_replay =
                function_replay_enabled() && env.function_templates.contains_key(&key);
            let mut seen: BTreeSet<VarId> = BTreeSet::new();
            for av in &mut arg_values {
                if let ArgValue::Fields(leaves) = av {
                    leaves.sort_by(|x, y| x.0.cmp(&y.0));
                    for (_, lc) in leaves.iter_mut() {
                        if will_replay {
                            plug_lcs.push(lc.clone());
                        } else {
                            let mut v = env.materialize_to_var(lc.clone());
                            // Plugs must be distinct: an aliased plug (the same var
                            // in two positions — e.g. `xor32(rotr(w,7), rotr(w,18))`
                            // shares w's bits) would collapse the plug substitution.
                            // Copy the duplicate so every plug position is unique.
                            if !seen.insert(v) {
                                v = env.copy_var(v);
                                seen.insert(v);
                            }
                            plug_vars.push(v);
                            *lc = LinearCombination::var(v);
                        }
                    }
                }
            }
            // `plug_lcs.len()` / `plug_vars.len() == plug_arity`, so this equals `key`.
            Some(key)
        } else {
            None
        }
    } else {
        None
    };

    // REPLAY: cached function + replay enabled → substitute the caller's arg LCs into
    // the template and append it, skipping the walk.
    if let Some(key) = &function_key
        && function_replay_enabled() && env.function_templates.contains_key(key) {
            let c_start = env.constraints.len();
            let w_start = env.witness_gen.len();
            let base = env.next_var_id;
            let outs = env.replay_function(key, &plug_lcs);
            if function_artifact_enabled() {
                env.function_calls.push((
                    key.clone(),
                    c_start,
                    env.constraints.len(),
                    base,
                    plug_lcs.clone(),
                    w_start,
                    env.witness_gen.len(),
                ));
            }
            env.call_memo_total += 1;
            env.call_memo_ok += 1;
            env.bind_value(dest, &[], ArgValue::Fields(outs));
            return Ok(());
        }

    // Snapshot resources so a function's body constraints/witness can be captured.
    let cap_base_var = env.next_var_id;
    let cap_base_c = env.constraints.len();
    let cap_base_w = env.witness_gen.len();

    // Lower the callee body in a fresh frame with params bound to the args. The
    // callee's generic args are pushed so nested calls in a generic body (e.g.
    // the blanket `Into::into`) monomorphize correctly.
    let body = env.tcx.optimized_mir(def_id);
    env.inlining.push(def_id);
    env.inline_substs.push(call_args);
    env.enter_frame();
    // If this function fixes the kind of the constraints it emits (e.g.
    // `require_bool` → Booleanity), push that override for the duration of its
    // body. Only relevant when profiling; harmless otherwise.
    let pushed_kind =
        function_kind_hint(env.tcx.item_name(def_id).as_str()).inspect(|&k| env.kind_stack.push(k));

    for (i, value) in arg_values.into_iter().enumerate() {
        let param = rustc_middle::mir::Local::from_usize(i + 1);
        env.bind_value(param, &[], value);
    }

    // Inside a function body cross-call caches are suppressed (purity). Nested calls
    // keep the depth raised, so the whole subtree is cache-free.
    let is_function_walk = function_key.is_some();
    // Scope the `mul → require_eq` merge state to this function body: save + clear the
    // caller's `pending_mul`/`merged` so a body-local mul can't fold across the
    // boundary (replayed functions never register for the merge, so a walk must match).
    // Restored after capture. `bit_cache` stays untouched (that's Stage 2).
    let saved_pending = if is_function_walk {
        std::mem::take(&mut env.pending_mul)
    } else {
        BTreeMap::new()
    };
    let saved_merged = if is_function_walk {
        std::mem::take(&mut env.merged)
    } else {
        BTreeMap::new()
    };
    if is_function_walk {
        env.function_depth += 1;
    }
    let walk_result = walk_body(env, body);
    let ret = env.frame_return();
    if is_function_walk {
        env.function_depth -= 1;
        // Local revival: an intra-body merge folded `a*b=t; require(t==x)` → `a*b=x`
        // and dropped `t`. If `t` is still referenced by a captured body constraint
        // or a function output, re-emit `a*b=t` so the captured template stays
        // self-contained (a merged var referenced later must stay defined).
        let mut ref_now: BTreeSet<VarId> = BTreeSet::new();
        for c in &env.constraints[cap_base_c..] {
            for lc in [&c.a, &c.b, &c.c] {
                for term in &lc.terms {
                    ref_now.insert(term.var);
                }
            }
        }
        if let ArgValue::Fields(f) = &ret {
            for (_, lc) in f {
                for term in &lc.terms {
                    ref_now.insert(term.var);
                }
            }
        }
        for (out, (a, b, wg_idx, _)) in std::mem::take(&mut env.merged) {
            if ref_now.contains(&out) {
                let id = env.fresh_constraint_id();
                env.push_constraint(
                    ConstraintKind::Mul,
                    R1csConstraint::mul(id, a.clone(), b.clone(), out, ""),
                );
                env.witness_gen[wg_idx] = Some(WitnessGen::Product {
                    out,
                    left: a,
                    right: b,
                });
            }
        }
        // Restore the caller's merge state; body-local merges never leak out.
        env.pending_mul = saved_pending;
        env.merged = saved_merged;
    }

    if pushed_kind.is_some() {
        env.kind_stack.pop();
    }
    env.exit_frame();
    env.inline_substs.pop();
    env.inlining.pop();
    walk_result?;

    // Function capture: keep each output leaf as its linear combination (do NOT
    // materialize it to a fresh word var), strip notes (so walk-mode is note-free
    // like replay-mode), and store the template on the first call. Only
    // Field-returning functions are templated; others keep the walked result.
    //
    // Keeping outputs as LCs is what lets a recomposed-word output `Σ 2ⁱ·rᵢ` reach
    // the caller as that sum (the caller's `to_bits` shortcut then avoids a
    // redundant decomposition). An output references only plugs + body internals,
    // so purity is unaffected; a single-var output is just the LC `1·v`.
    let out_leaves = match &ret {
        ArgValue::Fields(f) if function_key.is_some() => Some(f.clone()),
        _ => None,
    };
    let ret = if let (Some(key), Some(mut leaves)) = (&function_key, out_leaves) {
        leaves.sort_by(|x, y| x.0.cmp(&y.0));
        let outputs: Vec<(Vec<u64>, LinearCombination)> = leaves;
        for c in &mut env.constraints[cap_base_c..] {
            c.debug = None;
        }
        // Only cache/replay a function that is a pure function of its plugs; an
        // impure body (bit cache, cross-boundary merge, …) stays walked, so replay
        // is always byte-identical.
        let pure = function_is_pure(
            &env.constraints[cap_base_c..],
            &env.witness_gen[cap_base_w..],
            cap_base_var,
            &plug_vars,
        );
        if pure && !env.function_templates.contains_key(key) {
            let constraints = env.constraints[cap_base_c..].to_vec();
            let witness: Vec<WitnessGen> = env.witness_gen[cap_base_w..]
                .iter()
                .filter_map(|w| w.clone())
                .collect();
            let var_kinds: Vec<Visibility> = env.variables[cap_base_var as usize..]
                .iter()
                .map(|v| v.visibility.clone())
                .collect();
            let t = FunctionTemplate {
                constraints,
                witness,
                base_var: cap_base_var,
                plug_vars: plug_vars.clone(),
                var_kinds,
                outputs: outputs.clone(),
            };
            env.function_templates.insert(key.clone(), t);
        }
        if pure && function_artifact_enabled() {
            // The captured body still references the materialized single-var plugs,
            // so the CALL's plug LCs are just `var(plug)`.
            let plug_call_lcs: Vec<LinearCombination> = plug_vars
                .iter()
                .map(|&v| LinearCombination::var(v))
                .collect();
            env.function_calls.push((
                key.clone(),
                cap_base_c,
                env.constraints.len(),
                cap_base_var,
                plug_call_lcs,
                cap_base_w,
                env.witness_gen.len(),
            ));
        }
        env.call_memo_total += 1;
        env.call_memo_ok += 1;
        ArgValue::Fields(outputs)
    } else {
        ret
    };

    // Bind the return value into the caller frame.
    env.bind_value(dest, &[], ret);

    // Bit-cache miss: capture the freshly produced bit vars (each returned slot
    // is a single `var(bᵢ)` LC) so a later `to_bits::<N>` on the same value hits.
    // Never populate the cache from inside a function body — those bits are the
    // function's own internals and must not leak to other calls.
    if let Some(key) = bit_cache_key.filter(|_| env.function_depth == 0) {
        let n = key.1;
        let mut bits = Vec::with_capacity(n);
        for i in 0..n {
            match env.get_field_at(dest, &[i as u64]) {
                Some(lc)
                    if lc.constant.is_zero()
                        && lc.terms.len() == 1
                        && lc.terms[0].coeff.is_one() =>
                {
                    bits.push(lc.terms[0].var);
                }
                // Defensive: an unexpected non-var slot → don't cache (correctness
                // over the optimization). Should not happen for `to_bits`.
                _ => return Ok(()),
            }
        }
        env.bit_cache.insert(key, bits);
    }
    Ok(())
}

/// Finalize: drop unreferenced internal variables and assemble both programs.
fn finish(mut env: LoweringEnv<'_>, field: FieldSpec, n_inputs: usize) -> LowerOutput {
    // Developer diagnostic only (behind `XARK_BUILD_TIME`); a normal build stays
    // quiet on stderr rather than printing this on every compile.
    if crate::dbg_flag("XARK_BUILD_TIME") && call_memo_enabled() && env.call_memo_total > 0 {
        eprintln!(
            "CALLMEMO: {}/{} function-call replays byte-exact ({:.1}%); {} distinct function templates captured",
            env.call_memo_ok,
            env.call_memo_total,
            100.0 * env.call_memo_ok as f64 / env.call_memo_total as f64,
            env.function_templates.len()
        );
    }
    // Revive a merged mul output (its `a·b = out` folded into `require_eq`) if a
    // later constraint still references it, so the reuse stays bound to `a·b`.
    // Not-reused outputs are pruned below (fast path unchanged). This MUST run
    // before `build_function_blob` below — else the revived rows land in the flat
    // R1CS but not the artifact, leaving the artifact (what the prover proves)
    // under-constrained for a reused product (XARK_VERIFY caught exactly this).
    {
        let mut ref_now: BTreeSet<VarId> = BTreeSet::new();
        for c in &env.constraints {
            for lc in [&c.a, &c.b, &c.c] {
                for term in &lc.terms {
                    ref_now.insert(term.var);
                }
            }
        }
        for (out, (a, b, wg_idx, orig_idx)) in std::mem::take(&mut env.merged) {
            if ref_now.contains(&out) {
                let id = env.fresh_constraint_id();
                // Inherit the original mul's attribution (source line + chain);
                // it is genuinely a `Mul`. Keeps `profile` index-aligned with
                // `constraints` for the appended revival.
                if env.profile_enabled {
                    let mut prof = env.profile[orig_idx].clone();
                    prof.id = id;
                    prof.kind = ConstraintKind::Mul;
                    env.profile.push(prof);
                }
                env.constraints.push(R1csConstraint::mul(
                    id,
                    a.clone(),
                    b.clone(),
                    out,
                    "revived a*b = out (product reused after require_eq merge)",
                ));
                env.witness_gen[wg_idx] = Some(WitnessGen::Product {
                    out,
                    left: a,
                    right: b,
                });
            }
        }
    }
    // Witness-only dead-code elimination. A `witness_only` region emits value ops
    // (kept) alongside pin-only ops — range-check bit decompositions, carry hints —
    // whose only consumer, a constraint, was suppressed. Those are dead weight in
    // the witness program. Prune them by transitive liveness: a var is live if a
    // constraint references it, or a live op reads it; keep only live witness-only
    // ops/vars. (No-op for ordinary circuits — `check_pinning` guarantees every
    // non-witness-only hint output is constraint-referenced, hence already live.)
    // Runs BEFORE `build_function_blob` so the flat R1CS and the artifact prune
    // identically (XARK_VERIFY). Merged ops (`None`) are left untouched.
    if !env.witness_only_vars.is_empty() {
        let mut live: BTreeSet<VarId> = BTreeSet::new();
        for c in &env.constraints {
            for lc in [&c.a, &c.b, &c.c] {
                for t in &lc.terms {
                    live.insert(t.var);
                }
            }
        }
        // Witness-gen is in dependency order, so one reverse pass reaches fixpoint:
        // a live output pulls in the op's sibling outputs and its inputs.
        for op in env.witness_gen.iter().flatten().rev() {
            let outs = witness_gen_outs(op);
            if outs.iter().any(|o| live.contains(o)) {
                for o in outs {
                    live.insert(o);
                }
                for v in witness_gen_input_vars(op) {
                    live.insert(v);
                }
            }
        }
        let dead: Vec<usize> = (0..env.witness_gen.len())
            .filter(|&i| {
                env.witness_gen[i].as_ref().is_some_and(|op| {
                    let outs = witness_gen_outs(op);
                    outs.iter().any(|o| env.witness_only_vars.contains(o))
                        && outs.iter().all(|o| !live.contains(o))
                })
            })
            .collect();
        // Drop the dead ops (the witness-gen saving). The dead output vars stay
        // declared + pinning-exempt (in `witness_only_vars`) — harmless, unreferenced
        // scratch — so `finish` and `build_function_blob` keep the same var/exempt
        // sets and only the (now-`None`) ops differ, which both already skip.
        for i in dead {
            env.witness_gen[i] = None;
        }
    }
    // Complete DAG-compact artifact — built AFTER the revival above (so the
    // artifact == the flat R1CS: the reused-product binding is in both) and while
    // `env`/`field` are still intact. The single container rolls periodic runs of
    // inline rows (see `ser_c_items`), so it also compresses loops of primitives —
    // no functions required. Built for EVERY circuit (the sole on-disk format).
    let function_xbc = if function_artifact_enabled() {
        Some(build_function_blob(&env, &field, n_inputs))
    } else {
        None
    };

    let mut referenced: BTreeSet<VarId> = BTreeSet::new();
    for c in &env.constraints {
        for lc in [&c.a, &c.b, &c.c] {
            for term in &lc.terms {
                referenced.insert(term.var);
            }
        }
    }
    // Witness-only vars carry no constraint but ARE live: they feed the witness-gen
    // of a downstream, pinned result (e.g. `x²` feeding `d = x²·x²`). Keeping them —
    // and their witness-gen — is required, or the derived value computes from an
    // uncomputed (zero) input.
    let wo = core::mem::take(&mut env.witness_only_vars);

    let variables: Vec<Variable> = env
        .variables
        .into_iter()
        .filter(|v| {
            v.visibility != Visibility::Internal || referenced.contains(&v.id) || wo.contains(&v.id)
        })
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
            xark_ir::expr_from_r1cs(
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

    let profile = env.profile;

    let r1cs = R1csProgram {
        field,
        variables,
        constraints: env.constraints,
    };

    LowerOutput {
        r1cs,
        primitive,
        profile,
        function_xbc,
        witness_only_vars: wo,
    }
}

/// All output variables of a witness-gen op (multi-output ops list every limb/bit).
fn witness_gen_outs(op: &WitnessGen) -> Vec<VarId> {
    match op {
        WitnessGen::Product { out, .. }
        | WitnessGen::Linear { out, .. }
        | WitnessGen::Xor { out, .. }
        | WitnessGen::Or { out, .. }
        | WitnessGen::Inverse { out, .. }
        | WitnessGen::InverseOrZero { out, .. }
        | WitnessGen::Bit { out, .. } => vec![*out],
        WitnessGen::Bits { outs, .. } => outs.clone(),
        WitnessGen::DivRem { q, r, .. } => vec![*q, *r],
        WitnessGen::MulModDivMod { q, r, .. } => q.iter().chain(r).copied().collect(),
        WitnessGen::ModInverse { out, .. } => out.clone(),
        WitnessGen::Sub2 { qabs, r, .. } => {
            let mut v = vec![*qabs];
            v.extend(r);
            v
        }
    }
}

/// All input variables a witness-gen op reads (from its input linear combinations).
fn witness_gen_input_vars(op: &WitnessGen) -> Vec<VarId> {
    fn add(lc: &LinearCombination, v: &mut Vec<VarId>) {
        v.extend(lc.terms.iter().map(|t| t.var));
    }
    let mut v = Vec::new();
    match op {
        WitnessGen::Product { left, right, .. } => {
            add(left, &mut v);
            add(right, &mut v);
        }
        WitnessGen::Linear { lc, .. } => add(lc, &mut v),
        WitnessGen::Xor { a, b, .. } | WitnessGen::Or { a, b, .. } => {
            add(a, &mut v);
            add(b, &mut v);
        }
        WitnessGen::Inverse { input, .. }
        | WitnessGen::InverseOrZero { input, .. }
        | WitnessGen::Bit { input, .. }
        | WitnessGen::Bits { input, .. } => add(input, &mut v),
        WitnessGen::DivRem { num, den, .. } => {
            add(num, &mut v);
            add(den, &mut v);
        }
        WitnessGen::MulModDivMod { a, b, modulus, .. } => {
            for l in a.iter().chain(b).chain(modulus) {
                add(l, &mut v);
            }
        }
        WitnessGen::ModInverse { a, modulus, .. } => {
            for l in a.iter().chain(modulus) {
                add(l, &mut v);
            }
        }
        WitnessGen::Sub2 {
            a, b, c, modulus, ..
        } => {
            for l in a.iter().chain(b).chain(c).chain(modulus) {
                add(l, &mut v);
            }
        }
    }
    v
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
        // Multi-output; represented by its first bit for the "is any output still
        // referenced" filter (all bits of a decomposition are used together).
        WitnessGen::Bits { outs, .. } => *outs.first().unwrap_or(&0),
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

/// The Rust source spelling of a MIR `BinOp`, for diagnostics (never the raw
/// `BitAnd`/`Shl`/… debug name the author never typed).
fn binop_symbol(op: rustc_middle::mir::BinOp) -> &'static str {
    use rustc_middle::mir::BinOp::*;
    match op {
        Add | AddUnchecked | AddWithOverflow => "+",
        Sub | SubUnchecked | SubWithOverflow => "-",
        Mul | MulUnchecked | MulWithOverflow => "*",
        Div => "/",
        Rem => "%",
        BitXor => "^",
        BitAnd => "&",
        BitOr => "|",
        Shl | ShlUnchecked => "<<",
        Shr | ShrUnchecked => ">>",
        Eq => "==",
        Lt => "<",
        Le => "<=",
        Ne => "!=",
        Ge => ">=",
        Gt => ">",
        Cmp => "cmp",
        Offset => "offset",
    }
}

/// The Rust source spelling of a MIR `UnOp`, for diagnostics.
fn unop_symbol(op: rustc_middle::mir::UnOp) -> &'static str {
    use rustc_middle::mir::UnOp::*;
    match op {
        Not => "!",
        Neg => "-",
        PtrMetadata => "&-metadata",
    }
}

/// A user-facing description of an unsupported terminator, in Rust-source terms
/// (never the raw MIR variant name). The circuit author never wrote "SwitchInt".
fn terminator_name(kind: &TerminatorKind<'_>) -> &'static str {
    match kind {
        TerminatorKind::SwitchInt { .. } => "a branch (`if`/`match`) on a witness value",
        TerminatorKind::Assert { .. } => "a runtime `assert!` / overflow check",
        TerminatorKind::Drop { .. } => "dropping an owned value",
        TerminatorKind::Unreachable => "an unreachable branch",
        TerminatorKind::InlineAsm { .. } => "inline assembly (`asm!`)",
        _ => "an unsupported control-flow construct",
    }
}

/// A user-facing description of an unsupported rvalue, in Rust-source terms
/// (never the raw MIR variant name).
fn rvalue_name(rvalue: &Rvalue<'_>) -> &'static str {
    match rvalue {
        Rvalue::Ref(..) => "taking a reference (`&` / `&mut`)",
        Rvalue::RawPtr(..) => "a raw pointer",
        Rvalue::Cast(..) => "a cast (`as`)",
        Rvalue::Aggregate(..) => "building a struct / array / tuple value",
        Rvalue::BinaryOp(..) => "a native integer / bool operation",
        Rvalue::UnaryOp(..) => "a native unary operation",
        _ => "an unsupported operation",
    }
}

#[cfg(test)]
mod bit_sum_tests {
    use super::bit_sum_match;
    use std::collections::BTreeSet;
    use xark_ir::{FieldConst, LinearCombination, Term, VarId};

    /// Build `Σ coeffs[i]·vars[i]` (zero constant) for testing.
    fn lc(pairs: &[(i64, VarId)]) -> LinearCombination {
        LinearCombination {
            constant: FieldConst::zero(),
            terms: pairs
                .iter()
                .map(|&(c, v)| Term {
                    coeff: FieldConst::from_i64(c),
                    var: v,
                })
                .collect(),
        }
    }

    #[test]
    fn boolean_bit_sum_is_shortcut() {
        let x = lc(&[(1, 10), (2, 11), (4, 12)]); // 3-bit sum over vars 10,11,12
        let boolean: BTreeSet<VarId> = [10, 11, 12].into_iter().collect();
        assert_eq!(
            bit_sum_match(&x, 3, |v| boolean.contains(&v)),
            Some(vec![10, 11, 12])
        );
    }

    #[test]
    fn non_boolean_summand_is_not_shortcut() {
        let x = lc(&[(1, 10), (2, 11), (4, 12)]);
        // var 12 is NOT booleanity-constrained → must NOT shortcut (would be
        // unsound: 12 could be any field value, not a genuine bit).
        let boolean: BTreeSet<VarId> = [10, 11].into_iter().collect();
        assert_eq!(bit_sum_match(&x, 3, |v| boolean.contains(&v)), None);
    }

    #[test]
    fn wrong_coefficients_are_not_shortcut() {
        // coeffs 1,2,8 (missing the 4-weight, has an 8) — not a clean n-bit sum.
        let x = lc(&[(1, 10), (2, 11), (8, 12)]);
        let boolean: BTreeSet<VarId> = [10, 11, 12].into_iter().collect();
        assert_eq!(bit_sum_match(&x, 3, |v| boolean.contains(&v)), None);
    }

    #[test]
    fn repeated_var_is_not_shortcut() {
        // Same var in two positions: not a distinct-bit decomposition.
        let x = lc(&[(1, 10), (2, 10), (4, 12)]);
        let boolean: BTreeSet<VarId> = [10, 12].into_iter().collect();
        assert_eq!(bit_sum_match(&x, 3, |v| boolean.contains(&v)), None);
    }

    #[test]
    fn nonzero_constant_is_not_shortcut() {
        let mut x = lc(&[(1, 10), (2, 11)]);
        x.constant = FieldConst::from_i64(1);
        let boolean: BTreeSet<VarId> = [10, 11].into_iter().collect();
        assert_eq!(bit_sum_match(&x, 2, |v| boolean.contains(&v)), None);
    }

    #[test]
    fn wrong_term_count_is_not_shortcut() {
        let x = lc(&[(1, 10), (2, 11)]); // 2 terms but asked for width 3
        let boolean: BTreeSet<VarId> = [10, 11].into_iter().collect();
        assert_eq!(bit_sum_match(&x, 3, |v| boolean.contains(&v)), None);
    }
}
