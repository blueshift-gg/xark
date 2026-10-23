//! The circuit builder: allocates variables and emits R1CS constraints and the
//! witness-generation program.

use std::collections::{BTreeMap, BTreeSet};

use xark_ir::primitive::WitnessGen;
use xark_ir::{
    ConstraintKind, ConstraintProfile, LinearCombination, R1csConstraint, VarId, Variable,
    Visibility,
};

use crate::error::{CompileError, CompileResult};
use crate::output::FunctionTemplate;

/// A stable, `Ord`-able key for a canonical [`LinearCombination`]: its constant
/// plus its sorted `(coeff, var)` terms, all as canonical decimal strings
/// (`FieldConst::decimal` is always `BigInt::to_string()` output, so equal
/// values compare equal). Used to memoize bit decompositions (see `bit_cache`).
/// A constraint's debug note: formatted only when notes are wanted (`r1cs.json`).
/// Notes never reach `circuit.xbc`, so skipping them changes no artifact a normal
/// build writes.
macro_rules! note {
    ($b:expr, $($fmt:tt)*) => {
        if $b.notes { format!($($fmt)*) } else { String::new() }
    };
}

/// A fast hasher for dense integer keys (variable ids).
#[derive(Default, Clone, Copy)]
pub(crate) struct IdHasher(u64);
impl std::hash::Hasher for IdHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0.rotate_left(5) ^ b as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
        }
    }
    fn write_u32(&mut self, x: u32) {
        self.0 = (x as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}
pub(crate) type IdMap<K, V> =
    std::collections::HashMap<K, V, std::hash::BuildHasherDefault<IdHasher>>;

/// A content hash of a linear combination (deterministic across runs).
pub(crate) fn lc_hash(lc: &LinearCombination) -> u64 {
    #[inline]
    fn mix(h: u64, x: u64) -> u64 {
        (h.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95)
    }
    #[inline]
    fn fc(h: u64, c: &xark_ir::FieldConst) -> u64 {
        match c.as_big() {
            None => mix(h, c.as_i64().expect("small") as u64),
            Some(v) => v.iter_u64_digits().fold(
                mix(h, 0xb16 ^ (v.sign() == num_bigint::Sign::Minus) as u64),
                mix,
            ),
        }
    }
    let mut h = fc(0x1c5, &lc.constant);
    h = mix(h, lc.terms.len() as u64);
    for t in &lc.terms {
        h = fc(mix(h, t.var as u64), &t.coeff);
    }
    // Final avalanche (the products table keys on the full 64 bits).
    h ^= h >> 33;
    h = h.wrapping_mul(0xff51_afd7_ed55_8ccd);
    h ^= h >> 33;
    h
}

/// Dev knob (diagnostics): an env var's numeric value.
pub(crate) fn dev_knob(name: &str) -> Option<usize> {
    std::env::var(name).ok().and_then(|v| v.parse().ok())
}

pub(crate) type CanonicalLcKey = (String, Vec<(String, VarId)>);

/// Build the [`CanonicalLcKey`] for `lc` (simplified → merged + sorted terms).
pub(crate) fn canonical_lc_key(lc: &LinearCombination) -> CanonicalLcKey {
    let lc = lc.clone().simplified();
    (
        lc.constant.decimal(),
        lc.terms
            .iter()
            .map(|t| (t.coeff.decimal().clone(), t.var))
            .collect(),
    )
}

pub(crate) fn booleanity_var(c: &R1csConstraint) -> Option<VarId> {
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
pub(crate) fn bit_sum_match(
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

pub(crate) fn pow2_fc(n: usize) -> xark_ir::FieldConst {
    let mut p = xark_ir::FieldConst::from_i64(1);
    let two = xark_ir::FieldConst::from_i64(2);
    let mut i = 0;
    while i < n {
        p = p.mul(&two);
        i += 1;
    }
    p
}

pub(crate) fn pow2_lc(n: usize) -> LinearCombination {
    LinearCombination::constant(pow2_fc(n).decimal().clone())
}

/// Source attribution for profiling: the user's circuit line and the gadget call chain.
#[derive(Clone, Debug, Default)]
pub struct Location {
    pub file: String,
    pub line: u32,
    pub col: u32,
}

pub struct Builder {
    pub(crate) variables: Vec<Variable>,
    pub(crate) var_names: Vec<String>,
    pub(crate) constraints: Vec<R1csConstraint>,
    pub(crate) next_var_id: VarId,
    internal_counter: u32,
    advice_counter: u32,
    next_constraint_id: u32,
    pending_mul: IdMap<VarId, (usize, usize)>,
    /// Merged mul outputs → `(witness-gen index, constraint index)`; the operands
    /// stay in that constraint (a merge only rewrites its `c`).
    pub(crate) merged: IdMap<VarId, (usize, usize)>,
    /// Every constrained multiplication `(witness-gen index, constraint index, output)`:
    /// its `Product` witness op is filled in by [`Builder::fill_products`] (from the
    /// row's operands) unless the mul was merged — so a merged mul never pays for
    /// copying its operands into a witness op it then drops.
    deferred_products: Vec<(usize, usize, VarId)>,
    pub(crate) witness_gen: Vec<Option<WitnessGen>>,
    pub(crate) bit_cache: BTreeMap<(CanonicalLcKey, usize), Vec<VarId>>,
    /// Template defs found by [`crate::templates::detect`], in creation order.
    pub(crate) function_templates: Vec<FunctionTemplate>,
    /// Every template call, top-level or nested inside a def body.
    pub(crate) function_calls: Vec<crate::output::FunctionCall>,
    pub(crate) witness_only: bool,
    pub(crate) witness_only_vars: BTreeSet<VarId>,
    pub(crate) profile_enabled: bool,
    pub(crate) location: Location,
    pub(crate) chain: Vec<String>,
    pub(crate) profile: Vec<ConstraintProfile>,
    pub(crate) kind_stack: Vec<ConstraintKind>,
    pub(crate) boolean_vars: crate::output::VarSet,
    /// Build debug notes and internal variable names (only `r1cs.json` /
    /// `circuit.json` show them).
    pub(crate) notes: bool,
    /// Products already constrained, by operand hash → `(output, constraint index)`
    /// (common-subexpression reuse in [`Builder::emit_mul`]).
    products: IdMap<(u64, u64), (VarId, usize)>,
    /// Reuse repeated products (off under `XARK_NO_CSE`).
    pub(crate) cse: bool,
    /// Materialize multiplication operands with more terms than this.
    pub(crate) mat_threshold: usize,
    /// Input variables in binding order (normally `0..n`; see `output::renumber_inputs`).
    pub(crate) input_ids: Vec<VarId>,
    /// Per wasm call, what it produced (for post-hoc templates).
    pub(crate) regions: Vec<crate::templates::Region>,
    region_stack: Vec<usize>,
}

impl Builder {
    pub fn new(profile_enabled: bool) -> Self {
        Builder {
            variables: Vec::new(),
            var_names: Vec::new(),
            constraints: Vec::new(),
            next_var_id: 0,
            internal_counter: 0,
            advice_counter: 0,
            next_constraint_id: 0,
            pending_mul: IdMap::default(),
            merged: IdMap::default(),
            deferred_products: Vec::new(),
            witness_gen: Vec::new(),
            bit_cache: BTreeMap::new(),
            function_templates: Vec::new(),
            function_calls: Vec::new(),
            witness_only: false,
            witness_only_vars: BTreeSet::new(),
            profile_enabled,
            location: Location::default(),
            chain: Vec::new(),
            profile: Vec::new(),
            kind_stack: Vec::new(),
            boolean_vars: crate::output::VarSet::default(),
            notes: true,
            mat_threshold: dev_knob("XARK_MAT_THRESHOLD").unwrap_or(4096),
            products: IdMap::default(),
            cse: dev_knob("XARK_NO_CSE").is_none(),
            input_ids: Vec::new(),
            regions: Vec::new(),
            region_stack: Vec::new(),
        }
    }

    /// A wasm call begins: start recording what it produces.
    pub(crate) fn region_begin(&mut self) {
        let parent = self.region_stack.last().copied();
        self.regions.push(crate::templates::Region {
            c0: self.constraints.len(),
            c1: 0,
            w0: self.witness_gen.len(),
            w1: 0,
            v0: self.next_var_id,
            v1: 0,
            parent,
            closed: false,
        });
        self.region_stack.push(self.regions.len() - 1);
    }

    /// The innermost wasm call returned.
    pub(crate) fn region_end(&mut self) {
        if let Some(i) = self.region_stack.pop() {
            let r = &mut self.regions[i];
            r.c1 = self.constraints.len();
            r.w1 = self.witness_gen.len();
            r.v1 = self.next_var_id;
            r.closed = true;
            // Too small to template, and so is everything inside it: drop it now
            // (an Ed25519 build makes ~28M wasm calls).
            if r.c1 - r.c0 < crate::templates::MIN_ROWS {
                self.regions.truncate(i);
            }
        }
    }

    pub(crate) fn alloc_var(&mut self, name: String, visibility: Visibility) -> VarId {
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

    pub(crate) fn alloc_internal(&mut self) -> VarId {
        let name = if self.notes {
            format!("t{}", self.internal_counter)
        } else {
            String::new()
        };
        self.internal_counter += 1;
        self.alloc_var(name, Visibility::Internal)
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
    pub(crate) fn bit_sum_shortcut(&self, x: &LinearCombination, n: usize) -> Option<Vec<VarId>> {
        bit_sum_match(x, n, |v| self.boolean_vars.contains(&v))
    }

    pub(crate) fn alloc_advice(&mut self) -> VarId {
        let name = if self.notes {
            format!("w{}", self.advice_counter)
        } else {
            String::new()
        };
        self.advice_counter += 1;
        self.alloc_var(name, Visibility::Private)
    }

    pub(crate) fn fresh_constraint_id(&mut self) -> u32 {
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
    pub(crate) fn push_constraint(&mut self, kind: ConstraintKind, c: R1csConstraint) {
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

    pub(crate) fn constraint_profile(&self, id: u32, kind: ConstraintKind) -> ConstraintProfile {
        ConstraintProfile {
            id,
            file: self.location.file.clone(),
            line: self.location.line,
            col: self.location.col,
            chain: self.chain.clone(),
            kind,
        }
    }

    // --- rendering (for debug notes) ---------------------------------------

    pub(crate) fn render_lc(&self, lc: &LinearCombination) -> String {
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
    pub(crate) fn render_side(&self, lc: &LinearCombination) -> String {
        let compound = lc.terms.len() + usize::from(!lc.constant.is_zero()) > 1;
        let inner = self.render_lc(lc);
        if compound {
            format!("({inner})")
        } else {
            inner
        }
    }

    // --- operand helpers ----------------------------------------------------

    /// A pending mul var that a compound expression consumes can no longer be
    /// merged into a later equality.
    pub(crate) fn consume_pending(&mut self, lc: &LinearCombination) {
        if let Some(v) = self.as_pending_var(lc) {
            self.pending_mul.remove(&v);
        }
    }

    /// [`Self::consume_pending`] for the linear combination `1·v`.
    pub(crate) fn consume_pending_var(&mut self, v: VarId) {
        self.pending_mul.remove(&v);
    }

    pub(crate) fn as_pending_var(&self, lc: &LinearCombination) -> Option<VarId> {
        if lc.constant.is_zero() && lc.terms.len() == 1 {
            let term = &lc.terms[0];
            if term.coeff.is_one() && self.pending_mul.contains_key(&term.var) {
                return Some(term.var);
            }
        }
        None
    }

    /// If `lc` has more than `mat_threshold` terms, name it as a fresh internal
    /// variable `v` (emit `lc - v = 0`, record `v = eval(lc)`) and return `v`.
    ///
    /// The bound is large: in R1CS a large sum costs nothing inline in a row, while
    /// naming it costs a constraint and a variable (Poseidon: 400 → 241 constraints
    /// against naming every operand over 8 terms). It only guards against
    /// pathological growth (`XARK_MAT_THRESHOLD=<n>` to experiment).
    pub(crate) fn materialize(&mut self, lc: LinearCombination) -> LinearCombination {
        if lc.terms.len() <= self.mat_threshold {
            return lc;
        }
        let v = self.alloc_internal();
        let id = self.fresh_constraint_id();
        // Cheap note (materialized LCs are large by definition).
        let note = note!(
            self,
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
    pub(crate) fn emit_mul(
        &mut self,
        lhs: LinearCombination,
        rhs: LinearCombination,
    ) -> LinearCombination {
        LinearCombination::var(self.emit_mul_var(lhs, rhs))
    }

    /// [`Self::emit_mul`], returning the output variable `t`.
    pub(crate) fn emit_mul_var(&mut self, lhs: LinearCombination, rhs: LinearCombination) -> VarId {
        let lhs = self.materialize(lhs);
        let rhs = self.materialize(rhs);
        // The same product (either order) already constrained: reuse its output. The
        // earlier row pins it to `lhs·rhs`, so this is exact — the substitution
        // `t := out` that `Xark.R1cs.cse_sound` (`formal/Formal/Rewrites.lean`) proves
        // preserves the circuit's relation. The row is re-checked to be literally
        // `lhs · rhs = out` (the table keys on hashes).
        let key = (!self.witness_only && self.cse).then(|| {
            let (x, y) = (lc_hash(&lhs), lc_hash(&rhs));
            (x.min(y), x.max(y))
        });
        if let Some(k) = key
            && let Some(&(out, c_idx)) = self.products.get(&k)
        {
            // Only an output already used as a value: one still eligible for the
            // `require_eq` merge (or already merged) would need its row revived,
            // which costs as much as the product it saves.
            let c = &self.constraints[c_idx];
            if !self.pending_mul.contains_key(&out)
                && !self.merged.contains_key(&out)
                && ((c.a == lhs && c.b == rhs) || (c.a == rhs && c.b == lhs))
                && c.c == LinearCombination::var(out)
            {
                if dev_knob("XARK_CSE_LOG").is_some() {
                    eprintln!(
                        "cse: reuse {} = {} * {}",
                        self.var_names[out as usize],
                        self.render_side(&lhs),
                        self.render_side(&rhs)
                    );
                }
                return out;
            }
        }
        let out = self.alloc_internal();
        // Witness-only: compute the product (so the solver fills `out`) but emit
        // no product constraint and no merge state — `out` is pinning-exempt scratch.
        if self.witness_only {
            self.witness_gen.push(Some(WitnessGen::Product {
                out,
                left: lhs,
                right: rhs,
            }));
            return out;
        }
        // The product of two pinned booleans (an AND) is boolean: its row pins it.
        let both_bool = self.is_boolean_lc(&lhs) && self.is_boolean_lc(&rhs);
        let id = self.fresh_constraint_id();
        let note = note!(
            self,
            "{} * {} = {}",
            self.render_side(&lhs),
            self.render_side(&rhs),
            self.var_names[out as usize]
        );
        self.push_constraint(
            ConstraintKind::Mul,
            R1csConstraint::mul(id, lhs, rhs, out, &note),
        );
        let c_idx = self.constraints.len() - 1;
        if both_bool {
            self.boolean_vars.insert(out);
        }
        // Witness-gen: the mul output is computed as `eval(lhs) * eval(rhs)` — filled
        // in from the row's operands at the end (`fill_products`).
        self.witness_gen.push(None);
        let wg_idx = self.witness_gen.len() - 1;
        self.deferred_products.push((wg_idx, c_idx, out));
        if let Some(k) = key {
            self.products.insert(k, (out, c_idx));
        }
        // Always register the mul for the `mul → require_eq` merge. Intra-function
        // merges now fold `a*b=t; require(t==x)` → `a*b=x` *inside* a function body
        // (the caller's merge state is saved/cleared on entry so cross-boundary
        // folds stay suppressed, and body-local merges are revived at capture if
        // still referenced — keeping the template self-contained).
        self.pending_mul.insert(out, (c_idx, wg_idx));
        out
    }

    /// `lc` is `0`, `1`, `v` or `1 − v` for a pinned-boolean `v`.
    pub(crate) fn is_boolean_lc(&self, lc: &LinearCombination) -> bool {
        match &lc.terms[..] {
            [] => lc.constant.is_zero() || lc.constant.is_one(),
            [t] => {
                self.boolean_vars.contains(&t.var)
                    && ((lc.constant.is_zero() && t.coeff.is_one())
                        || (lc.constant.is_one() && t.coeff.is_neg_one()))
            }
            _ => false,
        }
    }

    /// Emit a fused boolean XOR: allocate `c`, emit `(2a) * b = a + b - c`, and
    /// record `c = a + b - 2ab`. `c` is a single variable, so chained XORs (e.g.
    /// Keccak's theta) don't grow linear combinations.
    pub(crate) fn emit_xor(
        &mut self,
        a: LinearCombination,
        b: LinearCombination,
    ) -> LinearCombination {
        self.consume_pending(&a);
        self.consume_pending(&b);
        let c = self.alloc_internal();
        let id = self.fresh_constraint_id();
        let a2 = a.clone().scale(&xark_ir::FieldConst::from_i64(2));
        let c_side = a.clone() + b.clone() - LinearCombination::var(c);
        let note = note!(self, "{} = xor", self.var_names[c as usize]);
        self.push_constraint(
            ConstraintKind::Xor,
            R1csConstraint::general(id, a2, b.clone(), c_side, &note),
        );
        self.witness_gen.push(Some(WitnessGen::Xor {
            out: c,
            a: a.clone(),
            b: b.clone(),
        }));
        // XOR / OR of `{0,1}` operands is `{0,1}` (the row pins `c` to it).
        if !self.witness_only && self.is_boolean_lc(&a) && self.is_boolean_lc(&b) {
            self.boolean_vars.insert(c);
        }
        LinearCombination::var(c)
    }

    /// Emit a fused boolean OR: allocate `c`, emit `a * b = a + b - c`, record
    /// `c = a + b - ab`.
    pub(crate) fn emit_or(
        &mut self,
        a: LinearCombination,
        b: LinearCombination,
    ) -> LinearCombination {
        self.consume_pending(&a);
        self.consume_pending(&b);
        let c = self.alloc_internal();
        let id = self.fresh_constraint_id();
        let c_side = a.clone() + b.clone() - LinearCombination::var(c);
        let note = note!(self, "{} = or", self.var_names[c as usize]);
        self.push_constraint(
            ConstraintKind::Or,
            R1csConstraint::general(id, a.clone(), b.clone(), c_side, &note),
        );
        self.witness_gen.push(Some(WitnessGen::Or {
            out: c,
            a: a.clone(),
            b: b.clone(),
        }));
        // XOR / OR of `{0,1}` operands is `{0,1}` (the row pins `c` to it).
        if !self.witness_only && self.is_boolean_lc(&a) && self.is_boolean_lc(&b) {
            self.boolean_vars.insert(c);
        }
        LinearCombination::var(c)
    }

    pub(crate) fn emit_pow(&mut self, base: LinearCombination, n: u64) -> LinearCombination {
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
    pub(crate) fn is_witness_only_lc(&self, lc: &LinearCombination) -> bool {
        !self.witness_only_vars.is_empty()
            && lc
                .terms
                .iter()
                .any(|t| self.witness_only_vars.contains(&t.var))
    }

    pub(crate) fn emit_require_eq(&mut self, lhs: LinearCombination, rhs: LinearCombination) {
        // Witness-only region: no row, and no rewrite of a row emitted before it.
        if self.witness_only {
            return;
        }
        // Merge `t = a * b; require_eq(t, target)` into `a * b = target` — but never
        // when `target` is a witness-only var: it already has a witness-gen op, so
        // rewriting a constraint to output it would doubly-define it (the value
        // from its own witness-gen vs. from `a·b`). Fall through to a clean equality.
        if let Some(v) = self.as_pending_var(&lhs)
            && !self.is_witness_only_lc(&rhs)
        {
            self.merge_mul(v, rhs);
            return;
        }
        if let Some(v) = self.as_pending_var(&rhs)
            && !self.is_witness_only_lc(&lhs)
        {
            self.merge_mul(v, lhs);
            return;
        }

        let diff = lhs - rhs;
        let id = self.fresh_constraint_id();
        let note = note!(self, "({}) * 1 = 0", self.render_lc(&diff));
        self.push_constraint(
            ConstraintKind::Equality,
            R1csConstraint::equal(id, diff, LinearCombination::zero(), &note),
        );
    }

    /// `g → lhs = rhs` for a `{0,1}` guard `g`: the row `g · (lhs − rhs) = 0`. The
    /// equality binds only when `g = 1`, so it never feeds a merge, a substitution or
    /// a booleanity fact (see `crate::host`'s branch guards).
    pub(crate) fn emit_require_eq_gated(
        &mut self,
        g: LinearCombination,
        lhs: LinearCombination,
        rhs: LinearCombination,
    ) {
        self.consume_pending(&lhs);
        self.consume_pending(&rhs);
        self.consume_pending(&g);
        let diff = lhs - rhs;
        if diff.is_constant() && diff.constant.is_zero() {
            return;
        }
        let id = self.fresh_constraint_id();
        let note = note!(
            self,
            "({}) * ({}) = 0",
            self.render_lc(&g),
            self.render_lc(&diff)
        );
        self.push_constraint(
            ConstraintKind::Equality,
            R1csConstraint::general(id, g, diff, LinearCombination::zero(), &note),
        );
    }

    /// A hint's input inside a witness-branch arm: `g · x`, which is `x` where the
    /// arm is taken and `0` where it isn't — so the hint always solves, and its
    /// output there is the canonical `0` (see [`Self::pin_dead`]).
    pub(crate) fn gate_input(
        &mut self,
        g: Option<&LinearCombination>,
        x: LinearCombination,
    ) -> LinearCombination {
        match g {
            None => x,
            Some(_) if x.is_constant() && x.constant.is_zero() => x,
            Some(g) => {
                self.consume_pending(&x);
                self.consume_pending(g);
                self.emit_mul(g.clone(), x)
            }
        }
    }

    /// `(1 − g) · v = 0`: a hint variable of an untaken arm is pinned to `0`, so every
    /// variable stays uniquely determined by the inputs (what `xark prove`'s
    /// under-constraint gate checks), not just the ones that reach the output.
    pub(crate) fn pin_dead(&mut self, g: Option<&LinearCombination>, v: VarId) {
        self.pin_dead_to(g, v, 0);
    }

    /// [`Self::pin_dead`] to `value`, for a hint whose output on its dead-arm
    /// inputs isn't `0` (a modular inverse of `1`): `(1 − g) · (v − value) = 0`.
    pub(crate) fn pin_dead_to(&mut self, g: Option<&LinearCombination>, v: VarId, value: i64) {
        if let Some(g) = g {
            let not_g = LinearCombination::one() - g.clone();
            self.emit_require_eq_gated(
                not_g,
                LinearCombination::var(v),
                LinearCombination::constant(value.to_string()),
            );
        }
    }

    /// Emit an `n`-bit range proof over a (possibly compound) linear combination:
    /// decompose `value` into `n` boolean bits and pin their recomposition to
    /// `value` (⇒ `value < 2^n`).
    /// Decompose `value` into `n` little-endian boolean bit vars: hint them (batched
    /// `Bits`), pin each `∈ {0,1}`, and pin `Σ bitᵢ·2ⁱ == value` (which also proves
    /// `value < 2^n`). Returns the bit vars — the shared core of the range proof and
    /// the native bitwise ops.
    pub(crate) fn decompose_bits(&mut self, value: LinearCombination, n: usize) -> Vec<VarId> {
        self.decompose_bits_gated(value, n, None)
    }

    /// [`Self::decompose_bits`] in a witness-branch arm with guard `gate`: the bits
    /// decompose `gate · value`, so the range proof binds where the arm is taken
    /// and the bits are `0` where it isn't (an out-of-range `value` is fine there).
    pub(crate) fn decompose_bits_gated(
        &mut self,
        value: LinearCombination,
        n: usize,
        gate: Option<LinearCombination>,
    ) -> Vec<VarId> {
        let value = self.gate_input(gate.as_ref(), value);
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
            let note = note!(self, "{} in {{0,1}}", self.var_names[b as usize]);
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
        let note = note!(self, "{n}-bit range: recompose == <lc>");
        self.push_constraint(
            ConstraintKind::Equality,
            R1csConstraint::equal(id, recomp, value, &note),
        );
        bit_vars
    }

    pub(crate) fn emit_range_proof_lc(&mut self, value: LinearCombination, n: usize) {
        let _ = self.decompose_bits(value, n);
    }

    /// Equality-to-zero function: a `{0,1}` lc that is `1` iff `input == 0`.
    /// `out = 1 − input·inv` with `input·out == 0` and `inv·out == 0` (the
    /// inverse-or-zero hint yields `0` when `input == 0`, and the last row makes
    /// that the only choice). Backs `==` on `Field`.
    pub(crate) fn emit_is_zero(&mut self, input: LinearCombination) -> LinearCombination {
        let inv = self.alloc_advice();
        self.witness_gen.push(Some(WitnessGen::InverseOrZero {
            out: inv,
            input: input.clone(),
        }));
        let prod = self.emit_mul(input.clone(), LinearCombination::var(inv));
        let out = LinearCombination::one() - prod;
        let input_out = self.emit_mul(input, out.clone());
        self.emit_require_eq(input_out, LinearCombination::zero());
        // `inv · out = 0`: when `input == 0` (`out = 1`) the hint's `inv = 0` is the
        // only value, rather than free — else the under-constraint gate `xark prove`
        // runs rejects every witness where the compared values are equal.
        // (`out` references the pending `input·inv` product: use it as a value
        // first, so that row isn't folded into a later `require_eq`.)
        self.consume_pending(&out);
        let inv_out = self.emit_mul(LinearCombination::var(inv), out.clone());
        self.emit_require_eq(inv_out, LinearCombination::zero());
        out
    }

    /// Unsigned `a < b` for `a, b ∈ [0, 2^n)`: a `{0,1}` lc. Borrow trick:
    /// `top = bitₙ(a − b + 2ⁿ)`, `lt = 1 − top`, range-prove
    /// `r = a − b + lt·2ⁿ ∈ [0, 2ⁿ)` (which pins `lt`). Needs `n ≤ 252`.
    pub(crate) fn emit_less_than(
        &mut self,
        n: usize,
        a: LinearCombination,
        b: LinearCombination,
    ) -> CompileResult<LinearCombination> {
        self.emit_less_than_gated(n, a, b, None)
    }

    /// [`Self::emit_less_than`] whose range proof binds only where `gate` is `1`
    /// (operands outside `[0, 2^n)` are then fine in an untaken arm).
    pub(crate) fn emit_less_than_gated(
        &mut self,
        n: usize,
        a: LinearCombination,
        b: LinearCombination,
        gate: Option<LinearCombination>,
    ) -> CompileResult<LinearCombination> {
        if n > 252 {
            return Err(CompileError::new(
                "comparison requires N ≤ 252 so 2^(N+1) ≤ BN254 field order",
            )
            .with_help("use a narrower fixed width; `2^(N+1)` must stay below the field order"));
        }
        let two_pow_n = pow2_lc(n);
        let diff_plus = a.clone() - b.clone() + two_pow_n.clone();
        let diff_plus = self.gate_input(gate.as_ref(), diff_plus);
        let top = self.alloc_advice();
        self.witness_gen.push(Some(WitnessGen::Bit {
            out: top,
            input: diff_plus,
            index: n as u32,
        }));
        // Booleanity: `top * top == top` (⟺ `top ∈ {0, 1}`). Attributed to the
        // comparison (its structural borrow bit), not a bare booleanity.
        let id = self.fresh_constraint_id();
        let note = note!(
            self,
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
        self.pin_dead(gate.as_ref(), top);
        let lt = LinearCombination::one() - LinearCombination::var(top);
        // `r = a − b + lt·2ⁿ`; range-proving `r ∈ [0, 2ⁿ)` pins `lt`. The `lt·2ⁿ`
        // product is part of the comparison; the range proof is a RangeCheck.
        let lt_pow = self.emit_mul(lt.clone(), two_pow_n);
        self.kind_stack.pop();
        let r = (a.clone() - b.clone()) + lt_pow;
        self.kind_stack.push(ConstraintKind::RangeCheck);
        let _ = self.decompose_bits_gated(r, n, gate);
        self.kind_stack.pop();
        Ok(lt)
    }

    /// Booleanity for a fresh advice `v`: emit `v · v = v` (⟺ `v ∈ {0,1}`) and record
    /// `v` as boolean. Used by the wrapping-arithmetic carry/borrow bits.
    pub(crate) fn emit_booleanity(&mut self, v: VarId, note: &str) {
        let id = self.fresh_constraint_id();
        let lc = LinearCombination::var(v);
        self.push_constraint(
            ConstraintKind::RangeCheck,
            R1csConstraint::general(id, lc.clone(), lc.clone(), lc, note),
        );
        // A witness-only region emits no row, so `v` is not proven boolean.
        if !self.witness_only {
            self.boolean_vars.insert(v);
        }
    }

    /// Wrapping `uN` subtraction (`a − b mod 2^N`). Bit `N` of `a − b + 2^N` is `1` iff
    /// `a ≥ b`, so `borrow = 1 − that`; `result = a − b + borrow·2^N` is range-checked
    /// `< 2^N`, pinning the unique borrow. One booleanity + one N-bit range check.
    pub(crate) fn emit_wrapping_sub(
        &mut self,
        n: usize,
        a: LinearCombination,
        b: LinearCombination,
    ) -> LinearCombination {
        let shifted = a.clone() - b.clone() + pow2_lc(n);
        let ge = self.alloc_advice();
        self.witness_gen.push(Some(WitnessGen::Bit {
            out: ge,
            input: shifted,
            index: n as u32,
        }));
        self.emit_booleanity(ge, "wrap-sub !borrow ∈ {0,1}");
        let borrow = LinearCombination::one() - LinearCombination::var(ge);
        let result = a - b + borrow.scale(&pow2_fc(n));
        self.kind_stack.push(ConstraintKind::RangeCheck);
        self.emit_range_proof_lc(result.clone(), n);
        self.kind_stack.pop();
        result
    }

    /// Fill in the `Product` witness op of every constrained multiplication that
    /// wasn't merged into a `require_eq` (see `deferred_products`): exactly the op
    /// `emit_mul` used to push eagerly, and the same one a merge would have dropped.
    pub(crate) fn fill_products(&mut self) {
        use rayon::prelude::*;
        let deferred = std::mem::take(&mut self.deferred_products);
        // Witness-gen slot → its deferred product (`u32::MAX`: none), so every slot
        // fills itself in place, in parallel.
        let mut at = vec![u32::MAX; self.witness_gen.len()];
        for (k, &(wg_idx, _, out)) in deferred.iter().enumerate() {
            if !self.merged.contains_key(&out) {
                at[wg_idx] = k as u32;
            }
        }
        let constraints = &self.constraints;
        self.witness_gen
            .par_iter_mut()
            .zip(at.par_iter())
            .filter(|(_, k)| **k != u32::MAX)
            .for_each(|(slot, &k)| {
                let (_, c_idx, out) = deferred[k as usize];
                let c = &constraints[c_idx];
                *slot = Some(WitnessGen::Product {
                    out,
                    left: c.a.clone(),
                    right: c.b.clone(),
                });
            });
    }

    pub(crate) fn merge_mul(&mut self, var: VarId, target: LinearCombination) {
        let (idx, wg_idx) = self
            .pending_mul
            .remove(&var)
            .expect("caller guarantees var is pending");
        // record operands so the product can be revived if referenced again (see `merged`)
        self.merged.insert(var, (wg_idx, idx));
        // The merged multiplication `a * b = target` is now a check, not a
        // definition — its output var is gone, so it gets no witness-gen Product
        // (`fill_products` skips merged outputs; the slot stays `None`).
        debug_assert!(self.witness_gen[wg_idx].is_none());
        let target = target.simplified();
        let note = note!(
            self,
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
