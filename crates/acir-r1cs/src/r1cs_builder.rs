//! Thin wrapper around Arkworks `ConstraintSystemRef<Fr>` providing the
//! variable bookkeeping we need during lowering.
//!
//! We maintain an explicit `BTreeMap<WitnessIndex, Variable>` so the same
//! circuit-shape allocation logic can run during setup (without witness
//! values) and during proving (with witness values).

use std::collections::BTreeMap;

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_relations::gr1cs::{ConstraintSystemRef, LinearCombination, SynthesisError, Variable};
use ark_relations::lc;

use crate::artifact::WitnessIndex;
use crate::witness::{CALLEE_NAMESPACE_STRIDE, WitnessMap};

/// Tracks the Arkworks `Variable` allocated for each ACIR witness.
pub struct R1csBuilder<'a> {
    cs: ConstraintSystemRef<Fr>,
    map: BTreeMap<WitnessIndex, Variable>,
    witness: Option<&'a WitnessMap<Fr>>,
    /// Auxiliary witness values injected by Call lowering. When
    /// inlining a callee circuit, we shift the callee's witness indices by
    /// a per-call offset and inject the shifted (index, value) pairs here
    /// so downstream `alloc_witness` lookups succeed without disturbing the
    /// main witness map.
    extra_witnesses: BTreeMap<WitnessIndex, Fr>,
    /// Next free offset for Call-namespace shifting. Each call site
    /// (top-level *or* nested) grabs `CALLEE_NAMESPACE_STRIDE` of fresh
    /// witness-index space and then bumps this counter. The first allocation
    /// returns `CALLEE_NAMESPACE_STRIDE` (so the main circuit's witnesses,
    /// which live in `[0, CALLEE_NAMESPACE_STRIDE)`, are never overlapped).
    next_call_offset: u32,
    /// Allocate witnesses lazily as we encounter them during lowering.
    /// `None` until the public-input pass has happened — until then we refuse
    /// to allocate.
    public_pass_done: bool,
    /// Active call-site predicate. When `Some(p)`, every constraint emitted
    /// via [`R1csBuilder::enforce`] is gated by `p` using the auxiliary-error
    /// trick: emit `A·B = C + e` plus `p·e = 0`, where `e = A·B − C` is a
    /// fresh witness. This makes every gadget (RANGE, SHA-256, Keccak,
    /// memory ops,...) work uniformly under a Call's predicate without
    /// per-gadget refactoring; the cost is roughly 2× the constraint count
    /// for code paths emitted while a predicate is active. Pushed/popped by
    /// [`R1csBuilder::push_predicate`] and the matching restore helper at
    /// Call-inlining sites in `lower::lower_call_at`.
    current_predicate: Option<Variable>,
}

impl<'a> R1csBuilder<'a> {
    pub fn new(cs: ConstraintSystemRef<Fr>, witness: Option<&'a WitnessMap<Fr>>) -> Self {
        Self {
            cs,
            map: BTreeMap::new(),
            witness,
            extra_witnesses: BTreeMap::new(),
            next_call_offset: CALLEE_NAMESPACE_STRIDE,
            public_pass_done: false,
            current_predicate: None,
        }
    }

    /// Install a new active predicate, returning the previous value so the
    /// caller can restore it via [`R1csBuilder::restore_predicate`]. While a
    /// predicate is installed, every `enforce` call is rewritten to its
    /// gated form (see `current_predicate` doc). Nested call sites should
    /// combine outer and inner predicates *before* pushing so the gating
    /// stays a single boolean variable.
    pub fn push_predicate(&mut self, predicate: Variable) -> Option<Variable> {
        let previous = self.current_predicate;
        self.current_predicate = Some(predicate);
        previous
    }

    /// Restore a predicate snapshot returned by [`R1csBuilder::push_predicate`].
    pub fn restore_predicate(&mut self, previous: Option<Variable>) {
        self.current_predicate = previous;
    }

    /// Temporarily clear the active predicate, returning the previous value
    /// so the caller can restore it via
    /// [`R1csBuilder::restore_predicate`]. Used by lowering paths that emit
    /// their own predicate-gated constraints (the explicit gating in
    /// `lower_assert_zero_gated`) so the builder's universal e-aux gating
    /// doesn't double up.
    pub fn take_predicate(&mut self) -> Option<Variable> {
        self.current_predicate.take()
    }

    /// Allocate a fresh witness-index offset for the next call site. Bumps the
    /// internal counter by [`CALLEE_NAMESPACE_STRIDE`] so the caller can shift
    /// the callee circuit's witnesses into a disjoint range. Returns
    /// `SynthesisError::Unsatisfiable` if the running counter would overflow
    /// `u32` (i.e. the program has more call sites — counting nested
    /// invocations — than `u32::MAX / CALLEE_NAMESPACE_STRIDE`, which is 255).
    pub fn alloc_call_offset(&mut self) -> Result<u32, SynthesisError> {
        let offset = self.next_call_offset;
        let next = offset
            .checked_add(CALLEE_NAMESPACE_STRIDE)
            .ok_or(SynthesisError::Unsatisfiable)?;
        self.next_call_offset = next;
        Ok(offset)
    }

    /// Inject (index → value) pairs into the auxiliary witness pool consulted
    /// by `alloc_witness` and `maybe_witness_value`. Used by Call lowering
    /// to supply the shifted callee witness map.
    pub fn inject_witnesses(&mut self, values: impl IntoIterator<Item = (WitnessIndex, Fr)>) {
        self.extra_witnesses.extend(values);
    }

    /// Look up the (pre-shift) callee witness map for function index `id`,
    /// if the proving-time witness stack carried one. Returns `None` in
    /// setup mode or for any single-function program.
    pub fn callee_witness_map(&self, id: u32) -> Option<&BTreeMap<WitnessIndex, Fr>> {
        self.witness.and_then(|w| w.callee(id))
    }

    pub fn constraint_system(&self) -> ConstraintSystemRef<Fr> {
        self.cs.clone()
    }

    pub fn variable_count(&self) -> usize {
        self.map.len()
    }

    pub fn finish_public_pass(&mut self) {
        self.public_pass_done = true;
    }

    /// Allocate a public input variable. Must be called during the public-input
    /// allocation pass (before [`R1csBuilder::finish_public_pass`]).
    pub fn alloc_public(&mut self, idx: WitnessIndex) -> Result<Variable, SynthesisError> {
        debug_assert!(
            !self.public_pass_done,
            "alloc_public after public_pass_done"
        );
        if let Some(v) = self.map.get(&idx) {
            return Ok(*v);
        }
        let value_fn = || self.lookup_witness(idx);
        let v = self.cs.new_input_variable(value_fn)?;
        self.map.insert(idx, v);
        Ok(v)
    }

    /// Allocate a private witness variable on demand, or return the existing
    /// allocation. Public inputs are pre-allocated separately and short-circuit
    /// here.
    pub fn alloc_witness(&mut self, idx: WitnessIndex) -> Result<Variable, SynthesisError> {
        if let Some(v) = self.map.get(&idx) {
            return Ok(*v);
        }
        let value_fn = || self.lookup_witness(idx);
        let v = self.cs.new_witness_variable(value_fn)?;
        self.map.insert(idx, v);
        Ok(v)
    }

    /// Allocate an auxiliary private witness whose value is computed from the
    /// supplied closure (which is only invoked during proving).
    pub fn alloc_aux<F>(&mut self, value_fn: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Fr, SynthesisError>,
    {
        self.cs.new_witness_variable(value_fn)
    }

    /// Enforce `a * b = c`. When a Call-site predicate is currently active
    /// (see [`R1csBuilder::push_predicate`]), the constraint is automatically
    /// rewritten to its gated form: allocate aux `e = A·B − C` (computed
    /// natively from the constraint system's current witness assignment in
    /// proving mode) and emit both `A·B = C + e` and `p·e = 0`. The result
    /// is that when `p == 0`, `e` is free and the original constraint is
    /// disabled; when `p == 1`, `e == 0` and the original constraint
    /// `A·B = C` is enforced exactly. Cost: one extra aux + one extra
    /// enforce per gated constraint (≈ 2× constraint count for predicated
    /// code paths).
    pub fn enforce(
        &self,
        a: LinearCombination<Fr>,
        b: LinearCombination<Fr>,
        c: LinearCombination<Fr>,
    ) -> Result<(), SynthesisError> {
        match self.current_predicate {
            None => self.cs.enforce_r1cs_constraint(|| a, || b, || c),
            Some(p) => self.enforce_gated(a, b, c, p),
        }
    }

    /// Emit the e-aux gated form of `a · b = c` under predicate `p`. See
    /// [`R1csBuilder::enforce`] for the soundness argument.
    ///
    /// Linear-only fast path: if both `a` and `b` are empty (the
    /// `0 · 0 = C` shape used for linear constraints — common in arithmetic
    /// expressions, range-recompose checks, and aliasing constraints), the
    /// e-aux trick collapses to a single `p · C = 0` row. Saves one aux +
    /// one R1CS constraint per linear assertion under predicate. Roughly
    /// halves the predicated constraint count for arithmetic-heavy
    /// callees.
    fn enforce_gated(
        &self,
        a: LinearCombination<Fr>,
        b: LinearCombination<Fr>,
        c: LinearCombination<Fr>,
        p: Variable,
    ) -> Result<(), SynthesisError> {
        if a.0.is_empty() && b.0.is_empty() {
            // Original constraint is `0 · 0 = C`, equivalent to `C = 0`.
            // Gated form: `p · C = 0`. When `p = 0`, the constraint is
            // satisfied for any value of `C`; when `p = 1`, `C = 0`.
            return self.cs.enforce_r1cs_constraint(
                || LinearCombination::from((Fr::one(), p)),
                || c,
                || lc!(),
            );
        }

        // Allocate `e = A·B − C`. The value closure runs only in proving
        // mode and reads variable assignments via `assigned_value`; both
        // operands and the right-hand side LCs reference variables that
        // were allocated before this enforce call, so their assignments
        // are already populated.
        let cs_for_closure = self.cs.clone();
        let a_clone = a.clone();
        let b_clone = b.clone();
        let c_clone = c.clone();
        let e = self.cs.new_witness_variable(move || {
            let a_val = eval_lc(&cs_for_closure, &a_clone)?;
            let b_val = eval_lc(&cs_for_closure, &b_clone)?;
            let c_val = eval_lc(&cs_for_closure, &c_clone)?;
            Ok(a_val * b_val - c_val)
        })?;

        // Modified original: `A · B = C + e` ⇔ `A · B - C - e = 0`.
        let mut c_plus_e = c;
        c_plus_e.0.push((Fr::one(), e));
        self.cs.enforce_r1cs_constraint(|| a, || b, || c_plus_e)?;

        // Gating: `p · e = 0`. When `p = 0`, `e` is unconstrained (so the
        // original A·B = C is disabled). When `p = 1`, `e = 0`, so the
        // modified original collapses to A·B = C exactly.
        self.cs.enforce_r1cs_constraint(
            || LinearCombination::from((Fr::one(), p)),
            || LinearCombination::from((Fr::one(), e)),
            || lc!(),
        )?;
        Ok(())
    }

    /// Zero linear combination.
    pub fn zero_lc(&self) -> LinearCombination<Fr> {
        lc!()
    }

    /// `coeff * one`.
    pub fn const_lc(&self, coeff: Fr) -> LinearCombination<Fr> {
        if coeff.is_zero() {
            lc!()
        } else {
            LinearCombination::from((coeff, Variable::One))
        }
    }

    fn lookup_witness(&self, idx: WitnessIndex) -> Result<Fr, SynthesisError> {
        if let Some(v) = self.extra_witnesses.get(&idx) {
            return Ok(*v);
        }
        Self::lookup(self.witness, idx)
    }

    fn lookup(
        witness: Option<&'a WitnessMap<Fr>>,
        idx: WitnessIndex,
    ) -> Result<Fr, SynthesisError> {
        match witness {
            None => Err(SynthesisError::AssignmentMissing),
            Some(map) => match map.get(&idx) {
                Some(v) => Ok(*v),
                None => Err(SynthesisError::AssignmentMissing),
            },
        }
    }

    /// Snapshot the values of two witnesses into a closure-friendly result.
    /// Used during lowering of multi-mul-term expressions to compute
    /// auxiliary `t = a * b` values without re-borrowing the builder. Uses
    /// the same lookup path as `alloc_witness` (extra_witnesses then the
    /// caller's WitnessMap), so Call-shifted callee witnesses resolve
    /// correctly.
    pub fn witness_value_snapshot(
        &self,
        a: WitnessIndex,
        b: WitnessIndex,
    ) -> Result<(Fr, Fr), SynthesisError> {
        let av = self.lookup_witness(a)?;
        let bv = self.lookup_witness(b)?;
        Ok((av, bv))
    }

    /// Look up an ACIR witness value, returning `None` in setup mode and
    /// `Some(value)` in proving mode. Returns `AssignmentMissing` only when
    /// the witness map is present but doesn't contain `idx`.
    pub fn maybe_witness_value(&self, idx: WitnessIndex) -> Result<Option<Fr>, SynthesisError> {
        if let Some(v) = self.extra_witnesses.get(&idx) {
            return Ok(Some(*v));
        }
        match self.witness {
            None => Ok(None),
            Some(map) => match map.get(&idx) {
                Some(v) => Ok(Some(*v)),
                None => Err(SynthesisError::AssignmentMissing),
            },
        }
    }

    /// Allocate a private witness with a known (optional) `Fr` value. The
    /// caller has already computed the value in proving mode; in setup mode
    /// the closure isn't invoked, so `None` is fine.
    pub fn alloc_with_value(&mut self, value: Option<Fr>) -> Result<Variable, SynthesisError> {
        self.cs
            .new_witness_variable(move || value.ok_or(SynthesisError::AssignmentMissing))
    }
}

/// Evaluate a [`LinearCombination`] against the constraint system's current
/// witness assignment. Used by [`R1csBuilder::enforce_gated`] inside the
/// `e = A·B − C` aux closure (which only runs in proving mode). Returns
/// [`SynthesisError::AssignmentMissing`] for any variable that hasn't been
/// assigned a value yet — by construction this shouldn't happen, because
/// every variable in the LC was allocated (and its value populated) before
/// the enforce call.
fn eval_lc(cs: &ConstraintSystemRef<Fr>, lc: &LinearCombination<Fr>) -> Result<Fr, SynthesisError> {
    let mut acc = Fr::zero();
    for (coeff, var) in &lc.0 {
        let val = cs
            .assigned_value(*var)
            .ok_or(SynthesisError::AssignmentMissing)?;
        acc += *coeff * val;
    }
    Ok(acc)
}
