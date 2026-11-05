//! `#[gadget]` calls as named templates, for the Lean export (`cargo xtask
//! lean-export`).
//!
//! The `gadget_begin`/`gadget_end` imports around a gadget's body tell the builder
//! where a call starts and ends; when recording, it keeps the call's name, its
//! inputs' and outputs' linear combinations, and the range of rows, witness ops
//! and variables between them. After lowering, each call becomes a
//! [`GadgetTemplate`]: those rows and hints with the call's variables renamed, so
//! the template is the call's exact R1CS, independent of where it sat.

use xark_ir::primitive::WitnessGen;
use xark_ir::{FieldConst, LinearCombination, R1csConstraint, VarId};

use crate::builder::Builder;
use crate::output::subst_witness_vars;

/// One recorded `#[gadget]` call.
pub(crate) struct GadgetCall {
    name: String,
    inputs: Vec<LinearCombination>,
    outputs: Vec<LinearCombination>,
    c0: usize,
    c1: usize,
    w0: usize,
    w1: usize,
    v0: VarId,
    v1: VarId,
    returned: bool,
    /// Why the recorded call isn't the call's exact R1CS, if it isn't.
    refused: Option<String>,
    /// The rows as the call left them, to catch a later rewrite of one (a
    /// caller's `require_eq` folded into the call's last product).
    rows: Vec<R1csConstraint>,
    /// The wasm call stack at `gadget_begin`, to name the call site.
    stack: Vec<(u32, u32)>,
    /// A decomposition outside any call, recorded as a `to_bits` call.
    decomposition: bool,
}

/// One recorded `#[gadget]` call: its template, or why its rows aren't one.
#[derive(Clone, Debug)]
pub struct RecordedCall {
    /// `module::function`.
    pub name: String,
    /// Where it was called: the calling function and its `file:line:col`.
    pub site: String,
    pub template: Result<GadgetTemplate, String>,
    /// The call's inputs and outputs over the circuit's own variables (empty when
    /// it never returned), and how many rows it emitted.
    pub inputs: Vec<LinearCombination>,
    pub outputs: Vec<LinearCombination>,
    pub rows: usize,
    /// How many variables it allocated.
    pub witnesses: u32,
    /// A bit decomposition the compiler made outside any `#[gadget]` call (an input's
    /// range check, a native bitwise op's bits), recorded as `xark::lang::to_bits`:
    /// its rows are that gadget's at its width.
    pub decomposition: bool,
    stack: Vec<(u32, u32)>,
}

/// A `#[gadget]` call's exact R1CS. Variables `0..plugs` are the ones its inputs
/// read (numbered in order of first appearance in `inputs`), `plugs..plugs +
/// witnesses` the ones it allocated, in allocation order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GadgetTemplate {
    /// `module::function`.
    pub name: String,
    pub plugs: u32,
    pub witnesses: u32,
    /// The parameters' field elements, in order, as `xark::Input` writes them.
    pub inputs: Vec<LinearCombination>,
    /// The result's field elements.
    pub outputs: Vec<LinearCombination>,
    /// The rows `a · b = c` it emitted, in order.
    pub rows: Vec<[LinearCombination; 3]>,
    /// The witness ops (hints) it emitted, in order: how the prover computes its
    /// variables.
    pub hints: Vec<WitnessGen>,
}

impl GadgetTemplate {
    /// The linear combination each of this template's plugs carries in `call`, when
    /// `call` is this template with them substituted: its inputs are this
    /// template's plug inputs with `call`'s linear combinations in their place, and
    /// its rows, hints and outputs are this template's with each plug replaced by
    /// its combination (over `call`'s variables), every linear combination reduced
    /// mod BN254's `r`. `None` when it isn't.
    pub fn substitution_of(
        &self,
        call: &GadgetTemplate,
    ) -> Option<Vec<(VarId, LinearCombination)>> {
        if call.inputs.len() != self.inputs.len() {
            return None;
        }
        let mut sub: Vec<(VarId, LinearCombination)> = Vec::new();
        for (mine, theirs) in self.inputs.iter().zip(&call.inputs) {
            let [t] = &mine.terms[..] else { return None };
            if !mine.constant.is_zero() || !t.coeff.is_one() || sub.iter().any(|(p, _)| *p == t.var)
            {
                return None;
            }
            sub.push((t.var, canonical_lc(theirs)));
        }
        sub.sort_by_key(|(p, _)| *p);
        (self.substituted(&sub, call.plugs).canonical() == call.canonical()).then_some(sub)
    }

    /// The constant plugs of `call`, when `call` is this template with constants
    /// for some plugs (the others plain variables or combinations, as in
    /// [`Self::substitution_of`]) and then folded the way the frontend folds: in hint
    /// order, each hint whose value is a constant or affine in the call's wires (a
    /// bit of a constant, XOR/OR/product with a constant operand) is dropped, its
    /// witness replaced by that combination everywhere, and every row the
    /// replacement leaves holding at all assignments (closed and true, or a linear
    /// identity) is dropped; the witnesses left are renumbered in order. This is
    /// `Formal/Template.lean`'s `inst` followed by `foldAt` once per folded witness.
    /// `None` when nothing folds or what is left isn't `call`; `Err` when a fold
    /// leaves a closed row that is false.
    pub fn folding_of(
        &self,
        call: &GadgetTemplate,
    ) -> Option<Result<Vec<(VarId, LinearCombination)>, String>> {
        if call.inputs.len() != self.inputs.len() || call.outputs.len() != self.outputs.len() {
            return None;
        }
        let mut sub: Vec<(VarId, LinearCombination)> = Vec::new();
        for (mine, theirs) in self.inputs.iter().zip(&call.inputs) {
            let [t] = &mine.terms[..] else { return None };
            if !mine.constant.is_zero() || !t.coeff.is_one() || sub.iter().any(|(p, _)| *p == t.var)
            {
                return None;
            }
            sub.push((t.var, canonical_lc(theirs)));
        }
        sub.sort_by_key(|(p, _)| *p);
        let mut t = self.substituted(&sub, call.plugs).canonical();
        let mut folded: Vec<VarId> = Vec::new();
        let mut i = 0;
        while i < t.hints.len() {
            let Some(folds) = affine_value(&t.hints[i]) else {
                i += 1;
                continue;
            };
            t.hints.remove(i);
            for (o, e) in folds {
                t = t.replaced(o, &e);
                folded.push(o);
            }
            let mut kept = Vec::with_capacity(t.rows.len());
            for r in std::mem::take(&mut t.rows) {
                match validity(&r) {
                    Some(true) => {}
                    Some(false) => {
                        return Some(Err("a fold leaves a closed row that is false".into()));
                    }
                    None => kept.push(r),
                }
            }
            t.rows = kept;
        }
        if folded.is_empty() {
            return None;
        }
        // A witness nothing reads or writes any more (add32's products by a
        // constant power of 2, all its bits folded) is not one the call allocates.
        let used = std::cell::RefCell::new(std::collections::BTreeSet::new());
        let note = |l: &LinearCombination| {
            used.borrow_mut().extend(l.terms.iter().map(|t| t.var));
            l.clone()
        };
        for l in t
            .inputs
            .iter()
            .chain(&t.outputs)
            .chain(t.rows.iter().flatten())
        {
            note(l);
        }
        for h in &t.hints {
            let write = |v: VarId| {
                used.borrow_mut().insert(v);
                v
            };
            subst_witness_vars(&mut h.clone(), &write, &note);
        }
        let used = used.into_inner();
        let left: Vec<VarId> = (call.plugs..call.plugs + self.witnesses)
            .filter(|v| !folded.contains(v) && used.contains(v))
            .collect();
        let plugs = call.plugs;
        let map = |v: VarId| {
            if v < plugs {
                v
            } else {
                plugs + left.iter().position(|&w| w == v).expect("a kept witness") as VarId
            }
        };
        let lc = |l: &LinearCombination| {
            let mut l = l.clone();
            for t in &mut l.terms {
                t.var = map(t.var);
            }
            canonical_lc(&l)
        };
        t.witnesses = left.len() as u32;
        t.inputs = t.inputs.iter().map(lc).collect();
        t.outputs = t.outputs.iter().map(lc).collect();
        t.rows = t.rows.iter().map(|r| r.each_ref().map(lc)).collect();
        for h in &mut t.hints {
            subst_witness_vars(h, &map, &lc);
        }
        (t.canonical() == call.canonical()).then_some(Ok(sub))
    }

    /// This template with variable `v` replaced by `e` in every linear combination.
    fn replaced(&self, v: VarId, e: &LinearCombination) -> GadgetTemplate {
        let lc = |l: &LinearCombination| {
            let Some(c) = l.terms.iter().find(|t| t.var == v).map(|t| t.coeff.clone()) else {
                return l.clone();
            };
            let mut l = l.clone();
            l.terms.retain(|t| t.var != v);
            canonical_lc(&(l + e.clone().scale(&c)))
        };
        let mut t = self.clone();
        t.inputs = t.inputs.iter().map(lc).collect();
        t.outputs = t.outputs.iter().map(lc).collect();
        t.rows = t.rows.iter().map(|r| r.each_ref().map(lc)).collect();
        for h in &mut t.hints {
            subst_witness_vars(h, &|x| x, &lc);
        }
        t
    }

    /// This template with each plug replaced by its combination in `sub` (over
    /// variables `0..plugs`) and its witnesses numbered after them.
    fn substituted(&self, sub: &[(VarId, LinearCombination)], plugs: VarId) -> GadgetTemplate {
        let map = |v: VarId| v - self.plugs + plugs;
        let lc = |l: &LinearCombination| {
            let mut out = LinearCombination {
                constant: l.constant.clone(),
                terms: Vec::new(),
            };
            for t in &l.terms {
                match sub.iter().find(|(p, _)| *p == t.var) {
                    Some((_, e)) => {
                        out.constant = out.constant.add(&t.coeff.mul(&e.constant));
                        out.terms.extend(e.terms.iter().map(|u| xark_ir::Term {
                            coeff: t.coeff.mul(&u.coeff),
                            var: u.var,
                        }));
                    }
                    None => out.terms.push(xark_ir::Term {
                        coeff: t.coeff.clone(),
                        var: map(t.var),
                    }),
                }
            }
            out
        };
        GadgetTemplate {
            name: self.name.clone(),
            plugs,
            witnesses: self.witnesses,
            inputs: self.inputs.iter().map(lc).collect(),
            outputs: self.outputs.iter().map(lc).collect(),
            rows: self.rows.iter().map(|r| r.each_ref().map(lc)).collect(),
            hints: self
                .hints
                .iter()
                .map(|h| {
                    let mut h = h.clone();
                    subst_witness_vars(&mut h, &map, &lc);
                    h
                })
                .collect(),
        }
    }

    /// Every linear combination reduced mod `r` ([`canonical_lc`]).
    fn canonical(&self) -> GadgetTemplate {
        let mut t = self.clone();
        t.inputs = t.inputs.iter().map(canonical_lc).collect();
        t.outputs = t.outputs.iter().map(canonical_lc).collect();
        t.rows = t
            .rows
            .iter()
            .map(|r| r.each_ref().map(canonical_lc))
            .collect();
        for h in &mut t.hints {
            subst_witness_vars(h, &|v| v, &canonical_lc);
        }
        t
    }
}

/// What a hint computes when it is a constant or affine in the template's other
/// variables (its operands canonical): each written witness with that combination.
fn affine_value(h: &WitnessGen) -> Option<Vec<(VarId, LinearCombination)>> {
    let konst = |c: FieldConst| LinearCombination {
        constant: reduce(&c),
        terms: Vec::new(),
    };
    let bit = |x: &LinearCombination, i: u32| {
        let v = x.constant.big();
        konst(FieldConst::from_i64(
            ((v >> i) & num_bigint::BigInt::from(1u8) == num_bigint::BigInt::from(1u8)) as i64,
        ))
    };
    // `a op b` with one operand the constant `k`: `k·…` and the other operand.
    let one_constant = |a: &LinearCombination, b: &LinearCombination| {
        if a.is_constant() {
            Some((a.constant.clone(), b.clone()))
        } else if b.is_constant() {
            Some((b.constant.clone(), a.clone()))
        } else {
            None
        }
    };
    let e = match h {
        WitnessGen::Bit { out, input, index } if input.is_constant() => {
            vec![(*out, bit(input, *index))]
        }
        WitnessGen::Bits { outs, input } if input.is_constant() => outs
            .iter()
            .enumerate()
            .map(|(i, &o)| (o, bit(input, i as u32)))
            .collect(),
        // `k ⊕ x = k + (1 − 2k)·x`.
        WitnessGen::Xor { out, a, b } => {
            let (k, x) = one_constant(a, b)?;
            let slope = FieldConst::one().add(&k.mul(&FieldConst::from_i64(-2)));
            vec![(*out, konst(k) + x.scale(&slope))]
        }
        // `k ∨ x = k + (1 − k)·x`.
        WitnessGen::Or { out, a, b } => {
            let (k, x) = one_constant(a, b)?;
            let slope = FieldConst::one().add(&k.neg());
            vec![(*out, konst(k) + x.scale(&slope))]
        }
        WitnessGen::Product { out, left, right } => {
            let (k, x) = one_constant(left, right)?;
            vec![(*out, x.scale(&k))]
        }
        _ => return None,
    };
    Some(e.into_iter().map(|(o, l)| (o, canonical_lc(&l))).collect())
}

/// Whether a row holds at every assignment (`Some(true)`), at none because it is
/// closed and false (`Some(false)`), or neither as far as a linear check tells.
fn validity(r: &[LinearCombination; 3]) -> Option<bool> {
    let [a, b, c] = r;
    let lin =
        |k: &FieldConst, x: &LinearCombination| canonical_lc(&(x.clone().scale(k) - c.clone()));
    let d = if a.is_constant() {
        lin(&a.constant, b)
    } else if b.is_constant() {
        lin(&b.constant, a)
    } else {
        return None;
    };
    if d.is_zero() {
        Some(true)
    } else if d.is_constant() {
        Some(false)
    } else {
        None
    }
}

/// `l` reduced mod `r`: coefficients and constant in `[0, r)`, like terms merged,
/// zero terms dropped, terms sorted.
pub fn canonical_lc(l: &LinearCombination) -> LinearCombination {
    let mut l = l.clone();
    for t in &mut l.terms {
        t.coeff = reduce(&t.coeff);
    }
    let mut l = l.simplified();
    l.constant = reduce(&l.constant);
    for t in &mut l.terms {
        t.coeff = reduce(&t.coeff);
    }
    l.terms.retain(|t| !t.coeff.is_zero());
    l
}

/// `c mod r` in `[0, r)`, for BN254's scalar field.
fn reduce(c: &FieldConst) -> FieldConst {
    static R: std::sync::OnceLock<num_bigint::BigInt> = std::sync::OnceLock::new();
    let r = R.get_or_init(|| {
        let r = xark_ir::FieldSpec::bn254()
            .modulus_decimal
            .expect("bn254 has a modulus");
        r.parse().expect("a decimal modulus")
    });
    let v = c.big() % r;
    FieldConst::from_bigint(if v.sign() == num_bigint::Sign::Minus {
        v + r
    } else {
        v
    })
}

impl Builder {
    fn counters(&self) -> (usize, usize, VarId) {
        (
            self.constraints.len(),
            self.witness_gen.len(),
            self.next_var_id,
        )
    }

    /// The guest asked whether calls are recorded: it may now pass a call's inputs
    /// or result.
    pub(crate) fn gadget_mark(&mut self) {
        self.gadget_mark = self.counters();
    }

    /// Whether anything was emitted since [`Self::gadget_mark`].
    pub(crate) fn gadget_marked_changed(&self) -> bool {
        self.counters() != self.gadget_mark
    }

    pub(crate) fn gadget_begin(
        &mut self,
        name: String,
        inputs: Vec<LinearCombination>,
        refused: Option<String>,
        stack: Vec<(u32, u32)>,
    ) {
        self.gadget_stack.push(self.gadget_calls.len());
        let (c0, w0, v0) = self.counters();
        self.gadget_calls.push(GadgetCall {
            name,
            inputs,
            outputs: Vec::new(),
            c0,
            c1: 0,
            w0,
            w1: 0,
            v0,
            v1: 0,
            returned: false,
            refused,
            rows: Vec::new(),
            stack,
            decomposition: false,
        });
    }

    pub(crate) fn gadget_counters(&self) -> (usize, usize, VarId) {
        self.counters()
    }

    /// A decomposition of `value` into `bits` that started at `start` (rows,
    /// witness ops, variables) and ends now, recorded as a `to_bits` call.
    pub(crate) fn record_decomposition(
        &mut self,
        (c0, w0, v0): (usize, usize, VarId),
        value: LinearCombination,
        bits: Vec<LinearCombination>,
        refused: Option<String>,
    ) {
        let (c1, w1, v1) = self.counters();
        self.gadget_calls.push(GadgetCall {
            name: "xark::lang::to_bits".into(),
            inputs: vec![value],
            outputs: bits,
            c0,
            c1,
            w0,
            w1,
            v0,
            v1,
            returned: true,
            refused,
            rows: self.constraints[c0..c1].to_vec(),
            stack: self.site_stack.clone(),
            decomposition: true,
        });
    }

    /// The call returned; it ended at the last mark (before its result was passed).
    pub(crate) fn gadget_end(
        &mut self,
        outputs: Vec<LinearCombination>,
        refused: Option<String>,
    ) -> Result<(), String> {
        let i = self
            .gadget_stack
            .pop()
            .ok_or("`gadget_end` without a `gadget_begin`")?;
        let (c1, w1, v1) = self.gadget_mark;
        let call = &mut self.gadget_calls[i];
        call.outputs = outputs;
        (call.c1, call.w1, call.v1) = (c1, w1, v1);
        call.returned = true;
        call.refused = call.refused.take().or(refused);
        call.rows = self.constraints[call.c0..call.c1].to_vec();
        Ok(())
    }

    /// Row `idx` was rewritten by a `require_eq` merge: a row from before an open
    /// call that the call's own equality now completes isn't in its template.
    pub(crate) fn gadget_merged(&mut self, idx: usize) {
        for &i in &self.gadget_stack {
            let call = &mut self.gadget_calls[i];
            if idx < call.c0 && call.refused.is_none() {
                call.refused =
                    Some("a `require_eq` in it folded into a row from before the call".into());
            }
        }
    }
}

/// Every recorded call as a template, or why it isn't one. Runs once the products'
/// witness ops are filled in, before anything renumbers variables (a template's
/// variables are its own, so a renumbering wouldn't change it).
pub(crate) fn extract(b: &Builder) -> Vec<RecordedCall> {
    if b.gadget_calls.is_empty() {
        return Vec::new();
    }
    // A product merged into a `require_eq` whose output is still read gets its row
    // back at the end of the circuit (`output::finish`), outside its call.
    let referenced: std::collections::HashSet<VarId> = b
        .constraints
        .iter()
        .flat_map(|c| [&c.a, &c.b, &c.c])
        .flat_map(|lc| lc.terms.iter().map(|t| t.var))
        .collect();
    let revived: Vec<usize> = b
        .merged
        .iter()
        .filter(|(out, _)| referenced.contains(out))
        .map(|(_, &(_, row))| row)
        .collect();
    b.gadget_calls
        .iter()
        .map(|c| RecordedCall {
            name: c.name.clone(),
            site: String::new(),
            template: template(b, c, &revived),
            inputs: c.inputs.clone(),
            outputs: c.outputs.clone(),
            rows: c.c1.saturating_sub(c.c0),
            witnesses: c.v1.saturating_sub(c.v0),
            decomposition: c.decomposition,
            stack: c.stack.clone(),
        })
        .collect()
}

/// When recording, the rows that can pin a wire to `{0, 1}`, reduced mod `r`
/// ([`canonical_lc`]): `x · x = x`, `x · (x − 1) = 0` (either factor first), and
/// `a · b = v` for a single variable `v` (a bit when `a` and `b` are).
/// `lean-export --coverage` decides which wires they pin. Rows are never dropped
/// after this, so each is in the circuit.
pub(crate) fn bit_rows(b: &Builder) -> Vec<[LinearCombination; 3]> {
    if b.gadget_calls.is_empty() {
        return Vec::new();
    }
    b.constraints
        .iter()
        .filter_map(|r| {
            let row = [&r.a, &r.b, &r.c].map(canonical_lc);
            let [a, x, c] = &row;
            let wire = matches!(&c.terms[..], [t] if t.coeff.is_one()) && c.constant.is_zero();
            (!a.is_constant() && !x.is_constant() && (wire || c.is_zero() || a == c)).then_some(row)
        })
        .collect()
}

/// Name each call's site: the frame that called the gadget function, with its
/// source location.
pub(crate) fn locate(calls: &mut [RecordedCall], r: &mut crate::debuginfo::Resolver<'_>) {
    for call in calls {
        let frames = r.stack(&call.stack);
        // Short names: an inlined frame has the function's own name (`add32`), a
        // call its path (`xark_bits::add32`), and inlining varies by rustc.
        use crate::debuginfo::short_name;
        let gadget = short_name(&call.name);
        // A decomposition outside any call: the innermost frame made it.
        let caller = if call.decomposition {
            frames.last()
        } else {
            frames
                .iter()
                .rposition(|f| short_name(&f.function) == gadget)
                .and_then(|i| i.checked_sub(1))
                .map(|i| &frames[i])
        };
        call.site = match caller {
            Some(f) => format!(
                "{} ({}:{}:{})",
                short_name(&f.function),
                f.file.as_deref().unwrap_or("?"),
                f.line,
                f.col
            ),
            None => "an unknown site (no frame calls the gadget)".into(),
        };
    }
}

fn template(b: &Builder, call: &GadgetCall, revived: &[usize]) -> Result<GadgetTemplate, String> {
    let fail = |why: &str| Err(format!("`{}` can't be exported: {why}", call.name));
    if !call.returned {
        return fail("the call never returned");
    }
    if let Some(why) = &call.refused {
        return fail(why);
    }
    if let Some(why) = &b.gadget_tainted {
        return fail(&format!(
            "another call in this circuit failed to record exactly ({why}), which \
             changes the rows and memos around it"
        ));
    }
    if revived.iter().any(|r| (call.c0..call.c1).contains(r)) {
        return fail(
            "a product it folded into a `require_eq` is read again, so its row is \
             re-emitted after the call",
        );
    }
    if b.constraints[call.c0..call.c1]
        .iter()
        .zip(&call.rows)
        .any(|(now, then)| (&now.a, &now.b, &now.c) != (&then.a, &then.b, &then.c))
    {
        return fail(
            "a row was rewritten after the call returned (a caller's `require_eq` folded into it)",
        );
    }
    let mut plugs: Vec<VarId> = Vec::new();
    for lc in &call.inputs {
        for t in &lc.terms {
            if t.var < call.v0 && !plugs.contains(&t.var) {
                plugs.push(t.var);
            }
        }
    }
    let n = plugs.len() as VarId;
    let stray = std::cell::Cell::new(None);
    let map = |v: VarId| -> VarId {
        if (call.v0..call.v1).contains(&v) {
            return n + (v - call.v0);
        }
        match plugs.iter().position(|&p| p == v) {
            Some(i) => i as VarId,
            None => {
                stray.set(Some(v));
                0
            }
        }
    };
    // Terms in renamed order: a sum's order is the original variables', which a
    // permutation of the inputs (a rotation's rewiring) changes without changing it.
    let map_lc = |lc: &LinearCombination| {
        let mut lc = lc.clone();
        for t in &mut lc.terms {
            t.var = map(t.var);
        }
        lc.terms.sort_by_key(|t| t.var);
        lc
    };
    let t = GadgetTemplate {
        name: call.name.clone(),
        plugs: n,
        witnesses: call.v1 - call.v0,
        inputs: call.inputs.iter().map(map_lc).collect(),
        outputs: call.outputs.iter().map(map_lc).collect(),
        rows: b.constraints[call.c0..call.c1]
            .iter()
            .map(|c| [map_lc(&c.a), map_lc(&c.b), map_lc(&c.c)])
            .collect(),
        hints: b.witness_gen[call.w0..call.w1]
            .iter()
            .flatten()
            .map(|w| {
                let mut w = w.clone();
                subst_witness_vars(&mut w, &map, &map_lc);
                w
            })
            .collect(),
    };
    match stray.get() {
        Some(v) if v >= call.v1 => fail(&format!(
            "it reads variable {v}, allocated after it returned"
        )),
        Some(v) => fail(&format!(
            "it reads variable {v}, which none of its inputs is (a value from outside \
             the call: a reused product, a cached decomposition)"
        )),
        None => Ok(t),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lc(c: i64, terms: &[(i64, VarId)]) -> LinearCombination {
        LinearCombination {
            constant: FieldConst::from_i64(c),
            terms: terms
                .iter()
                .map(|&(k, var)| xark_ir::Term {
                    coeff: FieldConst::from_i64(k),
                    var,
                })
                .collect(),
        }
    }

    /// `x · w = w` on plug `x` and witness `w`, and the call with `x := c` whose
    /// row's constant is `row`.
    fn proven_and_call(c: i64, row: i64) -> (GadgetTemplate, GadgetTemplate) {
        let t = |plugs, input, a| GadgetTemplate {
            name: "g".into(),
            plugs,
            witnesses: 1,
            inputs: vec![input],
            outputs: vec![lc(0, &[(1, plugs)])],
            rows: vec![[a, lc(0, &[(1, plugs)]), lc(0, &[(1, plugs)])]],
            hints: vec![],
        };
        (
            t(1, lc(0, &[(1, 0)]), lc(0, &[(1, 0)])),
            t(0, lc(c, &[]), lc(row, &[])),
        )
    }

    #[test]
    fn a_tampered_constant_plug_is_not_covered() {
        let (proven, call) = proven_and_call(3, 3);
        assert_eq!(proven.substitution_of(&call), Some(vec![(0, lc(3, &[]))]));
        let (proven, tampered) = proven_and_call(3, 4);
        assert_eq!(proven.substitution_of(&tampered), None);
    }

    /// Hint `w := bit 0 of x`, rows `w · w = w` and `w · 1 = x` (so `x` must be a
    /// bit): with `x := 1` the hint folds to `1` and both rows close true, leaving
    /// the empty call; with `x := 2` it folds to `0` and `0 · 1 = 2` is a closed row
    /// that is false, which no production call can be (the frontend refuses to
    /// compile one), so the fold must fail rather than drop it.
    #[test]
    fn a_fold_that_closes_a_false_row_fails() {
        let proven = GadgetTemplate {
            name: "g".into(),
            plugs: 1,
            witnesses: 1,
            inputs: vec![lc(0, &[(1, 0)])],
            outputs: vec![lc(0, &[(1, 1)])],
            rows: vec![
                [lc(0, &[(1, 1)]), lc(0, &[(1, 1)]), lc(0, &[(1, 1)])],
                [lc(0, &[(1, 1)]), lc(1, &[]), lc(0, &[(1, 0)])],
            ],
            hints: vec![WitnessGen::Bit {
                out: 1,
                input: lc(0, &[(1, 0)]),
                index: 0,
            }],
        };
        let call = |x: i64, out: i64| GadgetTemplate {
            name: "g".into(),
            plugs: 0,
            witnesses: 0,
            inputs: vec![lc(x, &[])],
            outputs: vec![lc(out, &[])],
            rows: vec![],
            hints: vec![],
        };
        assert_eq!(
            proven.folding_of(&call(1, 1)),
            Some(Ok(vec![(0, lc(1, &[]))]))
        );
        assert!(matches!(proven.folding_of(&call(2, 0)), Some(Err(_))));
    }
}
