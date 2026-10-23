//! Streaming R1CS: the variable-ordering contract and chunked row sources.
//!
//! The prover never holds the constraint system. It asks a [`ConstraintSource`]
//! for contiguous row *windows*, each expanded just-in-time into a flat
//! [`RowChunk`] (CSR: column indices + `Fr` coefficients), evaluates it against the
//! witness, and drops it before the next.
//!
//! ## The ordering contract
//!
//! Proving-key points are indexed by *assignment position*, and the QAP domain by
//! *row position*, exactly as arkworks' `gr1cs` allocated them when the key was
//! generated (via `xark_prover::XarkCircuit`). [`VarLayout`] reproduces that
//! allocation: position 0 is the constant `1`; then every `Public` variable in id
//! order; then every other variable in id order. Rows keep source order. Any
//! deviation pairs a witness value with the wrong key point and yields a proof
//! that fails verification — `tests/prover.rs` pins this against arkworks
//! (`ordering_contract_matches_arkworks_allocation`, `reordering_variables_breaks_the_proof`).

use std::collections::BTreeMap;
use std::ops::Range;

use ark_bn254::Fr;
use ark_ff::{PrimeField, Zero};
use rayon::prelude::*;
use xark_ir::function_decode::ReducedRowStream;
use xark_ir::r1cs_stream::RowFile;
use xark_ir::{FieldConst, LinearCombination, R1csProgram, VarId, Visibility};

/// IR variable id → assignment position, matching arkworks' allocation order.
#[derive(Clone, Debug)]
pub struct VarLayout {
    /// `pos[id]` = assignment position (`u32::MAX` = no such variable).
    pos: Vec<u32>,
    /// `ids[p-1]` = IR id at assignment position `p ≥ 1`.
    ids: Vec<VarId>,
    num_instance: usize,
}

impl VarLayout {
    /// Build from `(id, is_public)` pairs (any order; ids must be distinct).
    pub fn new(vars: impl IntoIterator<Item = (VarId, bool)>) -> Self {
        let mut vars: Vec<(VarId, bool)> = vars.into_iter().collect();
        vars.sort_unstable_by_key(|v| v.0);
        let max_id = vars.last().map_or(0, |v| v.0 as usize + 1);
        let mut pos = vec![u32::MAX; max_id];
        let mut ids = Vec::with_capacity(vars.len());
        for &(id, public) in &vars {
            if public {
                ids.push(id);
            }
        }
        let num_instance = ids.len() + 1;
        for &(id, public) in &vars {
            if !public {
                ids.push(id);
            }
        }
        for (p, &id) in ids.iter().enumerate() {
            pos[id as usize] = p as u32 + 1;
        }
        VarLayout {
            pos,
            ids,
            num_instance,
        }
    }

    /// The layout `XarkCircuit` allocates for `prog`.
    pub fn from_program(prog: &R1csProgram) -> Self {
        Self::new(
            prog.variables
                .iter()
                .map(|v| (v.id, v.visibility == Visibility::Public)),
        )
    }

    /// Instance variables, including the constant `1`.
    pub fn num_instance(&self) -> usize {
        self.num_instance
    }

    /// Witness (aux) variables.
    pub fn num_witness(&self) -> usize {
        self.ids.len() + 1 - self.num_instance
    }

    /// Total assignment length (`1 + vars`).
    pub fn num_vars(&self) -> usize {
        self.ids.len() + 1
    }

    /// Assignment position of IR var `id`, if it is allocated.
    #[inline]
    pub fn position(&self, id: VarId) -> Option<usize> {
        match self.pos.get(id as usize) {
            Some(&p) if p != u32::MAX => Some(p as usize),
            _ => None,
        }
    }

    /// The full assignment `z` (`z[0] = 1`), reading each variable's value by id.
    /// Unassigned variables are zero (as in `XarkCircuit`).
    pub fn assignment(&self, value: impl Fn(VarId) -> Option<Fr> + Sync) -> Vec<Fr> {
        let mut z = Vec::with_capacity(self.num_vars());
        z.push(Fr::from(1u64));
        z.par_extend(
            self.ids
                .par_iter()
                .map(|&id| value(id).unwrap_or_else(Fr::zero)),
        );
        z
    }

    /// The full assignment from a solved `VarId → Fr` map.
    pub fn assignment_from_map(&self, assign: &BTreeMap<VarId, Fr>) -> Vec<Fr> {
        self.assignment(|id| assign.get(&id).copied())
    }
}

/// A window of rows expanded into flat CSR form: for row `i` and matrix `m`
/// (0 = A, 1 = B, 2 = C) the terms are `cols/coeffs[offsets[3i+m]..offsets[3i+m+1]]`.
/// A linear combination's constant is a term on column 0 (the constant `1`).
#[derive(Default, Debug, Clone)]
pub struct RowChunk {
    /// Global index of this chunk's first row.
    pub first_row: usize,
    offsets: Vec<u32>,
    cols: Vec<u32>,
    coeffs: Vec<Fr>,
}

impl RowChunk {
    pub fn clear(&mut self, first_row: usize) {
        self.first_row = first_row;
        self.offsets.clear();
        self.offsets.push(0);
        self.cols.clear();
        self.coeffs.clear();
    }

    pub fn rows(&self) -> usize {
        self.offsets.len().saturating_sub(1) / 3
    }

    /// Total stored terms (a memory/volume probe).
    pub fn nnz(&self) -> usize {
        self.cols.len()
    }

    /// Terms of matrix `m` in local row `row`.
    #[inline]
    pub fn terms(&self, row: usize, m: usize) -> (&[u32], &[Fr]) {
        let k = 3 * row + m;
        let r = self.offsets[k] as usize..self.offsets[k + 1] as usize;
        (&self.cols[r.clone()], &self.coeffs[r])
    }

    /// `⟨M_row, z⟩` for matrix `m`.
    #[inline]
    pub fn eval(&self, row: usize, m: usize, z: &[Fr]) -> Fr {
        let (cols, coeffs) = self.terms(row, m);
        let mut acc = Fr::zero();
        for (&c, k) in cols.iter().zip(coeffs) {
            acc += z[c as usize] * k;
        }
        acc
    }

    /// Append one linear combination as raw `(assignment position, coefficient)`
    /// terms (three calls make a row: A, B, C).
    pub fn push_lc(&mut self, terms: impl IntoIterator<Item = (u32, Fr)>) {
        for (c, k) in terms {
            self.cols.push(c);
            self.coeffs.push(k);
        }
        self.offsets.push(self.cols.len() as u32);
    }

    /// Append one `a·b = c` row, mapping IR vars through `layout`.
    pub fn push_row(
        &mut self,
        lcs: [&LinearCombination; 3],
        layout: &VarLayout,
        conv: &mut CoeffCache,
    ) {
        for lc in lcs {
            if !lc.constant.is_zero() {
                self.cols.push(0);
                self.coeffs.push(conv.fr(&lc.constant));
            }
            for t in &lc.terms {
                let p = layout
                    .position(t.var)
                    .unwrap_or_else(|| panic!("constraint references unallocated var {}", t.var));
                self.cols.push(p as u32);
                self.coeffs.push(conv.fr(&t.coeff));
            }
            self.offsets.push(self.cols.len() as u32);
        }
    }
}

/// `FieldConst → Fr` with a per-window cache for big (non-`i64`) constants —
/// non-native circuits reuse a few thousand ~254-bit limb constants millions of
/// times.
#[derive(Default)]
pub struct CoeffCache {
    big: BTreeMap<FieldConst, Fr>,
}

impl CoeffCache {
    #[inline]
    pub fn fr(&mut self, fc: &FieldConst) -> Fr {
        if let Some(n) = fc.as_i64() {
            let mag = Fr::from(n.unsigned_abs());
            return if n < 0 { -mag } else { mag };
        }
        if let Some(f) = self.big.get(fc) {
            return *f;
        }
        let (sign, bytes) = fc.big().to_bytes_le();
        let mag = Fr::from_le_bytes_mod_order(&bytes);
        let f = if sign == num_bigint::Sign::Minus {
            -mag
        } else {
            mag
        };
        self.big.insert(fc.clone(), f);
        f
    }
}

/// A contiguous run of rows plus the source-specific handle that expands it.
#[derive(Clone, Debug)]
pub struct Window {
    pub rows: Range<usize>,
    /// Source-defined (row range for a program, item range for bytecode).
    pub handle: Range<usize>,
}

/// Anything that can enumerate the constraint rows, in order, window by window.
pub trait ConstraintSource: Sync {
    fn layout(&self) -> &VarLayout;
    fn num_constraints(&self) -> usize;
    /// Partition all rows, in order, into contiguous windows of roughly
    /// `rows_hint` rows (a window may be larger if the source can't split finer).
    fn windows(&self, rows_hint: usize) -> Vec<Window>;
    /// Expand one window into `out` (cleared first).
    fn expand(&self, w: &Window, out: &mut RowChunk);
    /// Optionally evaluate a window's rows directly (`outs[m][i] = ⟨M_i, z⟩` for
    /// the window's `i`-th row) without expanding it; `false` = not supported, use
    /// [`expand`](Self::expand).
    fn eval_window(&self, _w: &Window, _z: &[Fr], _outs: [Option<&mut [Fr]>; 3]) -> bool {
        false
    }
    /// The transpose: `outs[m][p] += Σ_rows w[row] · M[row][p]` for every
    /// assignment position `p` (position 0 is the constant `1`). Used by setup to
    /// evaluate each variable's QAP polynomials. Sequential; never holds more
    /// than one window.
    fn transpose_eval(&self, w: &[Fr], outs: [&mut [Fr]; 3]) {
        assert_eq!(w.len(), self.num_constraints());
        let mut chunk = RowChunk::default();
        let [oa, ob, oc] = outs;
        let mut outs = [oa, ob, oc];
        for win in self.windows(1 << 14) {
            self.expand(&win, &mut chunk);
            for i in 0..chunk.rows() {
                let wr = w[win.rows.start + i];
                if wr.is_zero() {
                    continue;
                }
                for (m, out) in outs.iter_mut().enumerate() {
                    let (cols, ks) = chunk.terms(i, m);
                    for (&c, k) in cols.iter().zip(ks) {
                        out[c as usize] += wr * k;
                    }
                }
            }
        }
    }
}

impl<T: ConstraintSource + ?Sized> ConstraintSource for &T {
    fn transpose_eval(&self, w: &[Fr], outs: [&mut [Fr]; 3]) {
        (**self).transpose_eval(w, outs)
    }
    fn eval_window(&self, w: &Window, z: &[Fr], outs: [Option<&mut [Fr]>; 3]) -> bool {
        (**self).eval_window(w, z, outs)
    }
    fn layout(&self) -> &VarLayout {
        (**self).layout()
    }
    fn num_constraints(&self) -> usize {
        (**self).num_constraints()
    }
    fn windows(&self, rows_hint: usize) -> Vec<Window> {
        (**self).windows(rows_hint)
    }
    fn expand(&self, w: &Window, out: &mut RowChunk) {
        (**self).expand(w, out)
    }
}

impl<T: ConstraintSource + ?Sized> ConstraintSource for Box<T> {
    fn transpose_eval(&self, w: &[Fr], outs: [&mut [Fr]; 3]) {
        (**self).transpose_eval(w, outs)
    }
    fn eval_window(&self, w: &Window, z: &[Fr], outs: [Option<&mut [Fr]>; 3]) -> bool {
        (**self).eval_window(w, z, outs)
    }
    fn layout(&self) -> &VarLayout {
        (**self).layout()
    }
    fn num_constraints(&self) -> usize {
        (**self).num_constraints()
    }
    fn windows(&self, rows_hint: usize) -> Vec<Window> {
        (**self).windows(rows_hint)
    }
    fn expand(&self, w: &Window, out: &mut RowChunk) {
        (**self).expand(w, out)
    }
}

/// The first row `i` with `⟨A_i, z⟩·⟨B_i, z⟩ ≠ ⟨C_i, z⟩`, or `None` when `z`
/// satisfies every row. Sequential, one window at a time: for telling why a
/// proof failed its self-check (a bad witness, or a key for another circuit),
/// not for the proving path.
pub fn first_unsatisfied<S: ConstraintSource + ?Sized>(src: &S, z: &[Fr]) -> Option<usize> {
    let mut chunk = RowChunk::default();
    for w in src.windows(1 << 14) {
        src.expand(&w, &mut chunk);
        for i in 0..chunk.rows() {
            if chunk.eval(i, 0, z) * chunk.eval(i, 1, z) != chunk.eval(i, 2, z) {
                return Some(w.rows.start + i);
            }
        }
    }
    None
}

/// Evaluate `⟨M_i, z⟩` for every row into the requested output vectors
/// (`outs[m]` for matrix `m`; each at least `num_constraints` long), streaming the
/// rows window-by-window in parallel. Peak extra memory: one [`RowChunk`] per
/// worker.
pub fn eval_rows<S: ConstraintSource + ?Sized>(
    src: &S,
    z: &[Fr],
    rows_hint: usize,
    outs: [Option<&mut [Fr]>; 3],
) {
    let windows = src.windows(rows_hint);
    // Split each requested output into per-window disjoint slices.
    let mut per_window: Vec<[Option<&mut [Fr]>; 3]> =
        (0..windows.len()).map(|_| [None, None, None]).collect();
    for (m, out) in outs.into_iter().enumerate() {
        let Some(mut rest) = out else { continue };
        let mut cursor = 0usize;
        for (w, slot) in windows.iter().zip(per_window.iter_mut()) {
            let (_, tail) = rest.split_at_mut(w.rows.start - cursor);
            let (mine, tail) = tail.split_at_mut(w.rows.len());
            slot[m] = Some(mine);
            rest = tail;
            cursor = w.rows.end;
        }
    }
    windows
        .par_iter()
        .zip(per_window.par_iter_mut())
        .for_each_init(RowChunk::default, |chunk, (w, slots)| {
            let [s0, s1, s2] = slots;
            if src.eval_window(
                w,
                z,
                [s0.as_deref_mut(), s1.as_deref_mut(), s2.as_deref_mut()],
            ) {
                return;
            }
            src.expand(w, chunk);
            debug_assert_eq!(chunk.rows(), w.rows.len());
            for (m, slot) in slots.iter_mut().enumerate() {
                if let Some(out) = slot {
                    for (i, o) in out.iter_mut().enumerate() {
                        *o = chunk.eval(i, m, z);
                    }
                }
            }
        });
}

/// Rows from an in-memory [`R1csProgram`] (e.g. the boundary-minimized circuit or
/// its setup cache): still evaluated chunk-by-chunk, so no second copy (arkworks'
/// `gr1cs` matrices + LC maps) is ever built.
pub struct ProgramSource<'a> {
    prog: &'a R1csProgram,
    layout: VarLayout,
}

impl<'a> ProgramSource<'a> {
    pub fn new(prog: &'a R1csProgram) -> Self {
        ProgramSource {
            layout: VarLayout::from_program(prog),
            prog,
        }
    }
}

impl ConstraintSource for ProgramSource<'_> {
    fn layout(&self) -> &VarLayout {
        &self.layout
    }
    fn num_constraints(&self) -> usize {
        self.prog.constraints.len()
    }
    fn windows(&self, rows_hint: usize) -> Vec<Window> {
        let n = self.prog.constraints.len();
        let step = rows_hint.max(1);
        (0..n)
            .step_by(step)
            .map(|s| {
                let r = s..n.min(s + step);
                Window {
                    rows: r.clone(),
                    handle: r,
                }
            })
            .collect()
    }
    fn expand(&self, w: &Window, out: &mut RowChunk) {
        out.clear(w.rows.start);
        let mut conv = CoeffCache::default();
        for c in &self.prog.constraints[w.handle.clone()] {
            out.push_row([&c.a, &c.b, &c.c], &self.layout, &mut conv);
        }
    }
}

/// Rows streamed straight out of the compact `circuit.xbc` bytecode (the
/// template-reduced R1CS, ~the size of the bytecode in RAM). Windows are runs of
/// independent top-level items, each expanded on demand.
pub struct BytecodeSource {
    stream: ReducedRowStream,
    layout: VarLayout,
    /// Evaluate rows from compiled templates (default) rather than expanding them.
    compiled: bool,
}

impl BytecodeSource {
    pub fn new(xbc: &[u8]) -> Result<Self, String> {
        let mut stream = ReducedRowStream::new(xbc)?;
        let layout = VarLayout::new(stream.vars().iter().copied());
        stream.release_vars(); // the layout now carries the same information
        Ok(BytecodeSource {
            stream,
            layout,
            compiled: true,
        })
    }

    pub fn stream(&self) -> &ReducedRowStream {
        &self.stream
    }

    /// Evaluate rows by expanding them (`false`) instead of from compiled
    /// templates — for benchmarking and cross-checking; results are identical.
    pub fn set_compiled(&mut self, on: bool) {
        self.compiled = on;
    }

    /// Rows of the largest single top-level item (bounds a window's size).
    pub fn max_item_rows(&self) -> usize {
        (0..self.stream.num_items())
            .map(|i| self.stream.item_row_start(i + 1) - self.stream.item_row_start(i))
            .max()
            .unwrap_or(0)
    }
}

impl ConstraintSource for BytecodeSource {
    fn layout(&self) -> &VarLayout {
        &self.layout
    }
    fn num_constraints(&self) -> usize {
        self.stream.num_constraints()
    }
    fn windows(&self, rows_hint: usize) -> Vec<Window> {
        let s = &self.stream;
        let mut out = Vec::new();
        let mut item = 0;
        while item < s.num_items() {
            let start = item;
            let row0 = s.item_row_start(item);
            while item < s.num_items() && s.item_row_start(item) - row0 < rows_hint {
                item += 1;
            }
            out.push(Window {
                rows: row0..s.item_row_start(item),
                handle: start..item,
            });
        }
        out
    }
    fn transpose_eval(&self, w: &[Fr], outs: [&mut [Fr]; 3]) {
        let [oa, ob, oc] = outs;
        let mut outs = [oa, ob, oc];
        let layout = &self.layout;
        self.stream.transpose_eval(w, &mut |var, m, v| {
            let p = match var {
                None => 0,
                Some(id) => layout
                    .position(id)
                    .expect("row references an unallocated var"),
            };
            outs[m][p] += v;
        });
    }
    fn eval_window(&self, w: &Window, z: &[Fr], outs: [Option<&mut [Fr]>; 3]) -> bool {
        if !self.compiled {
            return false;
        }
        let want = [outs[0].is_some(), outs[1].is_some(), outs[2].is_some()];
        let mut outs = outs;
        let pos = &self.layout;
        let zv = |id: u32| z[pos.position(id).expect("row references an unallocated var")];
        let mut i = 0usize;
        self.stream
            .eval_items(w.handle.clone(), &zv, want, &mut |v| {
                for (m, o) in outs.iter_mut().enumerate() {
                    if let Some(o) = o {
                        o[i] = v[m];
                    }
                }
                i += 1;
            });
        debug_assert_eq!(i, w.rows.len());
        true
    }
    fn expand(&self, w: &Window, out: &mut RowChunk) {
        out.clear(w.rows.start);
        let mut conv = CoeffCache::default();
        let layout = &self.layout;
        self.stream.visit_items(w.handle.clone(), &mut |row| {
            out.push_row([&row.a, &row.b, &row.c], layout, &mut conv);
        });
    }
}

/// Rows streamed from an `r1cs.stream` row file (any R1CS form — typically the
/// boundary-minimized circuit a plain `xark setup` keys). Holds the compact file
/// plus its coefficient pool as `Fr`; windows decode on demand.
pub struct RowFileSource {
    file: RowFile,
    layout: VarLayout,
    pool: Vec<Fr>,
}

impl RowFileSource {
    pub fn new(bytes: Vec<u8>) -> Result<Self, String> {
        let file = RowFile::parse(bytes)?;
        let layout = VarLayout::new(file.vars().iter().copied());
        let mut conv = CoeffCache::default();
        let pool = file.pool().iter().map(|f| conv.fr(f)).collect();
        // Every referenced var must be allocated (checked once, up front).
        let mut bad = None;
        for w in 0..file.num_windows() {
            file.decode_window(w, &mut |_, terms| {
                if bad.is_none() {
                    bad = terms
                        .iter()
                        .find(|t| layout.position(t.0).is_none())
                        .map(|t| t.0);
                }
            })?;
        }
        if let Some(v) = bad {
            return Err(format!("r1cs.stream references unallocated var {v}"));
        }
        Ok(RowFileSource { file, layout, pool })
    }

    pub fn file(&self) -> &RowFile {
        &self.file
    }
}

impl ConstraintSource for RowFileSource {
    fn layout(&self) -> &VarLayout {
        &self.layout
    }
    fn num_constraints(&self) -> usize {
        self.file.num_rows()
    }
    fn windows(&self, rows_hint: usize) -> Vec<Window> {
        let per = rows_hint.div_ceil(self.file.window_rows()).max(1);
        let (wr, n) = (self.file.window_rows(), self.file.num_rows());
        (0..self.file.num_windows())
            .step_by(per)
            .map(|w0| {
                let w1 = (w0 + per).min(self.file.num_windows());
                Window {
                    rows: w0 * wr..(w1 * wr).min(n),
                    handle: w0..w1,
                }
            })
            .collect()
    }
    fn expand(&self, w: &Window, out: &mut RowChunk) {
        out.clear(w.rows.start);
        let (pool, layout) = (&self.pool, &self.layout);
        for fw in w.handle.clone() {
            self.file
                .decode_window(fw, &mut |k, terms| {
                    let konst = (!pool[k as usize].is_zero()).then(|| (0u32, pool[k as usize]));
                    out.push_lc(
                        konst.into_iter().chain(
                            terms.iter().map(|&(v, c)| {
                                (layout.position(v).unwrap() as u32, pool[c as usize])
                            }),
                        ),
                    );
                })
                .expect("row file validated at load");
        }
    }
}
