//! The `xark.*` imports: each intrinsic call from the circuit module lands here and
//! drives the [`Builder`].
//!
//! **`Field` ABI.** A `Field` is 4 little-endian `u64` limbs in wasm memory, passed
//! by pointer. A constant keeps its true limbs (so `const` items and constructors
//! work unchanged); a witness value is a *handle*: `[index, kind, MAGIC, SENTINEL]`,
//! where `kind` says whether `index` is a variable id or an entry in the
//! linear-combination table. No canonical constant `< 2^256` has limb 3 =
//! `u64::MAX` *and* limb 2 = `MAGIC` below the field order, so the encodings can't
//! collide.

use std::collections::HashMap;

use num_bigint::BigInt;
use xark_ir::{ConstraintKind, FieldConst, FieldSpec, LinearCombination, Visibility};

use crate::builder::{Builder, CanonicalLcKey, canonical_lc_key};
use crate::error::{CompileError, CompileResult};
use crate::interp::{Bin, BoolOp, Cmp, Machine, Module, Sym, V};
use crate::output::{LowerOutput, check_pinning, finish};

const SENTINEL: u64 = u64::MAX;
const MAGIC: u64 = 0x6b72_6178_6b72_6178; // "xarkxark"
const KIND_VAR: u64 = 1;
const KIND_LC: u64 = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Intr {
    Add,
    Sub,
    Mul,
    Neg,
    Pow,
    Xor,
    Or,
    Eq,
    Ult,
    BoolToField,
    Advice,
    HintInverse,
    HintInverseOrZero,
    HintBit,
    HintDivRem,
    HintMulModDivMod,
    HintModInverse,
    HintSub2,
    RequireEq,
    WitnessBegin,
    WitnessEnd,
    ToBitsLookup,
    ToBitsRecord,
    InputField,
    InputUint,
    InputBool,
    InputsDone,
    InputSchema,
    InputUintHi,
    Panic,
}

fn intrinsic(name: &str) -> Option<Intr> {
    Some(match name {
        "add" => Intr::Add,
        "sub" => Intr::Sub,
        "mul" => Intr::Mul,
        "neg" => Intr::Neg,
        "pow" => Intr::Pow,
        "xor" => Intr::Xor,
        "or" => Intr::Or,
        "eq" => Intr::Eq,
        "ult" => Intr::Ult,
        "bool_to_field" => Intr::BoolToField,
        "advice" => Intr::Advice,
        "hint_inverse" => Intr::HintInverse,
        "hint_inverse_or_zero" => Intr::HintInverseOrZero,
        "hint_bit" => Intr::HintBit,
        "hint_div_rem" => Intr::HintDivRem,
        "hint_mulmod_divmod" => Intr::HintMulModDivMod,
        "hint_mod_inverse" => Intr::HintModInverse,
        "hint_sub2" => Intr::HintSub2,
        "require_eq" => Intr::RequireEq,
        "witness_begin" => Intr::WitnessBegin,
        "witness_end" => Intr::WitnessEnd,
        "to_bits_lookup" => Intr::ToBitsLookup,
        "to_bits_record" => Intr::ToBitsRecord,
        "input_field" => Intr::InputField,
        "input_uint" => Intr::InputUint,
        "input_bool" => Intr::InputBool,
        "inputs_done" => Intr::InputsDone,
        "input_schema" => Intr::InputSchema,
        "input_uint_hi" => Intr::InputUintHi,
        "panic" => Intr::Panic,
        _ => return None,
    })
}

pub struct Host {
    b: Builder,
    /// Import index → intrinsic.
    imports: Vec<Option<Intr>>,
    /// Linear-combination table for `Field` handles of kind `KIND_LC`; freed slots
    /// are `None` and reused under a new generation (see [`Host::collect`]).
    lcs: Vec<Option<LinearCombination>>,
    gens: Vec<u32>,
    free: Vec<u32>,
    /// Collect once this many slots are in use (`usize::MAX`: never — a native
    /// run's handles live in native memory the collector can't scan).
    pub(crate) gc_at: usize,
    /// `Sym::Wire` id → its linear combination.
    wires: Vec<LinearCombination>,
    /// Partial intrinsics (ones some inputs can't satisfy) run outside a guard; in
    /// an arm only input declarations count (see `crate::interp`'s fork).
    pub(crate) partial: usize,
    /// The witness-branch arms being run, outermost first: `(literal, guard)` where
    /// `literal` is the arm's condition (`c` or `1 − c`) and `guard` the conjunction
    /// of the literals so far, materialized on first use. Partial constraints in an
    /// arm are emitted as `guard → constraint` (see [`Host::require_gated`]).
    guards: Vec<(LinearCombination, Option<LinearCombination>)>,
    /// Bit widths known for variables (from the wires that are just that variable).
    var_width: HashMap<xark_ir::VarId, u32>,
    /// Unsigned comparisons by result wire: `(op, lhs, rhs)` — so a comparison later
    /// required outright (an overflow or bounds check) yields a variable bound.
    cmp_facts: HashMap<u32, (Cmp, LinearCombination, LinearCombination)>,
    /// Upper bounds on variables proven by such unconditional requirements (for
    /// `index_form`: an index LLVM narrowed using an earlier check, e.g. `1 − x`
    /// not underflowing, so `x ≤ 1`).
    var_max: HashMap<xark_ir::VarId, u64>,
    /// The high half of the last `u128` input bound (see `Intr::InputUintHi`).
    pending_hi: Option<LinearCombination>,
    /// Native-`uN` inputs awaiting their entry range check.
    uint_inputs: Vec<(u32, u32)>,
    n_inputs: usize,
    /// Input leaves in binding order: `(name, public, uint width)`.
    pub(crate) leaves: Vec<(String, bool, Option<u32>)>,
    /// `schema.json`, as the entry shim describes its parameters (`input_schema`).
    pub(crate) schema: Option<String>,
    /// `(p, p/2)`: reduce large constants into `(−p/2, p/2]` (when the field is known).
    reduce: Option<(BigInt, BigInt)>,
    /// Comparison intrinsics executed (`==`/`<` on witnesses), for stats.
    pub(crate) cmp_calls: u64,
    /// Big constants decoded from their limbs (bounded; see `decode_field`).
    consts: crate::builder::IdMap<[u64; 4], FieldConst>,
    /// Mux memo: one constraint per distinct `(cond, then, else)` select.
    muxes: HashMap<(u32, CanonicalLcKey, CanonicalLcKey), LinearCombination>,
    /// Profiling: the distinct wasm call stacks constraints were emitted at
    /// (resolved to source by [`crate::debuginfo`] after lowering).
    pub(crate) sites: Vec<Vec<(u32, u32)>>,
    site_ids: HashMap<Vec<(u32, u32)>, u32, std::hash::BuildHasherDefault<StackHasher>>,
    site_buf: Vec<(u32, u32)>,
}

/// A fast hasher for call stacks (`(func, pc)` pairs), looked up on every host
/// call: each word is mixed in, unlike `IdHasher`'s single-key `write_u32`.
#[derive(Default)]
struct StackHasher(u64);
impl std::hash::Hasher for StackHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.write_u64(b as u64);
        }
    }
    fn write_u32(&mut self, x: u32) {
        self.write_u64(x as u64);
    }
    fn write_usize(&mut self, x: usize) {
        self.write_u64(x as u64);
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}

impl Host {
    pub fn new(profile: bool, notes: bool, modulus: Option<&str>) -> Self {
        let mut b = Builder::new(profile);
        b.notes = notes;
        Host {
            reduce: modulus
                .filter(|_| crate::builder::dev_knob("XARK_NO_REDUCE").is_none())
                .and_then(|m| m.parse::<BigInt>().ok())
                .map(|p| {
                    let half = &p >> 1;
                    (p, half)
                }),
            b,
            imports: Vec::new(),
            lcs: Vec::new(),
            gens: Vec::new(),
            free: Vec::new(),
            gc_at: 1 << 20,
            wires: Vec::new(),
            var_width: HashMap::new(),
            cmp_facts: HashMap::new(),
            var_max: HashMap::new(),
            partial: 0,
            guards: Vec::new(),
            uint_inputs: Vec::new(),
            pending_hi: None,
            n_inputs: 0,
            leaves: Vec::new(),
            schema: None,
            cmp_calls: 0,
            muxes: HashMap::new(),
            sites: Vec::new(),
            site_ids: HashMap::default(),
            site_buf: Vec::new(),
            consts: Default::default(),
        }
    }

    /// The circuit's input interface as `schema.json`: the entry shim's description
    /// of its parameters (each parameter type's `Input::TYPE`), checked against the
    /// leaves it bound. A module without one (no `#[circuit]` shim) gets a schema of
    /// its public leaves alone.
    pub fn schema(&self, circuit: &str) -> CompileResult<serde_json::Value> {
        let public: Vec<&str> = self
            .leaves
            .iter()
            .filter(|l| l.1)
            .map(|l| l.0.as_str())
            .collect();
        let Some(text) = &self.schema else {
            return Ok(serde_json::json!({
                "version": 2,
                "circuit": circuit,
                "inputs": [],
                "types": {},
                "public_inputs": public,
            }));
        };
        let v: serde_json::Value = serde_json::from_str(text)
            .map_err(|e| CompileError::new(format!("internal error: the input schema: {e}")))?;
        if v["public_inputs"].as_array().map(|p| p.len()) != Some(public.len())
            || v["public_inputs"]
                .as_array()
                .into_iter()
                .flatten()
                .zip(&public)
                .any(|(a, b)| a != b)
        {
            return Err(CompileError::new(
                "an `Input` impl binds its leaves in a different order than its `TYPE` names                  them (the public inputs don't match the schema)",
            ));
        }
        Ok(v)
    }

    pub fn finish(self, field: FieldSpec) -> CompileResult<LowerOutput> {
        if std::env::var_os("XARK_FRONTEND_TIME").is_some() {
            let terms: usize = self.lcs.iter().flatten().map(|l| l.terms.len()).sum();
            let cterms: usize = self
                .b
                .constraints
                .iter()
                .map(|c| c.a.terms.len() + c.b.terms.len() + c.c.terms.len())
                .sum();
            eprintln!(
                "FRONTEND_TIME: cmp {} muxes {} ; lcs {} ({} terms), wires {}, regions {}, constraint terms {}",
                self.cmp_calls,
                self.muxes.len(),
                self.lcs.len(),
                terms,
                self.wires.len(),
                self.b.regions.len(),
                cterms
            );
        }
        let out = finish(self.b, field, self.n_inputs);
        check_pinning(&out, self.n_inputs)?;
        Ok(out)
    }

    // --- Field values -------------------------------------------------------

    fn field_words(&mut self, m: &Machine, lc: LinearCombination) -> [u64; 4] {
        if lc.terms.is_empty()
            && let Some(limbs) = const_limbs(&lc.constant)
        {
            return limbs;
        }
        if lc.constant.is_zero() && lc.terms.len() == 1 && lc.terms[0].coeff.is_one() {
            return [lc.terms[0].var as u64, KIND_VAR, MAGIC, SENTINEL];
        }
        if self.lcs.len() - self.free.len() >= self.gc_at && m.path_depth == 0 {
            self.collect(m);
        }
        let slot = match self.free.pop() {
            Some(i) => {
                self.lcs[i as usize] = Some(lc);
                i
            }
            None => {
                self.lcs.push(Some(lc));
                self.gens.push(0);
                self.lcs.len() as u32 - 1
            }
        };
        let generation = self.gens[slot as usize] as u64;
        [slot as u64, KIND_LC | generation << 8, MAGIC, SENTINEL]
    }

    /// Free every linear-combination slot no `Field` handle can still reach. A
    /// `Field` in wasm memory is found exactly (its marker limbs); any value in
    /// the machine's stack/locals/globals/selects is treated as a possible index.
    /// A freed slot's generation bumps, so a handle the scan missed fails loudly
    /// on use rather than reading a reused slot.
    fn collect(&mut self, m: &Machine) {
        let n = self.lcs.len();
        let live = std::cell::RefCell::new(vec![false; n]);
        m.scan_handles(
            (MAGIC, SENTINEL),
            |x| {
                if (x as usize) < n {
                    live.borrow_mut()[x as usize] = true;
                }
            },
            |idx, kind| {
                if kind & 0xff == KIND_LC && (idx as usize) < n {
                    live.borrow_mut()[idx as usize] = true;
                }
            },
        );
        let mut dead = Vec::new();
        for (i, alive) in live.into_inner().into_iter().enumerate() {
            if !alive && let Some(lc) = self.lcs[i].take() {
                dead.push(lc);
                self.gens[i] = self.gens[i].wrapping_add(1);
                self.free.push(i as u32);
            }
        }
        // Freeing a million linear combinations is pure allocator work: do it off
        // the lowering thread.
        std::thread::spawn(move || drop(dead));
        let in_use = n - self.free.len();
        self.gc_at = (2 * in_use).max(1 << 20);
    }

    /// Reduce `lc`'s large constants modulo the field (to the symmetric range, so a
    /// small negative stays small). The exact-integer constants the builder keeps
    /// otherwise grow without bound under repeated scaling (Poseidon's folded MDS
    /// products reach thousands of bits); the field element is unchanged.
    /// Profiling: attribute what's emitted next to the current wasm call stack (an
    /// interned site id, carried in the profile's `line` until it's resolved).
    #[inline]
    fn mark_site(&mut self, m: &Machine) {
        if !self.b.profile_enabled {
            return;
        }
        m.call_stack_into(&mut self.site_buf);
        let id = match self.site_ids.get(self.site_buf.as_slice()) {
            Some(&id) => id,
            None => {
                let id = self.sites.len() as u32;
                self.sites.push(self.site_buf.clone());
                self.site_ids.insert(self.site_buf.clone(), id);
                id
            }
        };
        self.b.location.line = id;
    }

    fn reduce_lc(&self, mut lc: LinearCombination) -> LinearCombination {
        let Some((p, half)) = &self.reduce else {
            return lc;
        };
        let fix = |c: &mut FieldConst| -> bool {
            // Small values and big ones already in `[−p/2, p/2]` (`|c| ≤ ⌊p/2⌋`, as
            // `p` is odd) reduce to themselves: skip the division.
            match c.as_big() {
                None => return false,
                Some(v) if v.magnitude() <= half.magnitude() => return false,
                Some(_) => {}
            }
            let mut r = c.big() % p;
            if r < BigInt::from(0) {
                r += p;
            }
            if &r > half {
                r -= p;
            }
            *c = FieldConst::from_bigint(r);
            c.is_zero()
        };
        fix(&mut lc.constant);
        let mut zero = false;
        for t in &mut lc.terms {
            zero |= fix(&mut t.coeff);
        }
        if zero {
            lc = lc.simplified();
        }
        lc
    }

    fn put_field(&mut self, m: &mut Machine, ptr: V, lc: LinearCombination) -> CompileResult<()> {
        let lc = self.reduce_lc(lc);
        let words = self.field_words(m, lc);
        m.write_words(ptr_of(ptr)?, &words)
    }

    fn get_field(&mut self, m: &mut Machine, ptr: V) -> CompileResult<LinearCombination> {
        let words = m.read_field(ptr_of(ptr)?)?;
        self.decode_field(m, &words)
    }

    /// `±a ± b` for the `Field`s at `pa`/`pb`, merging straight from the handle
    /// table (no clones) — the same canonical result as `LinearCombination`'s `+`/`-`.
    /// Also says whether the result may need [`Host::reduce_lc`]: not when both
    /// operands came from the handle table (stored reduced) and every coefficient
    /// the merge computed (rather than copied) is small — `reduce_lc` would return
    /// it unchanged.
    fn add_fields(
        &mut self,
        m: &mut Machine,
        pa: V,
        pb: V,
        neg_b: bool,
    ) -> CompileResult<(LinearCombination, bool)> {
        let wa = m.read_field(ptr_of(pa)?)?;
        let wb = m.read_field(ptr_of(pb)?)?;
        let va = self.view(m, &wa)?;
        let vb = self.view(m, &wb)?;
        // `consume_pending` on each operand (a pending product it reads stays a row).
        for v in [&va, &vb] {
            match v {
                View::Var(x) => self.b.consume_pending_var(*x),
                View::Owned(l) => self.b.consume_pending(l),
                View::Slot(_) => {}
            }
        }
        let owned = matches!(va, View::Owned(_)) || matches!(vb, View::Owned(_));
        let zero = xark_ir::FieldConst::zero();
        let (one_a, one_b);
        let (ca, ta): (&FieldConst, &[xark_ir::Term]) = match &va {
            View::Var(x) => {
                one_a = [xark_ir::Term {
                    coeff: FieldConst::one(),
                    var: *x,
                }];
                (&zero, &one_a)
            }
            View::Slot(i) => {
                let l = self.lcs[*i].as_ref().expect("live slot");
                (&l.constant, &l.terms)
            }
            View::Owned(l) => (&l.constant, &l.terms),
        };
        let (cb, tb): (&FieldConst, &[xark_ir::Term]) = match &vb {
            View::Var(x) => {
                one_b = [xark_ir::Term {
                    coeff: FieldConst::one(),
                    var: *x,
                }];
                (&zero, &one_b)
            }
            View::Slot(i) => {
                let l = self.lcs[*i].as_ref().expect("live slot");
                (&l.constant, &l.terms)
            }
            View::Owned(l) => (&l.constant, &l.terms),
        };
        let (lc, big) = merge_lc(ca, ta, cb, tb, neg_b);
        Ok((lc, big || owned))
    }

    /// A `Field`'s value without copying a stored linear combination.
    fn view(&mut self, m: &mut Machine, w: &[V; 4]) -> CompileResult<View> {
        if w.iter().all(|v| !v.is_sym()) && w[3].b == SENTINEL && w[2].b == MAGIC {
            match w[1].b & 0xff {
                KIND_VAR => return Ok(View::Var(w[0].b as u32)),
                KIND_LC => {
                    let i = w[0].b as usize;
                    return match (self.lcs.get(i), self.gens.get(i)) {
                        (Some(Some(_)), Some(&g)) if g as u64 == w[1].b >> 8 => Ok(View::Slot(i)),
                        _ => Err(CompileError::new(
                            "internal error: a stale `Field` handle was used (please report)",
                        )),
                    };
                }
                _ => {}
            }
        }
        Ok(View::Owned(self.decode_field(m, w)?))
    }

    fn get_fields(
        &mut self,
        m: &mut Machine,
        ptr: V,
        n: usize,
    ) -> CompileResult<Vec<LinearCombination>> {
        let base = ptr_of(ptr)?;
        (0..n)
            .map(|i| {
                let words = m.read_words(base + 32 * i as u32, 4)?;
                self.decode_field(m, &words)
            })
            .collect()
    }

    fn decode_field(&mut self, m: &mut Machine, w: &[V]) -> CompileResult<LinearCombination> {
        // A select in any limb: resolve each arm, then mux.
        if let Some(Sym::Ite { cond, .. }) = w
            .iter()
            .find(|v| v.is_sym() && matches!(m.syms[v.s as usize], Sym::Ite { .. }))
            .map(|v| m.syms[v.s as usize].clone())
        {
            let arm = |m: &Machine, pick_t: bool| -> Vec<V> {
                w.iter()
                    .map(|&v| match &m.syms[v.s as usize] {
                        Sym::Ite { cond: c, t, e } if *c == cond => {
                            if pick_t {
                                *t
                            } else {
                                *e
                            }
                        }
                        _ => v,
                    })
                    .collect()
            };
            let (tw, ew) = (arm(m, true), arm(m, false));
            let t = self.decode_field(m, &tw)?;
            let e = self.decode_field(m, &ew)?;
            return Ok(self.mux_by_sym(m, cond, t, e));
        }
        // A native-integer witness widened to a `Field` (`Field::from(x: u8)`): the
        // wire's own LC — `x` is already a range-checked field value.
        if w[0].is_sym() || w[1].is_sym() {
            // `Field::from(x)` for a `u64`/`u128` witness: limbs 0–1 are its 64-bit
            // halves (wires or zero), limbs 2–3 zero.
            if w[2..].iter().all(|v| !v.is_sym() && v.b == 0)
                && self.int_width(m, w[0]) <= 64
                && self.int_width(m, w[1]) <= 64
            {
                let lo = self.int_lc(m, w[0])?;
                let hi = self.int_lc(m, w[1])?;
                return Ok(lo + hi.scale(&FieldConst::from_bigint(BigInt::from(1u8) << 64)));
            }
            return Err(CompileError::new(
                "a `Field` was assembled from witness pieces the frontend can't follow",
            ));
        }
        if w.iter().any(|v| v.is_sym()) {
            return Err(CompileError::new(
                "a `Field` was assembled from witness pieces the frontend can't follow",
            ));
        }
        let limbs = [w[0].b, w[1].b, w[2].b, w[3].b];
        if limbs[3] == SENTINEL && limbs[2] == MAGIC {
            return match limbs[1] & 0xff {
                KIND_VAR => Ok(LinearCombination::var(limbs[0] as u32)),
                KIND_LC => {
                    let i = limbs[0] as usize;
                    match (self.lcs.get(i), self.gens.get(i)) {
                        (Some(Some(lc)), Some(&g)) if g as u64 == limbs[1] >> 8 => Ok(lc.clone()),
                        _ => Err(CompileError::new(
                            "internal error: a stale `Field` handle was used (please report)",
                        )),
                    }
                }
                k => Err(CompileError::new(format!(
                    "corrupt `Field` handle (kind {k})"
                ))),
            };
        }
        if limbs[1..] == [0, 0, 0] && limbs[0] <= i64::MAX as u64 {
            return Ok(LinearCombination {
                constant: FieldConst::from_i64(limbs[0] as i64),
                terms: Vec::new(),
            });
        }
        if let Some(c) = self.consts.get(&limbs) {
            return Ok(LinearCombination {
                constant: c.clone(),
                terms: Vec::new(),
            });
        }
        let mut bytes = [0u8; 32];
        for (i, l) in limbs.iter().enumerate() {
            bytes[8 * i..8 * i + 8].copy_from_slice(&l.to_le_bytes());
        }
        let c = FieldConst::from_bigint(BigInt::from_bytes_le(num_bigint::Sign::Plus, &bytes));
        if self.consts.len() >= 1 << 16 {
            self.consts.clear();
        }
        self.consts.insert(limbs, c.clone());
        Ok(LinearCombination {
            constant: c,
            terms: Vec::new(),
        })
    }

    /// The linear combination of an integer value (a `bool`, a `uN`).
    fn int_lc(&mut self, m: &mut Machine, v: V) -> CompileResult<LinearCombination> {
        if !v.is_sym() {
            return Ok(LinearCombination {
                constant: FieldConst::from_bigint(BigInt::from(v.b)),
                terms: Vec::new(),
            });
        }
        // (`FieldConst::from_bigint` normalizes small values to the inline form.)
        match m.syms[v.s as usize].clone() {
            Sym::Wire { id, .. } => Ok(self.wires[id as usize].clone()),
            Sym::Ite { cond, t, e } => {
                let t = self.int_lc(m, t)?;
                let e = self.int_lc(m, e)?;
                Ok(self.mux_by_sym(m, cond, t, e))
            }
            Sym::Bytes(bytes) => {
                // Σ byteᵢ·256ⁱ; a byte of a wider value comes from its bits.
                let mut acc = LinearCombination::zero();
                for (i, (byte, sb)) in bytes.iter().enumerate() {
                    let scale = FieldConst::from_bigint(BigInt::from(1u8) << (8 * i));
                    let piece = match sb {
                        None => LinearCombination {
                            constant: FieldConst::from_i64(*byte as i64),
                            terms: Vec::new(),
                        },
                        Some(sb) => self.byte_lc(m, sb.sym, sb.k)?,
                    };
                    acc = acc + piece.scale(&scale);
                }
                Ok(acc)
            }
            Sym::None => unreachable!(),
        }
    }

    /// Byte `k` of symbolic value `sym` as a linear combination.
    fn byte_lc(&mut self, m: &mut Machine, sym: u32, k: u8) -> CompileResult<LinearCombination> {
        let v = V { b: 0, s: sym };
        let (lc, width) = self.int_parts(m, v)?;
        if k == 0 && width <= 8 {
            return Ok(lc);
        }
        if 8 * k as u32 >= width {
            return Ok(LinearCombination::zero());
        }
        if let Some((_, high)) = self.split_lc(&lc, 8 * k as u32)
            && let Some((byte, _)) = self.split_lc(&high, 8)
        {
            return Ok(byte);
        }
        let bits = self.bits_of(&lc, width as usize)?;
        let hi = (8 * k as usize + 8).min(width as usize);
        Ok(Self::recompose(&bits[8 * k as usize..hi]))
    }

    fn mux_by_sym(
        &mut self,
        m: &Machine,
        cond: u32,
        t: LinearCombination,
        e: LinearCombination,
    ) -> LinearCombination {
        let id = match m.syms[cond as usize] {
            Sym::Wire { id, .. } => id,
            _ => unreachable!("conditions are wires"),
        };
        let t = t.simplified();
        let e = e.simplified();
        if t == e {
            return t;
        }
        let key = (id, canonical_lc_key(&t), canonical_lc_key(&e));
        if let Some(lc) = self.muxes.get(&key) {
            return lc.clone();
        }
        let c = self.wires[id as usize].clone();
        let diff = t - e.clone();
        let out = e + self.b.emit_mul(c, diff);
        // Memo tables record proven facts: a witness-only region proves nothing.
        if !self.b.witness_only {
            self.muxes.insert(key, out.clone());
        }
        out
    }

    fn new_wire(&mut self, m: &mut Machine, lc: LinearCombination, width: u32) -> V {
        // Remember a bare variable's range (for `index_form`).
        if lc.constant.is_zero()
            && let [t] = &lc.terms[..]
            && t.coeff.as_i64() == Some(1)
        {
            let w = self.var_width.entry(t.var).or_insert(width);
            *w = (*w).min(width);
        }
        self.wires.push(lc);
        m.new_sym(Sym::Wire {
            id: self.wires.len() as u32 - 1,
            width,
        })
    }
}

fn ptr_of(v: V) -> CompileResult<u32> {
    if v.is_sym() {
        return Err(CompileError::new(
            "a witness-dependent pointer reached an intrinsic",
        ));
    }
    Ok(v.b as u32)
}

fn int_of(v: V, what: &str) -> CompileResult<u64> {
    if v.is_sym() {
        return Err(CompileError::new(format!(
            "{what} must be a compile-time constant"
        )));
    }
    Ok(v.b)
}

/// The limbs of a non-negative constant below `2^256`, unless they would read as a
/// handle.
fn const_limbs(c: &FieldConst) -> Option<[u64; 4]> {
    if c.is_negative() {
        return None;
    }
    let (_, digits) = c.big().to_u64_digits();
    if digits.len() > 4 {
        return None;
    }
    let mut limbs = [0u64; 4];
    limbs[..digits.len()].copy_from_slice(&digits);
    if limbs[3] == SENTINEL && limbs[2] == MAGIC {
        return None;
    }
    Some(limbs)
}

impl Host {
    /// The current arm's guard: `None` outside witness branches, else the `{0,1}`
    /// conjunction of the enclosing arms' conditions (one product per nesting level,
    /// emitted the first time it's needed — a total row).
    fn guard(&mut self) -> Option<LinearCombination> {
        let i = self.guards.iter().rposition(|g| g.1.is_some());
        let start = i.map_or(0, |i| i + 1);
        for j in start..self.guards.len() {
            let lit = self.guards[j].0.clone();
            let g = match j
                .checked_sub(1)
                .map(|k| self.guards[k].1.clone().expect("set"))
            {
                None => lit,
                Some(parent) => {
                    self.b.consume_pending(&parent);
                    self.b.consume_pending(&lit);
                    self.b.emit_mul(parent, lit)
                }
            };
            self.guards[j].1 = Some(g);
        }
        self.guards.last().and_then(|g| g.1.clone())
    }

    /// `lhs = rhs` where the current path is taken. Outside witness branches a plain
    /// equality; inside an arm `guard · (lhs − rhs) = 0`, which binds exactly when
    /// the arm is taken (`guard = 1`) and is vacuous otherwise — so an `assert!` or
    /// `require_eq` in an untaken arm constrains nothing. Sound because every value
    /// the arm computes leaves it only through the merge's select on the same
    /// condition (`crate::interp`'s `merge`).
    fn require_gated(&mut self, lhs: LinearCombination, rhs: LinearCombination) {
        match self.guard() {
            None => self.b.emit_require_eq(lhs, rhs),
            Some(g) => self.b.emit_require_eq_gated(g, lhs, rhs),
        }
    }

    /// `cond == value` was just required outside any witness branch: if `cond` is an
    /// unsigned comparison of a bare variable with a constant, record the bound it
    /// proves (every satisfying witness obeys it).
    fn learn_bound(&mut self, cond: u32, value: bool) {
        let Some((o, x, y)) = self.cmp_facts.get(&cond).cloned() else {
            return;
        };
        let var_of = |l: &LinearCombination| {
            (l.constant.is_zero() && l.terms.len() == 1 && l.terms[0].coeff.is_one())
                .then(|| l.terms[0].var)
        };
        let konst = |l: &LinearCombination| {
            l.is_constant()
                .then(|| l.constant.as_i64())
                .flatten()
                .filter(|c| *c >= 0)
        };
        // Normalize to `v ≤ max` for a variable `v`.
        let (v, max) = match (var_of(&x), konst(&y), var_of(&y), konst(&x)) {
            // v OP c
            (Some(v), Some(c), _, _) => match (o, value) {
                (Cmp::LtU, true) | (Cmp::GeU, false) => (v, c - 1),
                (Cmp::LeU, true) | (Cmp::GtU, false) => (v, c),
                _ => return,
            },
            // c OP v
            (_, _, Some(v), Some(c)) => match (o, value) {
                (Cmp::GtU, true) | (Cmp::LeU, false) => (v, c - 1),
                (Cmp::GeU, true) | (Cmp::LtU, false) => (v, c),
                _ => return,
            },
            _ => return,
        };
        if max < 0 {
            return;
        }
        let e = self.var_max.entry(v).or_insert(max as u64);
        *e = (*e).min(max as u64);
    }

    /// Bits needed for the largest value `lc` can take, when every coefficient and the
    /// constant are non-negative and every variable is bounded (known width,
    /// booleanity, or a proven bound); `None` otherwise.
    fn lc_bits(&self, lc: &LinearCombination) -> Option<u32> {
        self.lc_max(lc).map(|max| 128 - max.leading_zeros())
    }

    /// An upper bound on the integer `lc` (non-negative coefficients and constant;
    /// each variable bounded by its proven width, booleanity or a learned bound).
    fn lc_max(&self, lc: &LinearCombination) -> Option<u128> {
        let mut max = u128::try_from(lc.constant.as_i64()?).ok()?;
        for t in &lc.terms {
            let c = u128::try_from(t.coeff.as_i64()?).ok()?;
            let width_max = self
                .var_width
                .get(&t.var)
                .filter(|&&w| w < 64)
                .map(|&w| (1u128 << w) - 1);
            let vmax = if self.b.boolean_vars.contains(&t.var) {
                1
            } else {
                match (width_max, self.var_max.get(&t.var)) {
                    (Some(a), Some(&b)) => a.min(b as u128),
                    (Some(a), None) => a,
                    (None, Some(&b)) => b as u128,
                    (None, None) => return None,
                }
            };
            max = max.checked_add(c.checked_mul(vmax)?)?;
        }
        Some(max)
    }

    /// `lc` as `low + 2^k·high` over the integers, with `0 ≤ low < 2^k`, read off its
    /// terms (each coefficient `c = q·2^k + r` gives `q` to `high` and `r` to `low`):
    /// bits `k..` and `..k` of a value without decomposing it. Needs `lc`'s bound
    /// ([`Self::lc_max`]: non-negative coefficients, every variable proven bounded, so
    /// no wrap mod p) and `low`'s below `2^k`; `None` otherwise.
    ///
    /// A value assembled from narrow pieces (bytes packed into a word, `hi << k | lo`)
    /// comes apart this way for free, so moving it through a register costs nothing.
    fn split_lc(
        &self,
        lc: &LinearCombination,
        k: u32,
    ) -> Option<(LinearCombination, LinearCombination)> {
        if k >= 63 {
            return None;
        }
        self.lc_max(lc)?;
        let m = 1i64 << k;
        let konst = |c: i64| LinearCombination {
            constant: FieldConst::from_i64(c),
            terms: Vec::new(),
        };
        let c = lc.constant.as_i64()?;
        let (mut low, mut high) = (konst(c % m), konst(c / m));
        for t in &lc.terms {
            let c = t.coeff.as_i64()?;
            let v = LinearCombination::var(t.var);
            if c % m != 0 {
                low = low + v.clone().scale(&FieldConst::from_i64(c % m));
            }
            if c / m != 0 {
                high = high + v.scale(&FieldConst::from_i64(c / m));
            }
        }
        (self.lc_max(&low)? < m as u128).then_some((low, high))
    }

    /// `a | b` (and `a ^ b`, `a + b`) when their bits can't overlap: every term and
    /// the constant of one a multiple of `2^k`, and the other below `2^k` — a word
    /// packed from narrow pieces (`hi << k | lo`). Then the OR is the sum.
    fn disjoint(&self, a: &LinearCombination, b: &LinearCombination) -> bool {
        let tz = |lc: &LinearCombination| -> Option<u32> {
            let mut k = 63u32;
            for c in std::iter::once(&lc.constant).chain(lc.terms.iter().map(|t| &t.coeff)) {
                let c = c.as_i64()?;
                if c < 0 {
                    return None;
                }
                if c != 0 {
                    k = k.min(c.trailing_zeros());
                }
            }
            Some(k)
        };
        let fits = |hi: &LinearCombination, lo: &LinearCombination| {
            !hi.is_constant()
                && self.lc_max(hi).is_some()
                && tz(hi)
                    .zip(self.lc_max(lo))
                    .is_some_and(|(k, max)| max < 1u128 << k)
        };
        fits(a, b) || fits(b, a)
    }

    /// An unsigned comparison (or `==`/`!=`) the operands' bounds already decide —
    /// e.g. a loop counter past a witness bound's proven width — with no gadget.
    fn decided_cmp(&self, o: Cmp, la: &LinearCombination, lb: &LinearCombination) -> Option<bool> {
        let range = |lc: &LinearCombination| -> Option<(u128, u128)> {
            if lc.is_constant() {
                let c = u128::try_from(lc.constant.as_i64()?).ok()?;
                Some((c, c))
            } else {
                Some((0, self.lc_max(lc)?))
            }
        };
        let ((alo, ahi), (blo, bhi)) = (range(la)?, range(lb)?);
        let (lt, ge) = (ahi < blo, alo >= bhi); // a < b surely; a ≥ b surely
        let (gt, le) = (alo > bhi, ahi <= blo); // a > b surely; a ≤ b surely
        match o {
            Cmp::LtU => lt.then_some(true).or(ge.then_some(false)),
            Cmp::GeU => ge.then_some(true).or(lt.then_some(false)),
            Cmp::GtU => gt.then_some(true).or(le.then_some(false)),
            Cmp::LeU => le.then_some(true).or(gt.then_some(false)),
            Cmp::Eq => (lt || gt).then_some(false),
            Cmp::Ne => (lt || gt).then_some(true),
            _ => None,
        }
    }

    /// A gadget hint's limbs inside an arm: `g · limb`, plus `low · (1 − g)` on limb
    /// 0 — the value the hint sees where the arm isn't taken (`1` for a divisor or
    /// modulus, so it never fails there). Unchanged outside arms.
    fn gate_limbs(
        &mut self,
        g: Option<&LinearCombination>,
        limbs: Vec<LinearCombination>,
        low: i64,
    ) -> Vec<LinearCombination> {
        let Some(g) = g else {
            return limbs;
        };
        limbs
            .into_iter()
            .enumerate()
            .map(|(i, x)| {
                let x = self.b.gate_input(Some(g), x);
                if i == 0 && low != 0 {
                    let k = FieldConst::from_i64(low);
                    x + (LinearCombination::one() - g.clone()).scale(&k)
                } else {
                    x
                }
            })
            .collect()
    }

    /// `x + 2^(reg−1) mod 2^reg` for a `reg`-bit `x` (see `int_cmp`).
    fn sign_flip(&mut self, x: LinearCombination, reg: u32) -> CompileResult<LinearCombination> {
        let half = pow2(reg - 1);
        if x.is_constant() {
            let f = (x.constant.big() + &half) % pow2(reg);
            return Ok(LinearCombination::constant(f.to_string()));
        }
        let lt = self
            .b
            .emit_less_than(reg as usize, x.clone(), lc_of(&half))?;
        // x + half − 2^reg·(1 − lt)
        Ok(x + lc_of(&half)
            - (LinearCombination::one() - lt).scale(&FieldConst::from_bigint(pow2(reg))))
    }

    /// A `width`-bit `x` sign-extended to `reg` bits: `x + (2^reg − 2^width)·top(x)`.
    fn sext_impl(&mut self, m: &mut Machine, x: V, width: u32, reg: u32) -> CompileResult<V> {
        let lx = self.int_lc(m, x)?;
        let lt = self
            .b
            .emit_less_than(width as usize, lx.clone(), lc_of(&pow2(width - 1)))?;
        let top = LinearCombination::one() - lt;
        let lc = lx + top.scale(&FieldConst::from_bigint(pow2(reg) - pow2(width)));
        Ok(self.new_wire(m, lc, reg))
    }

    /// An integer value's linear combination and a bound on its bit width.
    fn int_parts(&mut self, m: &mut Machine, v: V) -> CompileResult<(LinearCombination, u32)> {
        let w = self.int_width(m, v);
        Ok((self.int_lc(m, v)?, w))
    }

    fn int_width(&self, m: &Machine, v: V) -> u32 {
        if !v.is_sym() {
            return 64 - v.b.leading_zeros();
        }
        match &m.syms[v.s as usize] {
            Sym::Wire { width, .. } => *width,
            Sym::Ite { t, e, .. } => self.int_width(m, *t).max(self.int_width(m, *e)),
            Sym::Bytes(b) => {
                // Up to the last byte that may be nonzero.
                let last = b.iter().rposition(|(byte, sb)| sb.is_some() || *byte != 0);
                last.map_or(0, |i| 8 * (i as u32 + 1))
            }
            Sym::None => 0,
        }
    }

    /// `x`'s `n` little-endian bits (range-checking `x < 2ⁿ`), memoized like
    /// `to_bits`.
    fn bits_of(
        &mut self,
        x: &LinearCombination,
        n: usize,
    ) -> CompileResult<Vec<LinearCombination>> {
        if x.is_constant() {
            // A constant wider than `n` bits would mean a width was mis-tracked;
            // never read it as zero.
            let bits = x.constant.to_bits_le(n).ok_or_else(|| {
                CompileError::new(format!(
                    "internal: a constant does not fit its {n}-bit width"
                ))
            })?;
            return Ok(bits
                .into_iter()
                .map(|b| {
                    if b {
                        LinearCombination::one()
                    } else {
                        LinearCombination::zero()
                    }
                })
                .collect());
        }
        if let Some(vars) = self.b.bit_sum_shortcut(x, n) {
            return Ok(vars.into_iter().map(LinearCombination::var).collect());
        }
        let key = (canonical_lc_key(x), n);
        if let Some(vars) = self.b.bit_cache.get(&key) {
            return Ok(vars.iter().map(|&v| LinearCombination::var(v)).collect());
        }
        self.b.kind_stack.push(ConstraintKind::RangeCheck);
        let vars = self.b.decompose_bits(x.clone(), n);
        self.b.kind_stack.pop();
        if !self.b.witness_only {
            self.b.bit_cache.insert(key, vars.clone());
        }
        Ok(vars.into_iter().map(LinearCombination::var).collect())
    }

    fn recompose(bits: &[LinearCombination]) -> LinearCombination {
        let mut acc = LinearCombination::zero();
        let mut pow = FieldConst::one();
        let two = FieldConst::from_i64(2);
        for b in bits {
            acc = acc + b.clone().scale(&pow);
            pow = pow.mul(&two);
        }
        acc
    }

    /// A wire for `lc < 2^width`, truncated to the register (`reg` bits) if wider.
    fn int_result(
        &mut self,
        m: &mut Machine,
        lc: LinearCombination,
        width: u32,
        reg: u32,
    ) -> CompileResult<V> {
        if lc.is_constant()
            && let Some(v) = lc.constant.as_i64()
        {
            let v = v as u64;
            return Ok(V::c(if reg == 32 { v as u32 as u64 } else { v }));
        }
        // A value whose bound (from its variables' widths, booleanity and the bounds
        // unconditional checks proved) already fits needs no truncation — e.g. a
        // pointer `8·x + base` computed in 64 bits after `x ≤ 1` was checked.
        let width = width.min(self.lc_bits(&lc).unwrap_or(width));
        if width <= reg {
            return Ok(self.new_wire(m, lc, width));
        }
        if let Some((low, _)) = self.split_lc(&lc, reg) {
            return Ok(self.new_wire(m, low, reg));
        }
        let bits = self.bits_of(&lc, width as usize)?;
        let low = Self::recompose(&bits[..reg as usize]);
        Ok(self.new_wire(m, low, reg))
    }
}

impl crate::interp::Host for Host {
    fn int_bin(&mut self, m: &mut Machine, o: Bin, wide: bool, a: V, b: V) -> CompileResult<V> {
        probe_guard(m)?;
        self.mark_site(m);
        let reg = if wide { 64 } else { 32 };
        let (la, wa) = self.int_parts(m, a)?;
        let (lb, wb) = self.int_parts(m, b)?;
        let konst = |v: V| (!v.is_sym()).then_some(v.b);
        let shift = |b: V| -> CompileResult<u32> {
            konst(b)
                .map(|k| (k % reg as u64) as u32)
                .ok_or_else(|| CompileError::new("a shift by a witness amount is not supported"))
        };
        // A shift by a witness amount `k` (mod the register width, as wasm defines
        // it): `x << k = x · 2^k`, `x >> k = x / 2^k`, with `2^k = Π (1 + (2^2^i − 1)·kᵢ)`
        // over `k`'s low bits — a nonzero divisor, so both are total.
        if matches!(o, Bin::Shl | Bin::ShrU) && b.is_sym() {
            let lg: usize = if wide { 6 } else { 5 }; // log2(reg)
            let kb = self.bits_of(&lb, (wb as usize).max(lg))?;
            let mut p = LinearCombination::one();
            for (i, bit) in kb[..lg].iter().enumerate() {
                let f = LinearCombination::one()
                    + bit
                        .clone()
                        .scale(&FieldConst::from_bigint(pow2(1 << i) - 1));
                p = if p.is_constant() {
                    f.scale(&p.constant)
                } else {
                    self.b.consume_pending(&p);
                    self.b.emit_mul(p, f)
                };
            }
            if o == Bin::Shl {
                self.b.consume_pending(&la);
                self.b.consume_pending(&p);
                let lc = self.b.emit_mul(la, p);
                return self.int_result(m, lc, wa + reg - 1, reg);
            }
            let (q, r) = (self.b.alloc_advice(), self.b.alloc_advice());
            self.b
                .witness_gen
                .push(Some(xark_ir::primitive::WitnessGen::DivRem {
                    q,
                    r,
                    num: la.clone(),
                    den: p.clone(),
                }));
            let (ql, rl) = (LinearCombination::var(q), LinearCombination::var(r));
            let _ = self.bits_of(&ql, wa.max(1) as usize)?;
            let _ = self.bits_of(&rl, wa.max(1) as usize)?;
            let n = wa.max(reg) as usize;
            let lt = self.b.emit_less_than(n, rl.clone(), p.clone())?;
            self.b.emit_require_eq(lt, LinearCombination::one());
            self.b.consume_pending(&p);
            let prod = self.b.emit_mul(ql.clone(), p);
            self.b.consume_pending(&la);
            self.b.emit_require_eq(prod + rl, la);
            return self.int_result(m, ql, wa, reg);
        }
        Ok(match o {
            Bin::Add => {
                let w = wa.max(wb) + 1;
                self.int_result(m, la + lb, w, reg)?
            }
            Bin::Sub => {
                if konst(b) == Some(0) {
                    return Ok(a);
                }
                let r = self.b.emit_wrapping_sub(reg as usize, la, lb);
                self.new_wire(m, r, reg)
            }
            Bin::Mul => {
                let (lc, w) = if let Some(c) = konst(a) {
                    (lb.scale(&FieldConst::from_bigint(BigInt::from(c))), wa + wb)
                } else if let Some(c) = konst(b) {
                    (la.scale(&FieldConst::from_bigint(BigInt::from(c))), wa + wb)
                } else {
                    self.b.consume_pending(&la);
                    self.b.consume_pending(&lb);
                    (self.b.emit_mul(la, lb), wa + wb)
                };
                self.int_result(m, lc, w, reg)?
            }
            Bin::Or | Bin::Xor if self.disjoint(&la, &lb) => {
                self.int_result(m, la + lb, wa.max(wb), reg)?
            }
            Bin::And | Bin::Or | Bin::Xor => {
                // `x & (2^k − 1)`: the low `k` bits. (Not a match guard: `if let`
                // guards aren't stable on Rust 1.89, which xark supports.)
                let (x, mask_wa) = if konst(b).is_some() {
                    (&la, wa)
                } else {
                    (&lb, wb)
                };
                if o == Bin::And
                    && let Some(k) = konst(b)
                        .or(konst(a))
                        .and_then(|mask| mask.checked_add(1))
                        .filter(|p| p.is_power_of_two())
                        .map(u64::trailing_zeros)
                    && let Some((low, _)) = self.split_lc(x, k)
                {
                    return self.int_result(m, low, k.min(mask_wa), reg);
                }
                let n = wa.max(wb).min(reg) as usize;
                let ba = self.bits_of(&la, n)?;
                let bb = self.bits_of(&lb, n)?;
                let mut out = Vec::with_capacity(n);
                for i in 0..n {
                    let (x, y) = (ba[i].clone(), bb[i].clone());
                    let bit = match (o, x.is_constant(), y.is_constant()) {
                        (Bin::And, true, _) if x.constant.is_zero() => LinearCombination::zero(),
                        (Bin::And, _, true) if y.constant.is_zero() => LinearCombination::zero(),
                        (Bin::And, true, _) => y,
                        (Bin::And, _, true) => x,
                        (Bin::Or, true, _) if x.constant.is_zero() => y,
                        (Bin::Or, _, true) if y.constant.is_zero() => x,
                        (Bin::Or, true, _) | (Bin::Or, _, true) => LinearCombination::one(),
                        (Bin::Xor, true, _) if x.constant.is_zero() => y,
                        (Bin::Xor, _, true) if y.constant.is_zero() => x,
                        (Bin::Xor, true, _) => LinearCombination::one() - y,
                        (Bin::Xor, _, true) => LinearCombination::one() - x,
                        (Bin::And, _, _) => self.b.emit_mul(x, y),
                        (Bin::Or, _, _) => self.b.emit_or(x, y),
                        _ => self.b.emit_xor(x, y),
                    };
                    out.push(bit);
                }
                let lc = Self::recompose(&out);
                // `a & b < 2^min(wa, wb)` (a constant mask's width is its bit length).
                let w = if o == Bin::And { wa.min(wb) } else { n as u32 };
                self.int_result(m, lc, w, reg)?
            }
            Bin::Shl => {
                let k = shift(b)?;
                let lc = la.scale(&FieldConst::from_bigint(BigInt::from(1u8) << k));
                self.int_result(m, lc, wa + k, reg)?
            }
            Bin::ShrU | Bin::ShrS => {
                let k = shift(b)?;
                if o == Bin::ShrS && wa >= reg {
                    // Two's complement: the logical shift plus the sign bit copied
                    // into the top `k` bits.
                    let bits = self.bits_of(&la, reg as usize)?;
                    let top = bits[reg as usize - 1].clone();
                    let fill = pow2(reg) - pow2(reg - k);
                    let lc = Self::recompose(&bits[k as usize..])
                        + top.scale(&FieldConst::from_bigint(fill));
                    return self.int_result(m, lc, reg, reg);
                }
                if k >= wa {
                    return Ok(V::c(0));
                }
                if let Some((_, high)) = self.split_lc(&la, k) {
                    return self.int_result(m, high, wa - k, reg);
                }
                let bits = self.bits_of(&la, wa as usize)?;
                let lc = Self::recompose(&bits[k as usize..]);
                self.int_result(m, lc, wa - k, reg)?
            }
            Bin::Rotl | Bin::Rotr => {
                let k = shift(b)?;
                let mut bits = self.bits_of(&la, reg as usize)?;
                if o == Bin::Rotl {
                    bits.rotate_right(k as usize);
                } else {
                    bits.rotate_left(k as usize);
                }
                let lc = Self::recompose(&bits);
                self.int_result(m, lc, reg, reg)?
            }
            Bin::DivU | Bin::RemU => match konst(b) {
                Some(c) if c.is_power_of_two() => {
                    let k = c.trailing_zeros();
                    if let Some((low, high)) = self.split_lc(&la, k) {
                        return if o == Bin::DivU {
                            self.int_result(m, high, wa.saturating_sub(k), reg)
                        } else {
                            self.int_result(m, low, k.min(wa), reg)
                        };
                    }
                    let bits = self.bits_of(&la, wa.max(k) as usize)?;
                    let lc = if o == Bin::DivU {
                        Self::recompose(&bits[k.min(wa) as usize..])
                    } else {
                        Self::recompose(&bits[..k.min(wa) as usize])
                    };
                    let w = if o == Bin::DivU {
                        wa.saturating_sub(k)
                    } else {
                        k.min(wa)
                    };
                    self.int_result(m, lc, w, reg)?
                }
                Some(0) => {
                    return Err(CompileError::new("integer division by zero").diverging());
                }
                _ => {
                    // Hinted `q = a / b`, `r = a % b`, pinned by `a = q·b + r` with
                    // `q < 2^wa`, `r < 2^wb` and `r < b`. Everything is below
                    // `2^(2·64+1) < p`, so the identity holds over the integers and
                    // the division algorithm makes `(q, r)` unique; `b = 0` leaves
                    // `r < 0`: unsatisfiable, as Rust's check (and the trap) demand.
                    //
                    // In a witness-branch arm (guard `g`) the two equalities bind only
                    // when it's taken, and the hint divides `g·a` by `b + 1 − g`: an
                    // untaken arm's `b` may be 0, and there `q = r = 0` (pinned so).
                    let g = self.guard();
                    let den = match (&g, konst(b)) {
                        (Some(g), None) => lb.clone() + LinearCombination::one() - g.clone(),
                        _ => lb.clone(),
                    };
                    let num = self.b.gate_input(g.as_ref(), la.clone());
                    let (q, r) = (self.b.alloc_advice(), self.b.alloc_advice());
                    self.b
                        .witness_gen
                        .push(Some(xark_ir::primitive::WitnessGen::DivRem {
                            q,
                            r,
                            num,
                            den,
                        }));
                    self.b.pin_dead(g.as_ref(), q);
                    self.b.pin_dead(g.as_ref(), r);
                    let (ql, rl) = (LinearCombination::var(q), LinearCombination::var(r));
                    let _ = self.bits_of(&ql, wa.max(1) as usize)?;
                    let _ = self.bits_of(&rl, wb.max(1) as usize)?;
                    let lt = self
                        .b
                        .emit_less_than(wb.max(1) as usize, rl.clone(), lb.clone())?;
                    self.require_gated(lt, LinearCombination::one());
                    let prod = match konst(b) {
                        Some(c) => ql.clone().scale(&FieldConst::from_bigint(BigInt::from(c))),
                        None => {
                            self.b.consume_pending(&lb);
                            self.b.emit_mul(ql.clone(), lb)
                        }
                    };
                    self.b.consume_pending(&la);
                    self.require_gated(prod + rl.clone(), la);
                    if o == Bin::DivU {
                        self.int_result(m, ql, wa, reg)?
                    } else {
                        self.int_result(m, rl, wb, reg)?
                    }
                }
            },
            Bin::DivS | Bin::RemS => {
                return Err(CompileError::new(
                    "signed division of a witness integer is not supported",
                ));
            }
        })
    }

    fn int_cmp(&mut self, m: &mut Machine, o: Cmp, wide: bool, a: V, b: V) -> CompileResult<V> {
        probe_guard(m)?;
        self.mark_site(m);
        let reg = if wide { 64 } else { 32 };
        let (la, wa) = self.int_parts(m, a)?;
        let (lb, wb) = self.int_parts(m, b)?;
        if let Some(v) = self.decided_cmp(o, &la, &lb) {
            return Ok(V::i32(v as u32));
        }
        let fact = matches!(o, Cmp::LtU | Cmp::LeU | Cmp::GtU | Cmp::GeU)
            .then(|| (o, la.clone(), lb.clone()));
        let mut n = wa.max(wb).max(1) as usize;
        let signed = matches!(o, Cmp::LtS | Cmp::GtS | Cmp::LeS | Cmp::GeS);
        let (mut la, mut lb) = (la, lb);
        if signed && n as u32 >= reg {
            // Two's complement order is unsigned order with the sign bit flipped:
            // `x ↦ x + 2^(reg−1) mod 2^reg`, i.e. `x + 2^(reg−1) − 2^reg·top(x)` with
            // `top(x) = 1 − [x < 2^(reg−1)]` (`x` is a `reg`-bit wire). LLVM writes
            // `x < 2^63` as `x ≥ 0` (signed), so this is common.
            la = self.sign_flip(la, reg)?;
            lb = self.sign_flip(lb, reg)?;
            n = reg as usize;
        }
        let lt =
            |h: &mut Self, x: LinearCombination, y: LinearCombination| h.b.emit_less_than(n, x, y);
        let lc = match o {
            Cmp::Eq | Cmp::Ne => {
                let z = self.b.emit_is_zero(la - lb);
                if o == Cmp::Eq {
                    z
                } else {
                    LinearCombination::one() - z
                }
            }
            Cmp::LtU | Cmp::LtS => lt(self, la, lb)?,
            Cmp::GtU | Cmp::GtS => lt(self, lb, la)?,
            Cmp::LeU | Cmp::LeS => LinearCombination::one() - lt(self, lb, la)?,
            Cmp::GeU | Cmp::GeS => LinearCombination::one() - lt(self, la, lb)?,
        };
        let out = self.new_wire(m, lc, 1);
        // A comparison in a witness-only region has no range proof behind it.
        if let Some(f) = fact
            && !self.b.witness_only
        {
            self.cmp_facts.insert(out.s, f);
        }
        Ok(out)
    }

    fn index_form(&mut self, m: &mut Machine, p: V) -> Option<(u64, Vec<u64>, V)> {
        if m.probing {
            return None;
        }
        let lc = self.int_lc(m, p).ok()?;
        const MAX: i128 = 1 << 10;
        // Each term's range: a pinned-boolean variable is 0..=1, one of known width
        // `w` is 0..2^w. The sum then lies in `lo..=hi`, on a grid of step `g` (the
        // coefficients' gcd); its candidates are every subset sum when all terms are
        // boolean (`x & 7`, `!x & 7` = `7 − Σ bits`), else that grid. A superset of
        // the possible values is fine: an impossible one is never selected.
        let (mut lo, mut hi, mut g, mut all_bool) = (0i128, 0i128, 0i128, true);
        let mut coeffs = Vec::with_capacity(lc.terms.len());
        for t in &lc.terms {
            let c = t.coeff.as_i64()? as i128;
            let vhi = if self.b.boolean_vars.contains(&t.var) {
                1
            } else {
                all_bool = false;
                let by_width = self
                    .var_width
                    .get(&t.var)
                    .filter(|&&w| w <= 20)
                    .map(|&w| (1i128 << w) - 1);
                let by_bound = self
                    .var_max
                    .get(&t.var)
                    .filter(|&&b| b < 1 << 20)
                    .map(|&b| b as i128);
                match (by_width, by_bound) {
                    (Some(a), Some(b)) => a.min(b),
                    (Some(a), None) | (None, Some(a)) => a,
                    (None, None) => return None,
                }
            };
            if c > 0 {
                hi += c * vhi;
            } else {
                lo += c * vhi;
            }
            g = gcd(g, c.abs());
            coeffs.push(c);
        }
        if g == 0 {
            return None;
        }
        let mut offsets: Vec<u64> = if all_bool && coeffs.len() <= 10 {
            (0..1usize << coeffs.len())
                .map(|mask| {
                    let s: i128 = coeffs
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| mask >> i & 1 == 1)
                        .map(|(_, c)| c)
                        .sum();
                    (s - lo) as u64
                })
                .collect()
        } else {
            if (hi - lo) / g + 1 > MAX {
                return None;
            }
            (0..=(hi - lo) / g).map(|j| (j * g) as u64).collect()
        };
        offsets.sort_unstable();
        offsets.dedup();
        if offsets.len() as i128 > MAX {
            return None;
        }
        let base = lc.constant.as_i64()? as i128 + lo;
        if !(0..1i128 << 32).contains(&base) {
            return None;
        }
        let rest = LinearCombination {
            constant: FieldConst::from_i64(-(lo as i64)),
            terms: lc.terms.clone(),
        };
        let max = *offsets.last()?;
        let idx = self.new_wire(m, rest, 64 - max.leading_zeros());
        let base = base as u64;
        Some((base, offsets, idx))
    }

    fn sign_extend(&mut self, m: &mut Machine, x: V, width: u32, reg: u32) -> CompileResult<V> {
        probe_guard(m)?;
        self.mark_site(m);
        self.sext_impl(m, x, width, reg)
    }

    fn require_cond(&mut self, m: &mut Machine, cond: u32, value: bool) -> CompileResult<()> {
        probe_guard(m)?;
        self.mark_site(m);
        let c = self.int_lc(m, V { b: 0, s: cond })?;
        let want = if value {
            LinearCombination::one()
        } else {
            LinearCombination::zero()
        };
        self.require_gated(c, want);
        if self.guards.is_empty() && !self.b.witness_only {
            self.learn_bound(cond, value);
        }
        Ok(())
    }

    fn arm_begin(&mut self, m: &mut Machine, cond: u32, value: bool) -> CompileResult<()> {
        let c = self.int_lc(m, V { b: 0, s: cond })?;
        let lit = if value {
            c
        } else {
            LinearCombination::one() - c
        };
        self.guards.push((lit, None));
        Ok(())
    }

    fn arm_end(&mut self) {
        self.guards.pop();
    }

    fn int_trunc(&mut self, m: &mut Machine, v: V, bits: u32) -> CompileResult<V> {
        probe_guard(m)?;
        self.mark_site(m);
        let (lc, w) = self.int_parts(m, v)?;
        self.int_result(m, lc, w, bits)
    }

    fn link(&mut self, module: &Module) -> CompileResult<()> {
        self.imports = module
            .imports
            .iter()
            .map(|i| {
                if i.module != "xark" {
                    return Err(CompileError::new(format!(
                        "the circuit imports `{}.{}`, which a circuit can't use",
                        i.module, i.name
                    ))
                    .with_help("only `xark` operations are available inside a circuit"));
                }
                intrinsic(&i.name).map(Some).ok_or_else(|| {
                    CompileError::new(format!("unknown xark intrinsic `{}`", i.name))
                        .with_help("the `xark` crate and the xark CLI are different versions")
                })
            })
            .collect::<CompileResult<_>>()?;
        Ok(())
    }

    fn emitted(&self) -> usize {
        self.partial
    }

    fn location(&self) -> Option<String> {
        None
    }

    fn call_begin(&mut self) {
        self.b.region_begin();
    }

    fn call_end(&mut self) {
        self.b.region_end();
    }

    fn not(&mut self, m: &mut Machine, c: V) -> CompileResult<V> {
        if !c.is_sym() {
            return Ok(V::i32((c.b == 0) as u32));
        }
        let lc = LinearCombination::one() - self.int_lc(m, c)?;
        Ok(self.new_wire(m, lc, 1))
    }

    fn bool_op(&mut self, m: &mut Machine, op: BoolOp, a: V, b: V) -> CompileResult<V> {
        probe_guard(m)?;
        self.mark_site(m);
        // Fold a concrete operand first (`x & 1`, `x | 0`, …).
        for (x, y) in [(a, b), (b, a)] {
            if !y.is_sym() {
                return Ok(match (op, y.b != 0) {
                    (BoolOp::And, true) | (BoolOp::Or, false) | (BoolOp::Xor, false) => x,
                    (BoolOp::And, false) => V::i32(0),
                    (BoolOp::Or, true) => V::i32(1),
                    (BoolOp::Xor, true) => return self.not(m, x),
                });
            }
        }
        let la = self.int_lc(m, a)?;
        let lb = self.int_lc(m, b)?;
        let out = match op {
            BoolOp::And => {
                self.b.consume_pending(&la);
                self.b.consume_pending(&lb);
                self.b.emit_mul(la, lb)
            }
            BoolOp::Or => self.b.emit_or(la, lb),
            BoolOp::Xor => self.b.emit_xor(la, lb),
        };
        Ok(self.new_wire(m, out, 1))
    }

    fn call(&mut self, m: &mut Machine, import: u32, a: &[V]) -> CompileResult<Option<V>> {
        self.mark_site(m);
        let intr = self.imports[import as usize].expect("linked");
        // Total intrinsics: every input has outputs satisfying what they emit (a
        // product row, `==`'s is-zero gadget, a booleanity-pinned XOR/OR, a hint the
        // solver can always compute). Anything else is partial.
        if !matches!(
            intr,
            Intr::Add
                | Intr::Sub
                | Intr::Neg
                | Intr::Mul
                | Intr::Pow
                | Intr::Xor
                | Intr::Or
                | Intr::Eq
                | Intr::BoolToField
                | Intr::HintInverseOrZero
                | Intr::HintBit
                | Intr::WitnessBegin
                | Intr::WitnessEnd
                | Intr::Panic
                | Intr::RequireEq
                | Intr::ToBitsLookup
                | Intr::InputSchema
        ) && !(matches!(
            intr,
            Intr::Ult
                | Intr::HintInverse
                | Intr::ToBitsRecord
                | Intr::HintDivRem
                | Intr::HintMulModDivMod
                | Intr::HintModInverse
                | Intr::HintSub2
        ) && !self.guards.is_empty())
            && intr != Intr::Advice
        {
            self.partial += 1;
        }
        match intr {
            Intr::Add | Intr::Sub => {
                let (out, reduce) = self.add_fields(m, a[1], a[2], intr == Intr::Sub)?;
                if reduce {
                    self.put_field(m, a[0], out)?;
                } else {
                    let words = self.field_words(m, out);
                    m.write_words(ptr_of(a[0])?, &words)?;
                }
            }
            Intr::Neg => {
                let x = self.get_field(m, a[1])?;
                self.b.consume_pending(&x);
                self.put_field(m, a[0], -x)?;
            }
            Intr::Mul => {
                let lhs = self.get_field(m, a[1])?;
                let rhs = self.get_field(m, a[2])?;
                // Constant * anything is linear: fold into the coefficients.
                let out = if lhs.is_constant() {
                    self.b.consume_pending(&rhs);
                    rhs.scale(&lhs.constant)
                } else if rhs.is_constant() {
                    self.b.consume_pending(&lhs);
                    lhs.scale(&rhs.constant)
                } else {
                    self.b.consume_pending(&lhs);
                    self.b.consume_pending(&rhs);
                    // A product is a single variable: write its handle directly
                    // (what `put_field` of `1·v` writes).
                    let v = self.b.emit_mul_var(lhs, rhs);
                    m.write_words(ptr_of(a[0])?, &[v as u64, KIND_VAR, MAGIC, SENTINEL])?;
                    return Ok(None);
                };
                self.put_field(m, a[0], out)?;
            }
            Intr::Pow => {
                let base = self.get_field(m, a[1])?;
                self.b.consume_pending(&base);
                let n = int_of(a[2], "the exponent of `pow`")?;
                // A constant base is a constant power: fold it (as `mul` folds
                // constant operands) rather than emit `c·c = t` rows. Needs the
                // modulus.
                let out = match &self.reduce {
                    Some((p, _))
                        if base.is_constant()
                            && crate::builder::dev_knob("XARK_NO_POWFOLD").is_none() =>
                    {
                        let mut b = base.constant.big() % p;
                        if b < BigInt::from(0) {
                            b += p;
                        }
                        let mut lc = LinearCombination::zero();
                        lc.constant = FieldConst::from_bigint(b.modpow(&BigInt::from(n), p));
                        lc
                    }
                    _ => self.b.emit_pow(base, n),
                };
                self.put_field(m, a[0], out)?;
            }
            Intr::Xor | Intr::Or => {
                let x = self.get_field(m, a[1])?;
                let y = self.get_field(m, a[2])?;
                let out = if intr == Intr::Xor {
                    self.b.emit_xor(x, y)
                } else {
                    self.b.emit_or(x, y)
                };
                self.put_field(m, a[0], out)?;
            }
            Intr::Eq => {
                self.cmp_calls += 1;
                let x = self.get_field(m, a[0])?;
                let y = self.get_field(m, a[1])?;
                let out = self.b.emit_is_zero(x - y);
                return Ok(Some(self.new_wire(m, out, 1)));
            }
            Intr::Ult => {
                self.cmp_calls += 1;
                let x = self.get_field(m, a[0])?;
                let y = self.get_field(m, a[1])?;
                let n = int_of(a[2], "the comparison width `N`")? as usize;
                // In an arm, `x, y < 2^n` (the range proof) binds only if it's taken.
                let g = self.guard();
                let out = self.b.emit_less_than_gated(n, x, y, g)?;
                return Ok(Some(self.new_wire(m, out, 1)));
            }
            Intr::BoolToField => {
                let lc = self.int_lc(m, a[1])?;
                self.put_field(m, a[0], lc)?;
            }
            Intr::Advice => {
                // In an arm, `0` where it isn't taken: whatever pins it there is
                // guarded, so the pin keeps it determined.
                let v = self.b.alloc_advice();
                let g = self.guard();
                self.b.pin_dead(g.as_ref(), v);
                self.put_field(m, a[0], LinearCombination::var(v))?;
            }
            Intr::HintInverse | Intr::HintInverseOrZero => {
                let x = self.get_field(m, a[1])?;
                let g = self.guard();
                let x = self.b.gate_input(g.as_ref(), x);
                let v = self.b.alloc_advice();
                self.b.pin_dead(g.as_ref(), v);
                // In an arm, an inverse of 0 must still solve (the caller's
                // `x · inv = 1` is guarded): hint inverse-or-zero there.
                let w = if intr == Intr::HintInverse && self.guards.is_empty() {
                    xark_ir::primitive::WitnessGen::Inverse { out: v, input: x }
                } else {
                    xark_ir::primitive::WitnessGen::InverseOrZero { out: v, input: x }
                };
                self.b.witness_gen.push(Some(w));
                self.put_field(m, a[0], LinearCombination::var(v))?;
            }
            Intr::HintBit => {
                let x = self.get_field(m, a[1])?;
                let index = int_of(a[2], "the bit index of `hint_bit`")? as u32;
                let g = self.guard();
                let x = self.b.gate_input(g.as_ref(), x);
                let v = self.b.alloc_advice();
                self.b.pin_dead(g.as_ref(), v);
                self.b
                    .witness_gen
                    .push(Some(xark_ir::primitive::WitnessGen::Bit {
                        out: v,
                        input: x,
                        index,
                    }));
                self.put_field(m, a[0], LinearCombination::var(v))?;
            }
            Intr::HintDivRem => {
                // In an arm: `g·num / (g·den + 1 − g)`, so `q = r = 0` where it isn't
                // taken (pinned so) and the hint never divides by zero there.
                let g = self.guard();
                let num = self.get_field(m, a[1])?;
                let num = self.b.gate_input(g.as_ref(), num);
                let den = self.get_field(m, a[2])?;
                let den = self
                    .gate_limbs(g.as_ref(), vec![den], 1)
                    .pop()
                    .expect("one");
                let q = self.b.alloc_advice();
                let r = self.b.alloc_advice();
                self.b.pin_dead(g.as_ref(), q);
                self.b.pin_dead(g.as_ref(), r);
                self.b
                    .witness_gen
                    .push(Some(xark_ir::primitive::WitnessGen::DivRem {
                        q,
                        r,
                        num,
                        den,
                    }));
                let out = ptr_of(a[0])?;
                self.put_field(m, V::i32(out), LinearCombination::var(q))?;
                self.put_field(m, V::i32(out + 32), LinearCombination::var(r))?;
            }
            Intr::HintMulModDivMod => {
                // (q_out, r_out, a, b, m, n, bits)
                let n = int_of(a[5], "the limb count")? as usize;
                let bits = int_of(a[6], "the limb width")? as u32;
                // In an arm: `(g·a)(g·b) mod (g·m + 1 − g)` — `0 mod 1` where untaken.
                let g = self.guard();
                let x = self.get_fields(m, a[2], n)?;
                let x = self.gate_limbs(g.as_ref(), x, 0);
                let y = self.get_fields(m, a[3], n)?;
                let y = self.gate_limbs(g.as_ref(), y, 0);
                let md = self.get_fields(m, a[4], n)?;
                let md = self.gate_limbs(g.as_ref(), md, 1);
                let q: Vec<u32> = (0..n).map(|_| self.b.alloc_advice()).collect();
                let r: Vec<u32> = (0..n).map(|_| self.b.alloc_advice()).collect();
                for &v in q.iter().chain(&r) {
                    self.b.pin_dead(g.as_ref(), v);
                }
                self.b
                    .witness_gen
                    .push(Some(xark_ir::primitive::WitnessGen::MulModDivMod {
                        q: q.clone(),
                        r: r.clone(),
                        a: x,
                        b: y,
                        modulus: md,
                        limb_bits: bits,
                    }));
                self.put_vars(m, a[0], &q)?;
                self.put_vars(m, a[1], &r)?;
            }
            Intr::HintModInverse => {
                // (out, a, m, n, bits)
                let n = int_of(a[3], "the limb count")? as usize;
                let bits = int_of(a[4], "the limb width")? as u32;
                // In an arm: `1⁻¹ mod 2 = 1` where untaken (limb 0 pinned to 1).
                let g = self.guard();
                let x = self.get_fields(m, a[1], n)?;
                let x = self.gate_limbs(g.as_ref(), x, 1);
                let md = self.get_fields(m, a[2], n)?;
                let md = self.gate_limbs(g.as_ref(), md, 2);
                let out: Vec<u32> = (0..n).map(|_| self.b.alloc_advice()).collect();
                for (i, &v) in out.iter().enumerate() {
                    self.b.pin_dead_to(g.as_ref(), v, i64::from(i == 0));
                }
                self.b
                    .witness_gen
                    .push(Some(xark_ir::primitive::WitnessGen::ModInverse {
                        out: out.clone(),
                        a: x,
                        modulus: md,
                        limb_bits: bits,
                    }));
                self.put_vars(m, a[0], &out)?;
            }
            Intr::HintSub2 => {
                // (qabs_out, r_out, a, b, c, m, n, bits)
                let n = int_of(a[6], "the limb count")? as usize;
                let bits = int_of(a[7], "the limb width")? as u32;
                // In an arm: `0 + 2·1 − 0 − 0 = 2·1`, so `qabs = r = 0` where untaken.
                let g = self.guard();
                let x = self.get_fields(m, a[2], n)?;
                let x = self.gate_limbs(g.as_ref(), x, 0);
                let y = self.get_fields(m, a[3], n)?;
                let y = self.gate_limbs(g.as_ref(), y, 0);
                let z = self.get_fields(m, a[4], n)?;
                let z = self.gate_limbs(g.as_ref(), z, 0);
                let md = self.get_fields(m, a[5], n)?;
                let md = self.gate_limbs(g.as_ref(), md, 1);
                let qabs = self.b.alloc_advice();
                let r: Vec<u32> = (0..n).map(|_| self.b.alloc_advice()).collect();
                self.b.pin_dead(g.as_ref(), qabs);
                for &v in &r {
                    self.b.pin_dead(g.as_ref(), v);
                }
                self.b
                    .witness_gen
                    .push(Some(xark_ir::primitive::WitnessGen::Sub2 {
                        qabs,
                        r: r.clone(),
                        a: x,
                        b: y,
                        c: z,
                        modulus: md,
                        limb_bits: bits,
                    }));
                self.put_field(m, a[0], LinearCombination::var(qabs))?;
                self.put_vars(m, a[1], &r)?;
            }
            Intr::RequireEq => {
                let x = self.get_field(m, a[0])?;
                let y = self.get_field(m, a[1])?;
                self.require_gated(x, y);
            }
            Intr::WitnessBegin => self.b.witness_only = true,
            Intr::WitnessEnd => self.b.witness_only = false,
            Intr::ToBitsLookup => {
                // (x, n, out) → 1 if `out` was filled (constant / shortcut / cache hit).
                let x = self.get_field(m, a[0])?;
                let n = int_of(a[1], "the width of `to_bits`")? as usize;
                let out = ptr_of(a[2])?;
                let bits: Option<Vec<LinearCombination>> = if x.is_constant() {
                    let bits = x.constant.to_bits_le(n).ok_or_else(|| {
                        CompileError::new(format!(
                            "constant `{}` does not fit in {n} bits",
                            x.constant.decimal()
                        ))
                        .with_note(
                            "`Field::to_bits::<N>` of a constant requires `0 <= value < 2^N`",
                        )
                        // Unsatisfiable wherever this runs: in a witness branch, the
                        // arm can't be taken (like a panic there).
                        .diverging()
                    })?;
                    Some(
                        bits.into_iter()
                            .map(|b| {
                                if b {
                                    LinearCombination::one()
                                } else {
                                    LinearCombination::zero()
                                }
                            })
                            .collect(),
                    )
                } else if let Some(vars) = self.b.bit_sum_shortcut(&x, n) {
                    Some(vars.into_iter().map(LinearCombination::var).collect())
                } else {
                    self.b
                        .bit_cache
                        .get(&(canonical_lc_key(&x), n))
                        .cloned()
                        .map(|vars| vars.into_iter().map(LinearCombination::var).collect())
                };
                return Ok(Some(match bits {
                    Some(bits) => {
                        for (i, lc) in bits.into_iter().enumerate() {
                            self.put_field(m, V::i32(out + 32 * i as u32), lc)?;
                        }
                        V::i32(1)
                    }
                    None => V::i32(0),
                }));
            }
            Intr::ToBitsRecord => {
                // (x, n, bits): remember the decomposition just emitted.
                let x = self.get_field(m, a[0])?;
                let n = int_of(a[1], "the width of `to_bits`")? as usize;
                let bits = self.get_fields(m, a[2], n)?;
                let vars: Option<Vec<u32>> = bits
                    .iter()
                    .map(|lc| {
                        (lc.constant.is_zero() && lc.terms.len() == 1 && lc.terms[0].coeff.is_one())
                            .then(|| lc.terms[0].var)
                    })
                    .collect();
                // Not in an arm: there the recomposition is guarded, so the bits
                // are `x`'s only where the arm is taken.
                if let Some(vars) = vars
                    && self.guards.is_empty()
                    && !self.b.witness_only
                {
                    self.b.bit_cache.insert((canonical_lc_key(&x), n), vars);
                }
            }
            Intr::InputField | Intr::InputUint | Intr::InputBool => {
                // field: (out, name, len, vis) ; uint: (name, len, vis, width) -> i64 ;
                // bool: (name, len, vis) -> i32, a `u1` (range-checked with the `uN`s)
                let (name_at, len_at, vis_at) = if intr == Intr::InputField {
                    (1, 2, 3)
                } else {
                    (0, 1, 2)
                };
                let name = String::from_utf8(
                    m.read_bytes(ptr_of(a[name_at])?, int_of(a[len_at], "len")? as u32)?,
                )
                .map_err(|_| CompileError::new("input name is not UTF-8"))?;
                let vis = if int_of(a[vis_at], "visibility")? == 1 {
                    Visibility::Public
                } else {
                    Visibility::Private
                };
                let width = match intr {
                    Intr::InputUint => Some(a[3].b as u32),
                    Intr::InputBool => Some(1),
                    _ => None,
                };
                self.leaves
                    .push((name.clone(), matches!(vis, Visibility::Public), width));
                let id = self.b.alloc_var(name, vis);
                self.b.input_ids.push(id);
                self.n_inputs += 1;
                if intr == Intr::InputField {
                    self.put_field(m, a[0], LinearCombination::var(id))?;
                } else {
                    let width = match intr {
                        Intr::InputBool => 1,
                        _ => int_of(a[3], "width")? as u32,
                    };
                    if width > 64 {
                        // A `u128` spans two wasm registers: range-check it now and
                        // hand out its halves, recomposed from the check's bits.
                        let x = LinearCombination::var(id);
                        self.b.kind_stack.push(ConstraintKind::RangeCheck);
                        let bits: Vec<LinearCombination> = self
                            .b
                            .decompose_bits(x.clone(), width as usize)
                            .into_iter()
                            .map(LinearCombination::var)
                            .collect();
                        self.b.kind_stack.pop();
                        let lo = Self::recompose(&bits[..64]);
                        self.pending_hi = Some(Self::recompose(&bits[64..]));
                        return Ok(Some(self.new_wire(m, lo, 64)));
                    }
                    self.uint_inputs.push((id, width));
                    return Ok(Some(self.new_wire(m, LinearCombination::var(id), width)));
                }
            }
            Intr::InputSchema => {
                let json = String::from_utf8_lossy(
                    &m.read_bytes(ptr_of(a[0])?, int_of(a[1], "len")? as u32)?,
                )
                .into_owned();
                self.schema = Some(json);
            }
            Intr::InputUintHi => {
                let hi = self.pending_hi.take().ok_or_else(|| {
                    CompileError::new("internal error: no `u128` input to take the high half of")
                })?;
                return Ok(Some(self.new_wire(m, hi, 64)));
            }
            Intr::InputsDone => {
                // Every input is a var in `0..n_inputs`; now range-check the `uN` ones.
                for (id, n) in std::mem::take(&mut self.uint_inputs) {
                    self.b.kind_stack.push(ConstraintKind::RangeCheck);
                    self.b
                        .emit_range_proof_lc(LinearCombination::var(id), n as usize);
                    self.b.kind_stack.pop();
                }
            }
            Intr::Panic => {
                let msg = String::from_utf8_lossy(
                    &m.read_bytes(ptr_of(a[0])?, int_of(a[1], "len")? as u32)?,
                )
                .into_owned();
                let file = String::from_utf8_lossy(
                    &m.read_bytes(ptr_of(a[2])?, int_of(a[3], "len")? as u32)?,
                )
                .into_owned();
                let mut e = CompileError::new(format!("the circuit panicked: {msg}")).diverging();
                if !file.is_empty() {
                    e.location = Some(format!("{file}:{}:{}", a[4].b as u32, a[5].b as u32));
                }
                return Err(e);
            }
        }
        Ok(None)
    }
}

impl Host {
    fn put_vars(&mut self, m: &mut Machine, ptr: V, vars: &[u32]) -> CompileResult<()> {
        let base = ptr_of(ptr)?;
        for (i, &v) in vars.iter().enumerate() {
            self.put_field(m, V::i32(base + 32 * i as u32), LinearCombination::var(v))?;
        }
        Ok(())
    }
}

enum View {
    Var(u32),
    Slot(usize),
    Owned(LinearCombination),
}

fn canonical(t: &[xark_ir::Term]) -> bool {
    t.windows(2).all(|w| w[0].var < w[1].var) && !t.iter().any(|x| x.coeff.is_zero())
}

/// `(ca + Σ ta) ± (cb + Σ tb)` in canonical form (sorted vars, merged, no zeros) —
/// equal to `LinearCombination`'s `+`/`-` on the same operands. The flag: the result
/// has a big value the merge computed (a sum, or anything off the fallback path).
fn merge_lc(
    ca: &FieldConst,
    ta: &[xark_ir::Term],
    cb: &FieldConst,
    tb: &[xark_ir::Term],
    neg_b: bool,
) -> (LinearCombination, bool) {
    let nb = |c: &FieldConst| if neg_b { c.neg() } else { c.clone() };
    let constant = ca.add(&nb(cb));
    let mut big = constant.as_big().is_some();
    if !(canonical(ta) && canonical(tb)) {
        let a = LinearCombination {
            constant: FieldConst::zero(),
            terms: ta.to_vec(),
        };
        let b = LinearCombination {
            constant: FieldConst::zero(),
            terms: tb.to_vec(),
        };
        let mut r = if neg_b { a - b } else { a + b };
        r.constant = constant;
        return (r, true);
    }
    let mut out = Vec::with_capacity(ta.len() + tb.len());
    let b_term = |t: &xark_ir::Term| xark_ir::Term {
        coeff: nb(&t.coeff),
        var: t.var,
    };
    // Disjoint variable ranges (an accumulation `acc + x` with a fresh `x`): the
    // merge is a concatenation.
    match (ta.first(), ta.last(), tb.first(), tb.last()) {
        (_, Some(la), Some(fb), _) if la.var < fb.var => {
            out.extend_from_slice(ta);
            out.extend(tb.iter().map(b_term));
            return (
                LinearCombination {
                    constant,
                    terms: out,
                },
                big,
            );
        }
        (Some(fa), _, _, Some(lb)) if lb.var < fa.var => {
            out.extend(tb.iter().map(b_term));
            out.extend_from_slice(ta);
            return (
                LinearCombination {
                    constant,
                    terms: out,
                },
                big,
            );
        }
        (None, ..) | (_, _, None, _) => {
            out.extend_from_slice(ta);
            out.extend(tb.iter().map(b_term));
            return (
                LinearCombination {
                    constant,
                    terms: out,
                },
                big,
            );
        }
        _ => {}
    }
    let (mut i, mut j) = (0, 0);
    while i < ta.len() || j < tb.len() {
        if j == tb.len() || (i < ta.len() && ta[i].var < tb[j].var) {
            out.push(ta[i].clone());
            i += 1;
        } else if i == ta.len() || tb[j].var < ta[i].var {
            out.push(xark_ir::Term {
                coeff: nb(&tb[j].coeff),
                var: tb[j].var,
            });
            j += 1;
        } else {
            let c = ta[i].coeff.add(&nb(&tb[j].coeff));
            if !c.is_zero() {
                big |= c.as_big().is_some();
                out.push(xark_ir::Term {
                    coeff: c,
                    var: ta[i].var,
                });
            }
            i += 1;
            j += 1;
        }
    }
    (
        LinearCombination {
            constant,
            terms: out,
        },
        big,
    )
}

fn pow2(k: u32) -> BigInt {
    BigInt::from(1u8) << k
}

fn lc_of(v: &BigInt) -> LinearCombination {
    LinearCombination::constant(v.to_string())
}

fn gcd(a: i128, b: i128) -> i128 {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// A probe (see `crate::interp`) must not emit anything: end it at the first op
/// that would.
fn probe_guard(m: &Machine) -> CompileResult<()> {
    if m.probing {
        return Err(CompileError::new("probe: the path touches witness data"));
    }
    Ok(())
}
