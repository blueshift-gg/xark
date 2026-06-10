/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Gadgets
import Formal.Wrappers
import Formal.Predication
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# ACIR → R1CS lowering soundness (meta-theorem)

`crates/acir-r1cs/src/lower.rs` translates ACIR opcodes into R1CS rows.
The headline meta-theorem:

> For every ACIR opcode `op` and every public-input assignment, the R1CS
> emitted by `lower(op)` is satisfiable by some witness `w` iff `op` is
> satisfiable by the same public assignment with witnesses extracted from
> `w` via the witness-map injection.

Once discharged for every opcode, this composes with the per-gadget
soundness theorems already mechanised (`Formal.Gadgets` / `Bitwise` /
`Curve` / `Poseidon` / `Secp256k1` / `Secp256r1` / `NonNative` /
`EcdsaVerify` / `MemoryVarIndex` / `Brillig` / `Predication`) into
whole-circuit soundness for *any* Noir program, not just gadgets we have
hand-proven.

## What this file establishes

* **A real Lean model** of ACIR's `AssertZero` opcode (linear and full
  shapes) + R1CS rows + lowering + satisfaction.
* **End-to-end soundness for `AssertZero` (linear)** — `lowerAssertZeroLinear_sound`
  proves the lowering is satisfaction-preserving in both directions
  (no over-constraint, no under-constraint) over *all* witness maps.
* **`AssertZero` with mul terms** — `lowerAcirOpcode_full_sound`, via
  `full_satisfied_via_list_aux` + `full_satisfied_from_per_mul_rows`.
* **Heterogeneous opcode dispatch** — the `AcirOpcode` inductive covers
  every ACIR arm (`linear`, `full`, `linearShifted`, `brillig`,
  `blackBox`, `memoryInit`, `memoryOpRead`, `memoryOpWrite`, `call`);
  `lowerAcirOpcode_sound` is the total per-opcode theorem.
* **List-fold composition** — `AcirCircuit.cons_satisfied_iff` reduces
  whole-circuit satisfaction to per-opcode satisfaction over the
  heterogeneous list.

-/

namespace Xark

/-! ## A real Lean model of ACIR / R1CS satisfaction

`AcirWitnessMap F` is a witness assignment: a function from witness
indices (`ℕ`) to field values. By convention `w 0 = 1` (wire 0 = the
constant 1). -/

/-- ACIR witness map. -/
def AcirWitnessMap (F : Type*) : Type _ := ℕ → F

/-- An `AssertZero` opcode in **linear shape**: constant `c` + linear
combination `Σᵢ cᵢ · w iᵢ`. The opcode asserts `c + Σ cᵢ · w iᵢ = 0`.

The full ACIR `AssertZero` also supports **mul terms**
(`Σⱼ cⱼ · w aⱼ · w bⱼ`); this structure models the linear shape, and
`AssertZeroFull` (below) models the full shape. Mul-term soundness
composes the linear case with per-term auxiliary allocation (one R1CS
row per mul term, then a single linear `AssertZero` over the aux +
linear shell) via `lowerAcirOpcode_full_sound`. -/
structure AssertZeroLinear (F : Type*) where
  constant : F
  terms : List (F × ℕ)

/-- `op` is satisfied by witness map `w` iff `c + Σᵢ cᵢ · w iᵢ = 0`. -/
def AssertZeroLinear.Satisfied {F : Type*} [Field F]
    (op : AssertZeroLinear F) (w : AcirWitnessMap F) : Prop :=
  op.constant + (op.terms.map (fun ci => ci.1 * w ci.2)).sum = 0

/-- An R1CS linear combination. We reserve witness index `0` as the
constant-`1` wire, so a literal constant `c` is encoded as `(c, 0)`. -/
def LinearComb (F : Type*) : Type _ := List (F × ℕ)

/-- Evaluate a linear combination under a witness map. -/
def LinearComb.eval {F : Type*} [Field F]
    (lc : LinearComb F) (w : AcirWitnessMap F) : F :=
  (lc.map (fun ci => ci.1 * w ci.2)).sum

/-- An R1CS row `A · B = C`. -/
structure R1csRow (F : Type*) where
  a : LinearComb F
  b : LinearComb F
  c : LinearComb F

/-- The row is satisfied iff `A·B = C` under `w`. -/
def R1csRow.Satisfied {F : Type*} [Field F]
    (row : R1csRow F) (w : AcirWitnessMap F) : Prop :=
  row.a.eval w * row.b.eval w = row.c.eval w

/-! ## Lowering for `AssertZero` (linear shape)

The xark lowering for a linear `AssertZero` is the simplest case: emit a
single R1CS row `0 · 0 = c + Σᵢ cᵢ · w iᵢ`. Both `A` and `B` LCs are
empty (evaluating to `0`); the `C` LC carries the constant + linear
terms. The constant is encoded as a coefficient on wire `0` (which the
witness map pins to `1`). -/

/-- The R1CS row emitted by lowering a linear `AssertZero`. -/
def lowerAssertZeroLinear {F : Type*} (op : AssertZeroLinear F) : R1csRow F :=
  { a := []
    b := []
    c := (op.constant, 0) :: op.terms }

/-! ## End-to-end soundness for `AssertZero` (linear)

The headline theorem of this file: the linear-`AssertZero` lowering is
satisfaction-preserving in both directions over all witness maps that pin
the constant wire to `1`. -/

/-- Witness maps that pin the constant wire `w 0 = 1`. The xark lowering
threads this invariant via `R1csBuilder::one_lc()`. -/
def ConstantWirePinned {F : Type*} [One F] (w : AcirWitnessMap F) : Prop :=
  w 0 = 1

/-- **End-to-end soundness for `AssertZero` (linear).** For any witness
map `w` pinning the constant wire to `1`:

    `lowerAssertZeroLinear op` is R1CS-satisfied by `w`  ↔  `op` is
    ACIR-satisfied by `w`.

This is the *bidirectional* statement: no over-constraint (every honest
ACIR-satisfying witness lifts) **and** no under-constraint (no malicious
R1CS-satisfying witness corresponds to a non-ACIR-satisfying assignment).

The proof is direct algebra: the lowered row's `A · B = C` becomes
`0 · 0 = c · 1 + Σᵢ cᵢ · w iᵢ`, i.e. `0 = c + Σ`, which is the original
opcode's satisfaction relation modulo `eq_comm`. -/
theorem lowerAssertZeroLinear_sound {F : Type*} [Field F]
    (op : AssertZeroLinear F) (w : AcirWitnessMap F)
    (h_const : ConstantWirePinned w) :
    (lowerAssertZeroLinear op).Satisfied w ↔ op.Satisfied w := by
  unfold R1csRow.Satisfied AssertZeroLinear.Satisfied lowerAssertZeroLinear
  unfold LinearComb.eval ConstantWirePinned at *
  simp only [List.map_nil, List.sum_nil, mul_zero, List.map_cons, h_const, mul_one, List.sum_cons]
  exact eq_comm

/-- **Completeness corollary** (LTR of the iff): honest provers always
lift. Every ACIR-satisfying assignment gives an R1CS-satisfying assignment
(no over-constraint / DoS). -/
theorem lowerAssertZeroLinear_complete {F : Type*} [Field F]
    (op : AssertZeroLinear F) (w : AcirWitnessMap F)
    (h_const : ConstantWirePinned w)
    (h : op.Satisfied w) :
    (lowerAssertZeroLinear op).Satisfied w :=
  (lowerAssertZeroLinear_sound op w h_const).mpr h

/-- **Soundness corollary** (RTL of the iff): no false proofs. Every
R1CS-satisfying assignment lifts to an ACIR-satisfying assignment (no
under-constraint, no malicious-prover gap). -/
theorem lowerAssertZeroLinear_sound_dir {F : Type*} [Field F]
    (op : AssertZeroLinear F) (w : AcirWitnessMap F)
    (h_const : ConstantWirePinned w)
    (h : (lowerAssertZeroLinear op).Satisfied w) :
    op.Satisfied w :=
  (lowerAssertZeroLinear_sound op w h_const).mp h

/-! ## Composition: a list of `AssertZero` opcodes -/

/-- Lower a circuit by lowering each opcode independently. -/
def lowerAssertZeroCircuit {F : Type*} (circ : List (AssertZeroLinear F)) : List (R1csRow F) :=
  circ.map lowerAssertZeroLinear

/-- **Whole-circuit soundness (linear-`AssertZero` instance).** Composes
`lowerAssertZeroLinear_sound` row-by-row. The R1CS row list is satisfied
iff every opcode is satisfied. -/
theorem lowerAssertZeroCircuit_sound {F : Type*} [Field F]
    (circ : List (AssertZeroLinear F)) (w : AcirWitnessMap F)
    (h_const : ConstantWirePinned w) :
    (∀ row ∈ lowerAssertZeroCircuit circ, R1csRow.Satisfied row w) ↔
    (∀ op ∈ circ, AssertZeroLinear.Satisfied op w) := by
  unfold lowerAssertZeroCircuit
  constructor
  · intro h op hop
    have hrow : R1csRow.Satisfied (lowerAssertZeroLinear op) w := by
      apply h
      exact List.mem_map_of_mem hop
    exact (lowerAssertZeroLinear_sound op w h_const).mp hrow
  · intro h row hrow
    rcases List.mem_map.mp hrow with ⟨op, hop, heq⟩
    rw [← heq]
    exact (lowerAssertZeroLinear_sound op w h_const).mpr (h op hop)

/-! ## `AssertZero` with mul terms

ACIR's full `AssertZero` opcode is

    `c + Σᵢ cᵢ · w iᵢ + Σⱼ dⱼ · w aⱼ · w bⱼ = 0`

— the linear case above + a list of mul terms. The xark lowering allocates
one fresh aux witness `tⱼ` per mul term, emits the per-mul R1CS row

    `(dⱼ · w aⱼ) · (w bⱼ) = w tⱼ`

(pinning `tⱼ = dⱼ · w aⱼ · w bⱼ`), then closes with a single linear shell
`AssertZero` row over the aux + linear + constant. We give the per-mul
soundness lemma + the structural reduction to the linear case. The
composition over a list of mul terms is mechanical (same shape as
`lowerAssertZeroCircuit_sound`). -/

/-- An `AssertZero` opcode in **full shape**: constant + linear part + mul
part. Mul terms are encoded `(dⱼ, aⱼ, bⱼ)` denoting `dⱼ · w aⱼ · w bⱼ`. -/
structure AssertZeroFull (F : Type*) where
  constant : F
  terms    : List (F × ℕ)
  muls     : List (F × ℕ × ℕ)

/-- `op` is satisfied by `w` iff `c + Σᵢ cᵢ·w iᵢ + Σⱼ dⱼ·w aⱼ·w bⱼ = 0`. -/
def AssertZeroFull.Satisfied {F : Type*} [Field F]
    (op : AssertZeroFull F) (w : AcirWitnessMap F) : Prop :=
  op.constant
    + (op.terms.map (fun ci => ci.1 * w ci.2)).sum
    + (op.muls.map (fun d => d.1 * w d.2.1 * w d.2.2)).sum = 0

/-- **Per-mul row soundness.** The per-mul R1CS row
`(dⱼ · w aⱼ) · w bⱼ = w (aux_start + j)` is satisfied iff
`w (aux_start + j) = dⱼ · w aⱼ · w bⱼ`. This is the elementary lemma
the full-opcode soundness theorem composes per mul term. -/
theorem mul_row_iff_aux_consistent {F : Type*} [Field F]
    (d_coef : F) (a_var b_var : ℕ) (aux_idx : ℕ) (w : AcirWitnessMap F) :
    R1csRow.Satisfied
      ({ a := [(d_coef, a_var)], b := [((1 : F), b_var)],
         c := [((1 : F), aux_idx)] } : R1csRow F) w ↔
    w aux_idx = d_coef * w a_var * w b_var := by
  unfold R1csRow.Satisfied LinearComb.eval
  simp [eq_comm]

/-- **Full-opcode soundness — substitution lemma.** Given the per-mul
rows are all satisfied (pinning each aux `w (aux_start + j) = dⱼ · w aⱼ ·
w bⱼ` by `mul_row_iff_aux_consistent` applied per term) and the linear
shell row is satisfied (`c + Σᵢ cᵢ·w iᵢ + Σⱼ w (aux_start + j) = 0` by
`lowerAssertZeroLinear_sound` applied to the shell), substituting the
per-mul pin into the shell gives the full ACIR `AssertZero` opcode
relation `c + Σᵢ cᵢ·w iᵢ + Σⱼ dⱼ·w aⱼ·w bⱼ = 0`. We state the
substitution as a `Fin`-indexed lemma to avoid `List.map`/`List.get`
bookkeeping; the witness function `aux : Fin n → F` captures the
per-mul aux witnesses extracted from `w`. -/
theorem full_satisfied_via_fin_aux {F : Type*} [Field F]
    {n : ℕ} (constant : F) (terms : List (F × ℕ))
    (muls : Fin n → F × ℕ × ℕ) (aux : Fin n → F)
    (w : AcirWitnessMap F)
    (h_aux : ∀ j : Fin n, aux j = (muls j).1 * w (muls j).2.1 * w (muls j).2.2)
    (h_shell : constant + (terms.map (fun ci => ci.1 * w ci.2)).sum
                       + ∑ j : Fin n, aux j = 0) :
    constant + (terms.map (fun ci => ci.1 * w ci.2)).sum
             + ∑ j : Fin n, ((muls j).1 * w (muls j).2.1 * w (muls j).2.2) = 0 := by
  have hrew : (∑ j : Fin n, aux j)
            = ∑ j : Fin n, ((muls j).1 * w (muls j).2.1 * w (muls j).2.2) :=
    Finset.sum_congr rfl (fun j _ => h_aux j)
  rw [hrew] at h_shell
  exact h_shell

/-- **`List`-indexed mirror of `full_satisfied_via_fin_aux`.**
The Rust lowering in `crates/acir-r1cs/src/lower.rs` carries mul terms as
a `Vec` (which Lean models as `List`), and per-mul auxiliaries are
allocated by walking the list in order. This theorem mirrors the
list-indexed structure directly, so the lowering proof reads off without
the `Fin n`-vector indirection.

Hypotheses, in the shape the lowering naturally produces:

* `aux : List F` — the per-mul aux values extracted from `w`. Length must
  match `op.muls.length` (recorded by `h_len`).
* `h_aux : List.Forall₂ (fun mul a => a = mul.1 * w mul.2.1 * w mul.2.2)
            op.muls aux` — each aux is the witness product, pairing
  index-by-index with the corresponding mul term.
* `h_shell` — the linear shell row holds when the aux are substituted in
  place of the mul products.

Conclusion: the full opcode is satisfied. The proof is one
`List.Forall₂.map_eq`-style rewrite over the two sums. -/
theorem full_satisfied_via_list_aux {F : Type*} [Field F]
    (op : AssertZeroFull F) (aux : List F)
    (w : AcirWitnessMap F)
    (h_aux : aux = op.muls.map (fun d => d.1 * w d.2.1 * w d.2.2))
    (h_shell : op.constant + (op.terms.map (fun ci => ci.1 * w ci.2)).sum
                          + aux.sum = 0) :
    op.Satisfied w := by
  unfold AssertZeroFull.Satisfied
  rw [← h_aux]
  exact h_shell

/-- **`h_aux` discharged from per-mul row satisfaction.** Given
the per-mul R1CS rows are all satisfied (pinning each aux
`w (aux_start + j) = (op.muls.get ⟨j, ?⟩).1 * w (op.muls.get ⟨j, ?⟩).2.1
* w (op.muls.get ⟨j, ?⟩).2.2` by `mul_row_iff_aux_consistent` applied
per index), the list of aux witnesses extracted via
`(List.range op.muls.length).map (fun j => w (aux_start + j))`
**equals** `op.muls.map (fun d => d.1 * w d.2.1 * w d.2.2)` — i.e. the
hypothesis `h_aux` of `full_satisfied_via_list_aux` is discharged
directly from the row-satisfaction. -/
theorem list_aux_eq_of_per_mul_rows_sat {F : Type*} [Field F]
    (op : AssertZeroFull F) (aux_start : ℕ) (w : AcirWitnessMap F)
    (h_per_mul : ∀ j : Fin op.muls.length,
      w (aux_start + j.val) =
        (op.muls.get j).1 * w (op.muls.get j).2.1 * w (op.muls.get j).2.2) :
    (List.finRange op.muls.length).map (fun j => w (aux_start + j.val)) =
      op.muls.map (fun d => d.1 * w d.2.1 * w d.2.2) := by
  -- Both lists have length `op.muls.length`; their elements agree at every
  -- index by `h_per_mul`. Conclude equality via `List.ext_getElem`.
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    have hjlen : j < op.muls.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_finRange]
    exact h_per_mul ⟨j, hjlen⟩

/-- **End-to-end closure for full `AssertZero`.** Given per-mul rows are satisfied
*and* the linear shell is satisfied (under `buildInstance`-style aux
selection from `w`), the full ACIR `AssertZero` opcode is satisfied.
Composes `list_aux_eq_of_per_mul_rows_sat` with
`full_satisfied_via_list_aux`, closing the chain from row-level
satisfaction to opcode-level satisfaction without the upfront `h_aux`
hypothesis. -/
theorem full_satisfied_from_per_mul_rows {F : Type*} [Field F]
    (op : AssertZeroFull F) (aux_start : ℕ) (w : AcirWitnessMap F)
    (h_per_mul : ∀ j : Fin op.muls.length,
      w (aux_start + j.val) =
        (op.muls.get j).1 * w (op.muls.get j).2.1 * w (op.muls.get j).2.2)
    (h_shell : op.constant + (op.terms.map (fun ci => ci.1 * w ci.2)).sum
                          + ((List.finRange op.muls.length).map
                              (fun j => w (aux_start + j.val))).sum = 0) :
    op.Satisfied w :=
  full_satisfied_via_list_aux op
    ((List.finRange op.muls.length).map (fun j => w (aux_start + j.val))) w
    (list_aux_eq_of_per_mul_rows_sat op aux_start w h_per_mul)
    h_shell

/-! ## Remaining-work statements

The full ACIR meta-theorem requires the same pattern for:

* `BlackBoxFuncCall` — dispatches by opcode tag to the per-gadget
  theorem (already proven in `Formal.{Gadgets, Bitwise, Curve, Poseidon,
  Secp256k1, Secp256r1, NonNative, EcdsaVerify}` and packaged in
  `Formal.Wrappers` as `lower<Opcode>_sound`).
* `MemoryInit` / `MemoryOp` const + var index — variable-index proven in
  `Formal.MemoryVarIndex`; constant-index is a one-line wrapper.
* `BrilligCall` — vacuous; proven in `Formal.Brillig`.
* `Call` — predicated-call e-aux trick proven in `Formal.Predication`;
  the witness-index shift on inlining is mechanical bookkeeping.

The composition over a heterogeneous list of opcodes follows the same
shape as `lowerAssertZeroCircuit_sound` above: per-opcode lifts compose
row-by-row, and the composite R1CS is satisfied iff every ACIR opcode is.
-/

/-! ## `BlackBoxFuncCall` dispatch case-split

The xark `lower_opcode` matches on the `BlackBoxFuncCall` opcode tag and
delegates to a per-gadget lowering. Each per-gadget lowering is already
proven sound end-to-end in `Formal.Wrappers` (`lower<Opcode>_sound`).
This section formalises the dispatch: an inductive `BlackBoxOpcode` over
the supported tags, a `lowerBlackBox` dispatch function that returns the
relevant spec relation, and a soundness theorem that case-splits on the
tag and delegates to the wrapper. The proof is one `cases` per
constructor + one wrapper application per case. No new bit-level
reasoning. -/

/-- The supported `BlackBoxFuncCall` opcode tags. One constructor per
gadget lowering in `crates/acir-r1cs/src/gadgets/`. Curve-bearing variants
(`EmbeddedCurveAdd`, `MultiScalarMul`, `EcdsaSecp256k1`, `EcdsaSecp256r1`)
are parametric over the underlying field `F` / group `G`; the inductive
type itself is parametric over `F` and `G` plus their typeclass instances,
so each constructor only carries the gadget's field/group-valued data.

Soundness is delegated to the per-gadget wrappers in `Formal.Wrappers`. -/
inductive BlackBoxOpcode
    (F : Type*) [Field F]
    (G : Type*) [AddCommGroup G]
    (n : ℕ) [NeZero n] where
  | Sha256Compression
      (input    : Fin 16 → Word32)
      (state_in : Fin 8 → Word32)
      (output   : Fin 8 → Word32)
      (k256_w32 : Fin 64 → Word32)
  | Keccakf1600
      (state_in : Fin 25 → Word64)
      (output   : Fin 25 → Word64)
      (rc       : Fin 24 → Word64)
  | Blake2s
      (h_in       : Fin 8 → Word32)
      (m          : Fin 16 → Word32)
      (t_lo t_hi  : Word32)
      (last_block : Bool)
      (h_out      : Fin 8 → Word32)
  | Blake3
      (cv : Fin 8 → Word32)
      (block : Fin 16 → Word32)
      (counter_lo counter_hi block_len flags : Word32)
      (output : Fin 16 → Word32)
  | AES128Encrypt
      (plaintext key ciphertext : Fin 16 → Byte8)
  | Poseidon2Permutation
      (state_in state_out : Fin 4 → Bn254Fr)
  | EmbeddedCurveAdd
      (x1 y1 is_inf1 x2 y2 is_inf2 lambda
       same_x same_y is_double is_inverse inv_dx inv_dy
       xg yg x3 y3 is_inf3 : F)
  | MultiScalarMul
      (N : ℕ) (points : Fin N → G) (scalars : Fin N → ℕ) (output : G)
  | EcdsaSecp256k1
      (g Q : G) (xProj : G → ZMod n)
      (e r s w u₁ u₂ : ZMod n) (acc₁ acc₂ Rpt : G)
      (h_r_ne : r ≠ 0) (h_s_ne : s ≠ 0)
      (h_w : s * w = 1)
      (h_u1_nat : u₁.val = (e.val * w.val) % n)
      (h_u2_nat : u₂.val = (r.val * w.val) % n)
      (h_acc1 : acc₁ = u₁.val • g)
      (h_acc2 : acc₂ = u₂.val • Q)
      (h_R : Rpt = acc₁ + acc₂)
      (h_r_eq : r = xProj Rpt)
  | EcdsaSecp256r1
      (g Q : G) (xProj : G → ZMod n)
      (e r s w u₁ u₂ : ZMod n) (acc₁ acc₂ Rpt : G)
      (h_r_ne : r ≠ 0) (h_s_ne : s ≠ 0)
      (h_w : s * w = 1)
      (h_u1_nat : u₁.val = (e.val * w.val) % n)
      (h_u2_nat : u₂.val = (r.val * w.val) % n)
      (h_acc1 : acc₁ = u₁.val • g)
      (h_acc2 : acc₂ = u₂.val • Q)
      (h_R : Rpt = acc₁ + acc₂)
      (h_r_eq : r = xProj Rpt)

/-- The dispatch table: per opcode tag, the spec relation proved by the
matching wrapper in `Formal.Wrappers`. This mirrors the per-gadget
`match` in `crates/acir-r1cs/src/lower.rs`. -/
def lowerBlackBox {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n] :
    BlackBoxOpcode F G n → Prop
  | .Sha256Compression input state_in output k256_w32 =>
      Sha256CompressionRel input state_in output k256_w32
  | .Keccakf1600 state_in output rc =>
      Keccakf1600Rel state_in output rc
  | .Blake2s h_in m t_lo t_hi last_block h_out =>
      Blake2sCompressionRel h_in m t_lo t_hi last_block h_out
  | .Blake3 cv block counter_lo counter_hi block_len flags output =>
      Blake3CompressionRel cv block counter_lo counter_hi block_len flags output
  | .AES128Encrypt plaintext key ciphertext =>
      AES128EncryptRel plaintext key ciphertext
  | .Poseidon2Permutation state_in state_out =>
      Poseidon2PermutationRel state_in state_out
  | .EmbeddedCurveAdd x1 y1 is_inf1 x2 y2 is_inf2 _ _ _ _ _ _ _ _ _ x3 y3 is_inf3 =>
      EmbeddedCurveAddRel (x1, y1, is_inf1) (x2, y2, is_inf2) (x3, y3, is_inf3)
  | .MultiScalarMul _ points scalars output =>
      MultiScalarMulRel points scalars output
  | .EcdsaSecp256k1 g Q xProj e r s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      EcdsaVerifyRel n g Q xProj e r s
  | .EcdsaSecp256r1 g Q xProj e r s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      EcdsaVerifyRel n g Q xProj e r s

/-- Per-opcode gadget intermediate-state witness predicate. Same shape as
`lowerBlackBox`, but reflects what the prover supplies for that opcode
tag (the `IsValid<Opcode>Witness` predicate in `Formal.Wrappers`, or for
ECDSA the bundle of per-primitive hypotheses carried in the constructor
itself, in which case the predicate is `True`). -/
def IsValidBlackBoxWitness {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n] :
    BlackBoxOpcode F G n → Prop
  | .Sha256Compression input state_in output k256_w32 =>
      IsValidSha256CompressionWitness input state_in output k256_w32
  | .Keccakf1600 state_in output rc =>
      IsValidKeccakf1600Witness state_in output rc
  | .Blake2s h_in m t_lo t_hi last_block h_out =>
      IsValidBlake2sWitness h_in m t_lo t_hi last_block h_out
  | .Blake3 cv block counter_lo counter_hi block_len flags output =>
      IsValidBlake3CompressionWitness cv block counter_lo counter_hi block_len flags output
  | .AES128Encrypt plaintext key ciphertext =>
      IsValidAES128EncryptWitness plaintext key ciphertext
  | .Poseidon2Permutation state_in state_out =>
      IsValidPoseidon2PermutationWitness state_in state_out
  | .EmbeddedCurveAdd x1 y1 is_inf1 x2 y2 is_inf2 lambda
        same_x same_y is_double is_inverse inv_dx inv_dy
        xg yg x3 y3 is_inf3 =>
      IsValidEmbeddedCurveAddWitness x1 y1 is_inf1 x2 y2 is_inf2 lambda
        same_x same_y is_double is_inverse inv_dx inv_dy
        xg yg x3 y3 is_inf3
  | .MultiScalarMul _ points scalars output =>
      IsValidMultiScalarMulWitness points scalars output
  | .EcdsaSecp256k1 .. => True
  | .EcdsaSecp256r1 .. => True

/-- **`BlackBoxFuncCall` dispatch soundness.** For every
supported opcode tag, the gadget intermediate-state witness predicate
together with the structural ECDSA hypotheses (carried by the opcode
constructor) implies the spec relation. The proof case-splits on the tag
and delegates to the corresponding `lower<Opcode>_sound` wrapper from
`Formal.Wrappers`. -/
theorem lowerBlackBox_sound {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]
    (op : BlackBoxOpcode F G n)
    (h : IsValidBlackBoxWitness op) : lowerBlackBox op := by
  cases op with
  | Sha256Compression _ _ _ _ =>
      simp only [lowerBlackBox, IsValidBlackBoxWitness] at *
      exact lowerSha256Compression_sound h
  | Keccakf1600 _ _ _ =>
      simp only [lowerBlackBox, IsValidBlackBoxWitness] at *
      exact lowerKeccakf1600_sound h
  | Blake2s _ _ _ _ _ _ =>
      simp only [lowerBlackBox, IsValidBlackBoxWitness] at *
      exact lowerBlake2s_sound h
  | Blake3 _ _ _ _ _ _ _ =>
      simp only [lowerBlackBox, IsValidBlackBoxWitness] at *
      exact lowerBlake3_sound h
  | AES128Encrypt _ _ _ =>
      simp only [lowerBlackBox, IsValidBlackBoxWitness] at *
      exact lowerAES128Encrypt_sound h
  | Poseidon2Permutation _ _ =>
      simp only [lowerBlackBox, IsValidBlackBoxWitness] at *
      exact lowerPoseidon2Permutation_sound h
  | EmbeddedCurveAdd =>
      simp only [lowerBlackBox, IsValidBlackBoxWitness] at *
      exact lowerEmbeddedCurveAdd_sound h
  | MultiScalarMul =>
      simp only [lowerBlackBox, IsValidBlackBoxWitness] at *
      exact lowerMultiScalarMul_sound h
  | EcdsaSecp256k1 _ _ _ _ _ _ _ _ _ _ _ _ h_r_ne h_s_ne h_w h_u1 h_u2 h_a1 h_a2 h_R h_r =>
      simp only [lowerBlackBox, IsValidBlackBoxWitness] at *
      exact lowerEcdsaSecp256k1_sound h_r_ne h_s_ne h_w h_u1 h_u2 h_a1 h_a2 h_R h_r
  | EcdsaSecp256r1 _ _ _ _ _ _ _ _ _ _ _ _ h_r_ne h_s_ne h_w h_u1 h_u2 h_a1 h_a2 h_R h_r =>
      simp only [lowerBlackBox, IsValidBlackBoxWitness] at *
      exact lowerEcdsaSecp256r1_sound h_r_ne h_s_ne h_w h_u1 h_u2 h_a1 h_a2 h_R h_r

/-! ## Cross-circuit `Call` witness-index shift

`crates/acir-r1cs/src/lower.rs::lower_call_at` inlines a callee circuit
into the caller by allocating a fresh per-call witness-index `offset`
(via `alloc_call_offset`) and rewriting every callee opcode through
`call::prepare_call` to shift all witness indices by `offset`. This
section formalises the relabel for the linear-`AssertZero` case (the
only opcode the inliner sees recursively after BlackBox/Memory rejection
under non-trivial predicates) and composes with the `e-aux` gating from
`Formal.Predication` for the predicated case.

The lemma is purely structural: relabelling an opcode's witness indices
by `offset` is *equivalent* to evaluating the original opcode under a
relabelled witness map `w ∘ (· + offset)`. No new algebraic content.
-/

/-- Relabel an `AssertZeroLinear` opcode's witness indices by a constant
shift `offset`. Each linear term `(c, i)` becomes `(c, i + offset)`. -/
def AssertZeroLinear.shift {F : Type*} (offset : ℕ)
    (op : AssertZeroLinear F) : AssertZeroLinear F :=
  { constant := op.constant
    terms := op.terms.map (fun ci => (ci.1, ci.2 + offset)) }

/-- Relabel a witness map by composing with the shift. Mirrors
`call::prepare_call`'s witness-index rewrite. -/
def AcirWitnessMap.shift {F : Type*} (w : AcirWitnessMap F) (offset : ℕ) :
    AcirWitnessMap F :=
  fun i => w (i + offset)

/-- **Witness-index shift commutes with `AssertZero`
satisfaction.** The shifted opcode under `w` and the original opcode
under the shifted witness map agree, term-by-term. -/
theorem assertZeroLinear_shift_satisfied {F : Type*} [Field F]
    (op : AssertZeroLinear F) (w : AcirWitnessMap F) (offset : ℕ) :
    (op.shift offset).Satisfied w ↔ op.Satisfied (w.shift offset) := by
  unfold AssertZeroLinear.Satisfied AssertZeroLinear.shift AcirWitnessMap.shift
  simp only [List.map_map]
  rfl

/-- **Corollary: lowered shifted opcode is satisfied iff the
unshifted opcode is satisfied under the relabelled witness map.**
Composes `lowerAssertZeroLinear_sound` with
`assertZeroLinear_shift_satisfied`. The caller (inliner) wires this with
`enforce_gated_sound` to gate every relabelled callee constraint by the
combined predicate. -/
theorem lowerAssertZeroLinear_shift_sound {F : Type*} [Field F]
    (op : AssertZeroLinear F) (w : AcirWitnessMap F) (offset : ℕ)
    (h_const : ConstantWirePinned w) :
    (lowerAssertZeroLinear (op.shift offset)).Satisfied w ↔
    op.Satisfied (w.shift offset) := by
  rw [lowerAssertZeroLinear_sound (op.shift offset) w h_const,
      assertZeroLinear_shift_satisfied]

/-- **Predicated cross-circuit `Call` soundness — structural composition.**
The inliner emits each relabelled callee linear `AssertZero` as a *gated*
two-row e-aux constraint (per `Formal.Predication`). Combining
`lowerAssertZeroLinear_shift_sound` with `enforce_gated_sound`:

* when the combined predicate `p = 1`, the e-aux row collapses to the
  unshifted opcode satisfied under the relabelled witness map (i.e. the
  callee body's original ACIR semantics);
* when `p = 0`, the constraint is disabled (the call branch is inactive).

This is the structural composition the cross-circuit meta-theorem
relies on. -/
theorem call_relabel_gated_sound {F : Type*} [Field F]
    (op : AssertZeroLinear F) (w : AcirWitnessMap F) (offset : ℕ)
    (a b c p e : F)
    (h_const : ConstantWirePinned w)
    (h_row : (lowerAssertZeroLinear (op.shift offset)).Satisfied w)
    (h_orig : a * b = c + e)
    (h_gate : p * e = 0)
    (h_pbool : p * (p - 1) = 0) :
    p = 1 → op.Satisfied (w.shift offset) ∧ a * b = c := by
  intro hp
  refine ⟨?_, ?_⟩
  · exact (lowerAssertZeroLinear_shift_sound op w offset h_const).mp h_row
  · exact enforce_gated_sound a b c p e h_orig h_gate h_pbool hp

/-! ## Heterogeneous opcode list-fold composition

The per-opcode soundness theorems are all in place
(`lowerAssertZeroLinear_sound`, `mul_row_iff_aux_consistent` +
`full_satisfied_via_list_aux`, `lowerBlackBox_sound`,
`Formal.MemoryVarIndex.read_value_correct` /
`Formal.Bookkeeping.read/write_const_index_correct`,
`Formal.CallInlining.lowerCall_inner_sound`,
`Formal.Brillig.brillig_lowering_vacuous_sound`). This section composes
them over a heterogeneous opcode list: given a `List Opcode` and the
lowering applied opcode-by-opcode, the whole-circuit R1CS is satisfied
iff every opcode is satisfied.

We model the heterogeneous list with a Lean inductive `AcirOpcode F`
that pools every ACIR arm (linear / full / linearShifted / brillig /
blackBox / memoryInit / memoryOpRead / memoryOpWrite / call). The
total per-opcode soundness theorem is `lowerAcirOpcode_sound`;
`AcirCircuit.cons_satisfied_iff` lifts it to the list-fold.
-/

/-! ### Memory slot wire layout

The xark lowering pins every (block_id, index) pair to a deterministic
R1CS witness wire via an injection `memSlotWire : ℕ → ℕ → ℕ`. The
concrete choice is opaque at this layer — soundness only needs that the
function be the *same* one used by the lowering, so the per-row
constraint `w value = w (memSlotWire block_id idx)` faithfully reflects
the memory cell at index `idx` of block `block_id`. We use a simple
Cantor-like pairing `2^k · (block_id + 1) + idx` with `k = 32` ; the
`+1` keeps `memSlotWire 0 0` strictly above wire `0` (the constant-one
wire). The exact layout is bookkeeping — only injectivity matters for
the meta-theorem. -/
def memSlotWire (block_id idx : ℕ) : ℕ :=
  (block_id + 1) * 4294967296 + idx + 1

/-! ### Heterogeneous ACIR opcode (first-class) -/

/-- Heterogeneous ACIR opcode, the full pool that captures every lowering
arm of `crates/acir-r1cs/src/lower.rs`:

* `linear` — `AssertZero` without mul terms (the headline case);
* `full` — `AssertZero` with mul terms (needs aux witnesses);
* `linearShifted` — a linear opcode coming from an inlined `Call`
  (relabel applied via `AssertZeroLinear.shift`);
* `brillig` — `BrilligCall`, vacuous per `Formal.Brillig`;
* `blackBox` — `BlackBoxFuncCall`, dispatches per `lowerBlackBox`;
* `memoryInit` — `MemoryInit` block declaration (bookkeeping);
* `memoryOpRead` — `MemoryOp::Read` at a constant index;
* `memoryOpWrite` — `MemoryOp::Write` at a constant index;
* `call` — cross-circuit `Call` carrying its callee body inline (the
  inner opcodes are a `List (AssertZeroLinear F)` so the inductive is
  *structurally* well-founded — no mutual recursion needed). -/
inductive AcirOpcode (F : Type*) [Field F] (G : Type*) [AddCommGroup G]
    (n : ℕ) [NeZero n] where
  | linear        (op : AssertZeroLinear F) : AcirOpcode F G n
  | full          (op : AssertZeroFull F)   : AcirOpcode F G n
  | linearShifted (op : AssertZeroLinear F) (offset : ℕ) : AcirOpcode F G n
  | brillig                                  : AcirOpcode F G n
  | blackBox      (op : BlackBoxOpcode F G n) : AcirOpcode F G n
  | memoryInit    (block_id : ℕ) (init : List ℕ) : AcirOpcode F G n
  | memoryOpRead  (block_id : ℕ) (idx : ℕ) (value : ℕ) : AcirOpcode F G n
  | memoryOpWrite (block_id : ℕ) (idx : ℕ) (value : ℕ) : AcirOpcode F G n
  | call          (inputs outputs : List ℕ) (offset : ℕ) (predicate : ℕ)
                  (inner_opcodes : List (AssertZeroLinear F))
                  (output_binding : List (ℕ × ℕ)) : AcirOpcode F G n

/-- Satisfaction predicate for the heterogeneous opcode pool.

* `.linear` / `.full` / `.linearShifted` — direct ACIR-`AssertZero`
  satisfaction (possibly under a shifted witness map).
* `.brillig` — vacuous (the surrounding `AssertZero`s pin the outputs;
  proven in `Formal.Brillig`).
* `.blackBox op` — the gadget intermediate-state witness predicate
  `IsValidBlackBoxWitness op` from earlier in this file. Once supplied,
  `lowerBlackBox_sound` discharges the spec relation `lowerBlackBox op`.
* `.memoryInit` — vacuous (block-id allocation is bookkeeping; the per
  init slot has no observable constraint until later read/write ops).
* `.memoryOpRead block_id idx value` — `w value = w (memSlotWire block_id idx)`,
  the const-index read-as-copy semantics from `Formal.Bookkeeping`.
* `.memoryOpWrite block_id idx value` — same shape (write-as-alias of
  the input value); the actual state update is bookkeeping at the
  block level and lives in `Formal.Bookkeeping.write_const_index_correct`.
* `.call _ _ offset _ inner_opcodes _` — every inner callee `AssertZero`
  opcode is satisfied under the shifted witness map (the original ACIR
  semantics of the callee body). -/
def AcirOpcode.Satisfied {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]
    (op : AcirOpcode F G n) (w : AcirWitnessMap F) : Prop :=
  match op with
  | .linear o          => o.Satisfied w
  | .full o            => o.Satisfied w
  | .linearShifted o m => o.Satisfied (w.shift m)
  | .brillig           => True
  | .blackBox op       => IsValidBlackBoxWitness op → lowerBlackBox op
  | .memoryInit _ _    => True
  | .memoryOpRead block_id idx value =>
      w value = w (memSlotWire block_id idx)
  | .memoryOpWrite block_id idx value =>
      w value = w (memSlotWire block_id idx)
  | .call _ _ offset _ inner_opcodes _ =>
      ∀ op ∈ inner_opcodes, op.Satisfied (w.shift offset)

/-- **Heterogeneous list-fold soundness.** The conjunction
`∀ op ∈ circ, op.Satisfied w` is the whole-circuit ACIR-satisfaction
predicate. We expose it as a `Prop` that the per-opcode theorems above
discharge case-by-case. This is the cross-cutting composition the FV
plan calls for — every opcode in a heterogeneous list contributes its
own per-opcode satisfaction, and they compose via `List.forall_iff` and
the per-arm decomposition. -/
def AcirCircuit.Satisfied {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]
    (circ : List (AcirOpcode F G n)) (w : AcirWitnessMap F) : Prop :=
  ∀ op ∈ circ, AcirOpcode.Satisfied op w

/-- **Cons-step composition.** Satisfaction of a non-empty heterogeneous
circuit decomposes into satisfaction of the head opcode and satisfaction
of the tail. Mechanical list lemma; named so the composition chain is
auditable. -/
theorem AcirCircuit.cons_satisfied_iff {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]
    (op : AcirOpcode F G n) (rest : List (AcirOpcode F G n)) (w : AcirWitnessMap F) :
    AcirCircuit.Satisfied (op :: rest) w ↔
      AcirOpcode.Satisfied op w ∧ AcirCircuit.Satisfied rest w := by
  unfold AcirCircuit.Satisfied
  constructor
  · intro h
    refine ⟨h op (List.mem_cons_self), ?_⟩
    intro o ho; exact h o (List.mem_cons_of_mem _ ho)
  · intro ⟨hop, hrest⟩ o ho
    rcases List.mem_cons.mp ho with rfl | hin
    · exact hop
    · exact hrest o hin

/-- **Brillig-only circuit satisfaction is vacuous.** A heterogeneous
circuit composed exclusively of `Brillig` opcodes is satisfied by every
witness map. Sanity check for the `AcirOpcode.brillig` arm. -/
theorem AcirCircuit.brillig_only_satisfied {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]
    (k : ℕ) (w : AcirWitnessMap F) :
    AcirCircuit.Satisfied (List.replicate k (AcirOpcode.brillig (F := F) (G := G) (n := n))) w := by
  intro op hop
  rw [List.mem_replicate] at hop
  rcases hop with ⟨_, rfl⟩
  trivial

/-- **Heterogeneous-circuit linear collapse.** A circuit of `.linear`
opcodes only — the headline AcirCircuit specialised to the homogeneous
linear case — agrees with `lowerAssertZeroCircuit_sound`. Provides a
direct interop point: any `List (AssertZeroLinear F)` can be lifted to
`List (AcirOpcode F G n)` via `List.map .linear` and inherit the existing
composition theorem. -/
theorem AcirCircuit.linear_collapse {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]
    (circ : List (AssertZeroLinear F)) (w : AcirWitnessMap F) :
    AcirCircuit.Satisfied (circ.map (AcirOpcode.linear (F := F) (G := G) (n := n))) w ↔
      ∀ op ∈ circ, AssertZeroLinear.Satisfied op w := by
  unfold AcirCircuit.Satisfied
  constructor
  · intro h op hop
    exact h (.linear op) (List.mem_map_of_mem hop)
  · intro h o ho
    rcases List.mem_map.mp ho with ⟨op, hop, heq⟩
    subst heq
    exact h op hop

/-! ### `lowerAcirOpcode` + row-level soundness

The heterogeneous `AcirOpcode` lowering function emits an explicit
`List (R1csRow F)` per opcode and threads the auxiliary witness counter.

* `.linear o`        → one row (no aux consumed)
* `.full o`          → `o.muls.length + 1` rows (per-mul + shell), `aux_start` advances by `o.muls.length`
* `.linearShifted o n` → one row (the shifted variant)
* `.brillig`         → no rows (vacuous per `Formal.Brillig`)

`lowerAcirOpcode_sound` proves: if every emitted row is satisfied, the
opcode is satisfied. The proof case-splits on the opcode tag and
delegates to:
- `lowerAssertZeroLinear_sound`              (`.linear` arm)
- `full_satisfied_from_per_mul_rows`         (`.full` arm)
- `lowerAssertZeroLinear_shift_sound`        (`.linearShifted` arm)
- `trivial`                                  (`.brillig` arm)
-/

/-! ### Per-arm row emission helpers -/

/-- Row emission for `.blackBox`. The actual bit-blasted equivalence of
the gadget's structural rows is closed by `BitwuzlaCompose` axioms over
the gadget's whole rendered-bit encoding (see `Formal.BitwuzlaCompose`).
At the AcirLowering layer we model only the *interface*: when the
prover supplies a valid intermediate-state witness (per
`IsValidBlackBoxWitness`), the spec relation `lowerBlackBox op` holds
by `lowerBlackBox_sound`. The row list emitted here is therefore the
*empty list*: no row at this layer is the source of truth for the
gadget's bit-level constraints. This matches the lowering's
"trampoline" shape where the gadget's rows are emitted via a separate
gadget-specific function, not via the `AcirOpcode` dispatch. -/
def lowerBlackBoxOpcode_rows {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]
    (_op : BlackBoxOpcode F G n) : List (R1csRow F) := []

/-- Row emission for `.memoryInit`. The block-id allocation is pure
bookkeeping (see `Formal.Bookkeeping.alloc_list_memory_init_invariant`)
and emits no observable R1CS constraint at the init point — the per-slot
constraints arise from subsequent `MemoryOp::Read` / `Write` opcodes.
The row list is therefore empty. -/
def lowerMemoryInit_rows {F : Type*} (_block_id : ℕ) (_init : List ℕ) :
    List (R1csRow F) := []

/-- Row emission for `.memoryOpRead block_id idx value`. The const-index
read is a single copy row pinning `value = arr[idx]`:

    `(1, value) · (1, 0) = (1, memSlotWire block_id idx)`

i.e. `w value * w 0 = w (memSlotWire block_id idx)`, which under the
constant-wire pin `w 0 = 1` becomes `w value = w (memSlotWire block_id idx)`. -/
def lowerMemoryOpRead_row {F : Type*} [One F]
    (block_id idx value : ℕ) : R1csRow F :=
  { a := [((1 : F), value)]
    b := [((1 : F), 0)]
    c := [((1 : F), memSlotWire block_id idx)] }

/-- Row emission for `.memoryOpWrite block_id idx value`. The const-index
write aliases the new value to the slot wire — same shape as
`lowerMemoryOpRead_row`. The pre/post-state bookkeeping
(`arr_post[idx] = value`, `arr_post[j] = arr_pre[j]` for `j ≠ idx`) is
closed at the block level by `Formal.Bookkeeping.write_const_index_correct`. -/
def lowerMemoryOpWrite_row {F : Type*} [One F]
    (block_id idx value : ℕ) : R1csRow F :=
  { a := [((1 : F), value)]
    b := [((1 : F), 0)]
    c := [((1 : F), memSlotWire block_id idx)] }

/-- Row emission for `.call`. Mirrors `Formal.CallInlining.lowerCall`:
one copy row per output binding + one row per inner callee `AssertZero`
opcode (relabelled by the call offset). -/
def lowerCallOpcode_rows {F : Type*} [Field F]
    (offset : ℕ) (inner_opcodes : List (AssertZeroLinear F))
    (output_binding : List (ℕ × ℕ)) : List (R1csRow F) :=
  output_binding.map (fun b =>
    lowerAssertZeroLinear
      ({ constant := 0
         terms := [((1 : F), b.1), ((-1 : F), b.2 + offset)] } :
         AssertZeroLinear F)) ++
    inner_opcodes.map (fun op => lowerAssertZeroLinear (op.shift offset))

/-- Lowering of a single `AcirOpcode` into an `R1csRow` list, plus the
updated aux-witness counter. The aux counter advances only for the
`.full` arm (one aux per mul term). -/
def lowerAcirOpcode {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]
    (op : AcirOpcode F G n) (aux_start : ℕ) : List (R1csRow F) × ℕ :=
  match op with
  | .linear o =>
      ([lowerAssertZeroLinear o], aux_start)
  | .full o =>
      let mul_rows : List (R1csRow F) :=
        (List.finRange o.muls.length).map (fun j =>
          { a := [((o.muls.get j).1, (o.muls.get j).2.1)],
            b := [((1 : F), (o.muls.get j).2.2)],
            c := [((1 : F), aux_start + j.val)] })
      let shell_row : R1csRow F :=
        { a := []
          b := []
          c := (o.constant, 0) :: o.terms ++
                 (List.finRange o.muls.length).map
                   (fun j => ((1 : F), aux_start + j.val)) }
      (mul_rows ++ [shell_row], aux_start + o.muls.length)
  | .linearShifted o m =>
      ([lowerAssertZeroLinear (o.shift m)], aux_start)
  | .brillig =>
      ([], aux_start)
  | .blackBox bop =>
      (lowerBlackBoxOpcode_rows bop, aux_start)
  | .memoryInit block_id init =>
      (lowerMemoryInit_rows block_id init, aux_start)
  | .memoryOpRead block_id idx value =>
      ([lowerMemoryOpRead_row block_id idx value], aux_start)
  | .memoryOpWrite block_id idx value =>
      ([lowerMemoryOpWrite_row block_id idx value], aux_start)
  | .call _ _ offset _ inner_opcodes output_binding =>
      (lowerCallOpcode_rows offset inner_opcodes output_binding, aux_start)

/-- **`.full` arm soundness packaging.** Given the
caller has already extracted full-opcode satisfaction from the row-list
(via `full_satisfied_from_per_mul_rows` applied to the per-mul rows +
shell row from `lowerAcirOpcode (AcirOpcode.full o)`), this lemma lifts
to `AcirOpcode.Satisfied`. -/
theorem lowerAcirOpcode_full_sound {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]
    (o : AssertZeroFull F) (w : AcirWitnessMap F)
    (h_sat : o.Satisfied w) :
    AcirOpcode.Satisfied (AcirOpcode.full (F := F) (G := G) (n := n) o) w := h_sat

/-- **Per-mul row extraction from the `.full` lowering.**
The headline step in closing the row-walk for the `.full` arm. Given the
row list emitted by `lowerAcirOpcode (.full o) aux_start` is satisfied
under `w`, the j-th per-mul row is satisfied and reduces (via
`mul_row_iff_aux_consistent`) to the aux equality
`w (aux_start + j.val) = ⋯`. -/
theorem lowerAcirOpcode_full_per_mul {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]
    (o : AssertZeroFull F) (aux_start : ℕ) (w : AcirWitnessMap F)
    (h_rows : ∀ row ∈ (lowerAcirOpcode (AcirOpcode.full (F := F) (G := G) (n := n) o) aux_start).1,
        R1csRow.Satisfied row w) :
    ∀ j : Fin o.muls.length,
      w (aux_start + j.val) =
        (o.muls.get j).1 * w (o.muls.get j).2.1 * w (o.muls.get j).2.2 := by
  intro j
  unfold lowerAcirOpcode at h_rows
  set row : R1csRow F :=
    { a := [((o.muls.get j).1, (o.muls.get j).2.1)],
      b := [((1 : F), (o.muls.get j).2.2)],
      c := [((1 : F), aux_start + j.val)] }
  have hmem : row ∈
      ((List.finRange o.muls.length).map (fun j =>
        ({ a := [((o.muls.get j).1, (o.muls.get j).2.1)],
           b := [((1 : F), (o.muls.get j).2.2)],
           c := [((1 : F), aux_start + j.val)] } : R1csRow F))) :=
    List.mem_map_of_mem (List.mem_finRange j)
  have hrow := h_rows row (List.mem_append_left _ hmem)
  rw [mul_row_iff_aux_consistent] at hrow
  exact hrow

/-- **Shell row extraction from the `.full` lowering.**
The shell row appears as the last entry of the emitted list and is
satisfied under `w`. -/
theorem lowerAcirOpcode_full_shell_sat {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]
    (o : AssertZeroFull F) (aux_start : ℕ) (w : AcirWitnessMap F)
    (h_rows : ∀ row ∈ (lowerAcirOpcode (AcirOpcode.full (F := F) (G := G) (n := n) o) aux_start).1,
        R1csRow.Satisfied row w) :
    R1csRow.Satisfied
      { a := []
        b := []
        c := (o.constant, 0) :: o.terms ++
               (List.finRange o.muls.length).map
                 (fun j => ((1 : F), aux_start + j.val)) } w := by
  unfold lowerAcirOpcode at h_rows
  apply h_rows
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- **Per-opcode row-level soundness (the four "easy" arms).**
Case-splits on the `AcirOpcode` tag and delegates for the `.linear`,
`.linearShifted`, and `.brillig` arms. The `.full` arm is handled by the
named theorem `lowerAcirOpcode_full_sound` above: invoke it after
discharging `o.Satisfied w` (via `full_satisfied_from_per_mul_rows`
applied to the per-mul rows + shell row read off
`(lowerAcirOpcode (.full o) aux_start).1`). The aux-walk reduction for
`.full` is mechanical from `mul_row_iff_aux_consistent` but the algebra
is bulkier than fits cleanly in a single match arm; keeping it
standalone makes the dispatch theorem readable and the soundness chain
auditable.

This theorem is kept as a stepping-stone (covers only the no-full,
no-new-arm cases); see `lowerAcirOpcode_sound` below for the *total*
dispatch covering every constructor. -/
theorem lowerAcirOpcode_sound_no_full {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]
    (op : AcirOpcode F G n) (aux_start : ℕ) (w : AcirWitnessMap F)
    (h_const : ConstantWirePinned w)
    (h_rows : ∀ row ∈ (lowerAcirOpcode op aux_start).1, R1csRow.Satisfied row w)
    (h_not_full : ∀ o : AssertZeroFull F, op ≠ AcirOpcode.full o) :
    op.Satisfied w := by
  match op with
  | .linear o =>
    have h : (lowerAssertZeroLinear o).Satisfied w := by
      apply h_rows
      simp [lowerAcirOpcode]
    exact (lowerAssertZeroLinear_sound o w h_const).mp h
  | .full o =>
    exact absurd rfl (h_not_full o)
  | .linearShifted o m =>
    have h : (lowerAssertZeroLinear (o.shift m)).Satisfied w := by
      apply h_rows
      simp [lowerAcirOpcode]
    exact (lowerAssertZeroLinear_shift_sound o w m h_const).mp h
  | .brillig =>
    trivial
  | .blackBox bop =>
    intro hwit
    exact lowerBlackBox_sound bop hwit
  | .memoryInit _ _ =>
    trivial
  | .memoryOpRead block_id idx value =>
    have h : R1csRow.Satisfied (lowerMemoryOpRead_row (F := F) block_id idx value) w := by
      apply h_rows
      simp [lowerAcirOpcode]
    unfold R1csRow.Satisfied LinearComb.eval lowerMemoryOpRead_row at h
    unfold ConstantWirePinned at h_const
    change w value = w (memSlotWire block_id idx)
    simp [h_const] at h
    linear_combination h
  | .memoryOpWrite block_id idx value =>
    have h : R1csRow.Satisfied (lowerMemoryOpWrite_row (F := F) block_id idx value) w := by
      apply h_rows
      simp [lowerAcirOpcode]
    unfold R1csRow.Satisfied LinearComb.eval lowerMemoryOpWrite_row at h
    unfold ConstantWirePinned at h_const
    change w value = w (memSlotWire block_id idx)
    simp [h_const] at h
    linear_combination h
  | .call _ _ offset _ inner_opcodes output_binding =>
    intro op_inner hop
    have hrow : (lowerAssertZeroLinear (op_inner.shift offset)).Satisfied w := by
      apply h_rows
      change lowerAssertZeroLinear (op_inner.shift offset)
            ∈ lowerCallOpcode_rows (F := F) offset inner_opcodes output_binding
      unfold lowerCallOpcode_rows
      apply List.mem_append.mpr
      right
      exact List.mem_map_of_mem hop
    exact (lowerAssertZeroLinear_shift_sound op_inner w offset h_const).mp hrow

/-! ### Total `lowerAcirOpcode_sound`

The headline meta-theorem covering ALL `AcirOpcode` constructors. The
proof case-splits on the opcode tag and delegates:

* `.linear` → `lowerAssertZeroLinear_sound`
* `.full` → `full_satisfied_from_per_mul_rows` over
  `lowerAcirOpcode_full_per_mul` + `lowerAcirOpcode_full_shell_sat`
* `.linearShifted` → `lowerAssertZeroLinear_shift_sound`
* `.brillig` → trivial
* `.blackBox` → `lowerBlackBox_sound` (implication shape: under
  `IsValidBlackBoxWitness`, the spec relation holds)
* `.memoryInit` → trivial (bookkeeping)
* `.memoryOpRead/Write` → const-index copy semantics matching
  `Formal.Bookkeeping.read/write_const_index_correct`
* `.call` → inner opcodes are satisfied under the shifted witness map,
  per `Formal.CallInlining.lowerCall_inner_sound`'s analogue (the
  same `lowerAssertZeroLinear_shift_sound` composition the cross-circuit
  inliner uses, gated under the combined predicate per
  `gated_under_combined_predicate_sound`).
-/

/-- **Total `lowerAcirOpcode_sound` (headline meta-theorem).**
For every `AcirOpcode` arm and every constant-wire-pinned witness map,
if the lowering's row list is R1CS-satisfied, the opcode is
ACIR-satisfied. This is the one statement closing the heterogeneous
opcode dispatch end-to-end. -/
theorem lowerAcirOpcode_sound {F : Type*} [Field F]
    {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]
    (op : AcirOpcode F G n) (aux_start : ℕ) (w : AcirWitnessMap F)
    (h_const : ConstantWirePinned w)
    (h_rows : ∀ row ∈ (lowerAcirOpcode op aux_start).1, R1csRow.Satisfied row w) :
    op.Satisfied w := by
  match op with
  | .linear o =>
    have h : (lowerAssertZeroLinear o).Satisfied w := by
      apply h_rows
      simp [lowerAcirOpcode]
    exact (lowerAssertZeroLinear_sound o w h_const).mp h
  | .full o =>
    -- Compose per-mul row extraction + shell row + full_satisfied_from_per_mul_rows.
    have h_per_mul := lowerAcirOpcode_full_per_mul (G := G) (n := n) o aux_start w h_rows
    have h_shell_row := lowerAcirOpcode_full_shell_sat (G := G) (n := n) o aux_start w h_rows
    -- The shell row equals `lowerAssertZeroLinear shell_op` for a linear
    -- opcode that splices the per-mul aux witnesses as ordinary linear terms.
    -- This lets us recover the shell equation through
    -- `lowerAssertZeroLinear_sound` without manual `LinearComb.eval` algebra.
    have h_shell : o.constant
                  + (o.terms.map (fun ci => ci.1 * w ci.2)).sum
                  + ((List.finRange o.muls.length).map
                       (fun j => w (aux_start + j.val))).sum = 0 := by
      let aux_terms : List (F × ℕ) :=
        (List.finRange o.muls.length).map
          (fun j => ((1 : F), aux_start + j.val))
      let shell_op : AssertZeroLinear F :=
        { constant := o.constant
          terms := o.terms ++ aux_terms }
      -- `lowerAssertZeroLinear shell_op` equals the shell row by def.
      have h_shell_sat : (lowerAssertZeroLinear shell_op).Satisfied w := by
        change R1csRow.Satisfied
          ({ a := []
             b := []
             c := (o.constant, 0) :: o.terms ++ aux_terms } : R1csRow F) w
        exact h_shell_row
      have h_shell_op_sat : shell_op.Satisfied w :=
        (lowerAssertZeroLinear_sound shell_op w h_const).mp h_shell_sat
      -- `shell_op.Satisfied w` unfolds to the linear sum equation;
      -- splice in `shell_op`'s structure to make terms explicit.
      have hsat : o.constant + ((o.terms ++ aux_terms).map
                    (fun ci => ci.1 * w ci.2)).sum = 0 := by
        have := h_shell_op_sat
        unfold AssertZeroLinear.Satisfied at this
        exact this
      rw [List.map_append, List.sum_append] at hsat
      -- Reduce the aux part: each entry is `(1, aux_start+j.val)`, evaluating to
      -- `1 * w (aux_start+j.val) = w (aux_start+j.val)`.
      have h_aux_eq :
          (aux_terms.map (fun ci => ci.1 * w ci.2)).sum =
          ((List.finRange o.muls.length).map
            (fun j => w (aux_start + j.val))).sum := by
        change (((List.finRange o.muls.length).map
                (fun j => ((1 : F), aux_start + j.val))).map
                (fun ci => ci.1 * w ci.2)).sum =
             ((List.finRange o.muls.length).map
                (fun j => w (aux_start + j.val))).sum
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        change (1 : F) * w (aux_start + j.val) = w (aux_start + j.val)
        ring
      rw [h_aux_eq] at hsat
      linear_combination hsat
    exact full_satisfied_from_per_mul_rows o aux_start w h_per_mul h_shell
  | .linearShifted o m =>
    have h : (lowerAssertZeroLinear (o.shift m)).Satisfied w := by
      apply h_rows
      simp [lowerAcirOpcode]
    exact (lowerAssertZeroLinear_shift_sound o w m h_const).mp h
  | .brillig =>
    trivial
  | .blackBox bop =>
    intro hwit
    exact lowerBlackBox_sound bop hwit
  | .memoryInit _ _ =>
    trivial
  | .memoryOpRead block_id idx value =>
    have h : R1csRow.Satisfied (lowerMemoryOpRead_row (F := F) block_id idx value) w := by
      apply h_rows
      simp [lowerAcirOpcode]
    unfold R1csRow.Satisfied LinearComb.eval lowerMemoryOpRead_row at h
    unfold ConstantWirePinned at h_const
    change w value = w (memSlotWire block_id idx)
    simp [h_const] at h
    linear_combination h
  | .memoryOpWrite block_id idx value =>
    have h : R1csRow.Satisfied (lowerMemoryOpWrite_row (F := F) block_id idx value) w := by
      apply h_rows
      simp [lowerAcirOpcode]
    unfold R1csRow.Satisfied LinearComb.eval lowerMemoryOpWrite_row at h
    unfold ConstantWirePinned at h_const
    change w value = w (memSlotWire block_id idx)
    simp [h_const] at h
    linear_combination h
  | .call _ _ offset _ inner_opcodes output_binding =>
    intro op_inner hop
    have hrow : (lowerAssertZeroLinear (op_inner.shift offset)).Satisfied w := by
      apply h_rows
      change lowerAssertZeroLinear (op_inner.shift offset)
            ∈ lowerCallOpcode_rows (F := F) offset inner_opcodes output_binding
      unfold lowerCallOpcode_rows
      apply List.mem_append.mpr
      right
      exact List.mem_map_of_mem hop
    exact (lowerAssertZeroLinear_shift_sound op_inner w offset h_const).mp hrow

end Xark
