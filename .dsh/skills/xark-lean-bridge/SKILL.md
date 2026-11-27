---
name: xark-lean-bridge
description: Build and audit the xark Lean bridge for R1CS gadgets, especially the xark-rsa 25×82 chain and the lean-export/Template/coverage workflow. Use when adding or changing a gadget, exporting rows with lean-export, proving/covering a bridge, or comparing with zkGolf/Clean.
---

# xark Lean bridge

## Goal

Machine-check the generic `xark-rsa` RSA-2048 chain at 25×82:
`grouped_columns`, `square_lazy`, `fused_final`, `convert_wide`,
`bytes_to_wide`, `minus_one`, `n_top`/EM, and `verify_wide`.

Keep the gadget generic: no pinned key. The existing
`RequireLt25x82`, `RangeCheckLimbs17x121`, and `ToBits` bridges stay.

## Status (2026-11)

Proven and exported (`lean-export --check` is green on 71 templates):

| piece | template | proof |
|---|---|---|
| `range_check_q`, `range_check_r` | `Templates/RangeCheck{Q,R}.lean` (394 KB each) | `Formal/RangeCheck{Q,R}.lean` over the generic model `Formal/RangeDerived.lean` |
| `grouped_column_step` | `Templates/GroupedColumnStep.lean` | `Formal/GroupedColumnStep.lean` (89 rows, `Spec` = output `< 2^89`) |
| carry telescope | — (row-independent integer model) | `Formal/GroupedColumns.lean`, `Xark.Rsa.GroupedColumns.soundness` |
| product identity | — (model) | `GroupedColumns.{val_mul, mul_eq}`: `a·b = q·m + r` over ℤ; `square_lazy`/`fused_final` are its cases |
| field→integer carry | the step's output LC | `GroupedCarry.{outputs_eq, Q_mul_vLC, carry_row}` — the no-wrap step |
| chain top level | — (model) | `RsaChain.{n_bits, squarings, chain}`: 2048-bit modulus, `em ≡ sig^65537` |
| re-limbing | — (model) | `RsaConvert.{cols_sum, partial_sum, telescoping}`: 17×121 → 25×82 proves one number |
| byte packing | — (model) | `RsaBytes.{packing, bytes_of_bits, bytes_to_wide}`: octets and limbs denote one number |
| `grouped_columns` (general) | `Templates/GroupedColumns.lean` (704 KB, 3,435 rows) | `Formal/GroupedColumnsGadget.lean`: `modelRows`, `rows_eq`, `soundness` (`Assumptions → val a·val b = val q·val m + val rhs`) |
| `grouped_columns_square` (CSE'd) | `Templates/GroupedColumnsSquare.lean` (639 KB, 3,135 rows, 100 plugs) | `Formal/GroupedColumnsSquareGadget.lean`: same, with `a` on both sides |
| term normalization | — | `Formal/Norm.lean`: `normTerms`/`eval_norm` (sort by `varLe`, merge, drop zeros; structural so `decide +kernel` works) |
| `Consts` obligation for LC plugs | `Templates/Consts/GroupedColumnStep.lean`, `GroupedColumns.lean`, `GroupedColumnsSquare.lean` (`soundness_free`) | needed because the chain gadgets call the step with LC plugs |

Coverage on `examples/rsa2048`: 17/17 chain calls (16
`grouped_columns_square`, 1 `grouped_columns`), 17/17 `range_check_q`, 16/16
`range_check_r` calls, no allowlist entries. The 408 `grouped_column_step` calls are
children of the chain gadgets and are no longer top-level segments. Digests
pinned (`rsa2048 68ef4df3… 98b4c751…` under the keyed rustc; run
`rustup toolchain install 1.99.1` then `rustup run 1.99.1 cargo xtask digests
--check` — the workspace rustc also passes, with a different *keyed* digest).

The chain gadgets' row-level models and contracts are now proved; what remains
is the composition (17 `sat_call`s plus the chain/EM lemmas). Still hand-proved
(the remaining gap, in order):

1. The composition: 17 `sat_call` applications (`GroupedColumns.soundness` and
   `GroupedColumnsSquare.soundness` with the limb bounds from the q/r `Spec`s),
   then `RsaChain.chain` and `RsaEm.em` to the top-level statement.
2. `square_lazy`: `hint_mulmod_divmod` (the `divRem` hint's integer `a² = q·m + r`
   and its per-limb semantics), q/r ranges (done), the columns (done).
3. `fused_final` (q range + 25 EM pins + columns with `rhs_extra = em`),
   `convert_wide` (17×121→25×82, 118-bit carries, `range_derived_top::<80>`),
   `bytes_to_wide` (`to_bits::<8>` big-endian packing, `n_top`), `minus_one`
   (`m[i] − borrow + next·2^82`, the `RequireLt25x82` LC plugs),
   `sha256_em_bits_82` (constant, `EM82_CONST`), `verify_wide` (`n` exactly 2048
   bits, `sig < n`, 16 squarings + terminal multiply, the EM comparison).

## The instantiation shortcut: make the chain a gadget (finding, round 43)

Composing the circuit call-by-call is blocked on variable identity (below), and the bounds
would have to be traced through the packing. Both disappear if `grouped_columns` itself is
a `#[gadget]`:

* markers do not change rows (the digests stayed identical when the step/q/r were marked),
  so this costs no circuit change and no re-key;
* its template is one 24-step chain: **measured 704 KB, 3,435 rows** = 1,250 product rows
  (`a[i]·b[k]` and `q[i]·m[k]` interleaved by the CSE order) + 24 inlined step instances
  (91 rows each, the step's rows flat) + 1 top row — well inside what `decide +kernel`
  handles (`RangeCheckQ` is 394 KB / 4,073 rows). The tooling enforces the invariant:
  `lean-export --example` refuses to run unless `Formal.Templates.GroupedColumns` is
  imported by exactly one proof under `formal/Formal/`, so the marker cannot land
  without the proof;
* the limb bounds: `Assumptions` (`∀ i, ins i < 2^82` on the 125 plugs) come from the
  q/r `Spec`s at the call site;
* its `Assumptions` are the limb bounds (`∀ i, ins i < 2^82`, plus the rhs limbs' bits) and
  its `Spec` is `val a · val b = val q · val m + val r` — the `GroupedColumns` model, proven
  once, transferred by `rows_eq`;
* the export then has **17 top-level calls** instead of 408 step calls plus 1,250 glue rows
  each, so the circuit composition is 17 `sat_call` applications plus the plug-obligation
  (each plug is a limb, whose bound is the q/r `Spec` — already theorems);
* `bytes_to_wide`/`convert_wide` get the same treatment (bytes < 256 → limbs < 2^82 and the
  packing identity), which supplies the remaining bounds.

The nested step/q/r calls become children (`coverage::Call.parent`) and vanish from the
top-level export. Proof work: one `rows_eq` + `soundness` per new gadget, the models being
`GroupedColumns`, `RsaBytes`, `RsaConvert` (all already proven, but over values rather than
LC sums — the `Row`-level version of `GroupedColumns` is the real work).

## What the rsa2048 instantiation needed without that (finding, round 42)

The composition's mathematics is complete: step contract (`carry_of_sat_shadow`), the
integer shadow (`Shadow.lean`: `shadow_toF`, `shadow_eq_of_eval`, `val_of_mul`,
`shadow_of_products`), the CarrySpec assembly (`carry_spec_of_steps`), the telescope
(`GroupedColumns`), the chain (`RsaChain`) and the EM (`RsaEm`). What blocks the
instantiation is **variable identity**: the export's variables are anonymous `ℕ` indices,
and no proof can know that index 483 is limb `a_3` of chain 2. Linking them needs data the
exporter does not emit:

1. per gadget call, the *roles* of its plug variables (this product variable = limb `a_i`
   times `b_k`; this q/r output = limb `q_j`);
2. per `grouped_columns` invocation, its 24 step-call indices (they are consecutive — the
   loop runs to completion — so runs of 24 in `callsOf` order suffice).

With that, the instantiation is: per chain, 24 × `carry_of_sat_shadow` with the bound from
the limb ranges, `carry_spec_of_steps`, `mul_eq`, and the chain/EM lemmas — mechanical and
about 17 tactic invocations if the roles are emitted as concrete lists. Emitting them is
an `xtask/src/lean.rs` change; the Lean side then needs a `Chain` record and a tactic that
unfolds `shadow σ plug` over the concrete terms and closes each with `val_of_mul`.

## The circuit export (option 1 was taken)

The chain now witnesses each carry: `grouped_column_step` does
`hint_div_rem(num, 2^164)`, pins `num = 2^164·k` and the remainder to zero, and
range-checks `k` — 91 rows, +816 per circuit. That made
`lean-export --example rsa2048` viable: with the chain gadgets marked, the export
is **597 segments, 125,856 rows, 3 parts** (the flat row hash is unchanged:
`fnv1a64:860142cc226105b8`), hash-gated in `CircuitHash.lean`. The affine-carry design would have
been 30 MB. The frontend refuses a hint output that no row pins, which is why the
remainder needs its own row.

## Older note: why the export was blocked on nesting

`lean-export --example rsa2048` writes 30 MB (88 parts): `grouped_column_step` returns an
LC and the caller uses it as the next `cb_prev`, so each call's plugs nest the previous
one's, and the exporter spells every LC out. Two ways out, both deliberate:

1. **Allocate a variable per carry** (a row `k_j = 0 + ...` or a `let` the frontend turns
   into a witness pin): small export, but a digest change and ~24 extra rows per step
   chain — the opposite of the row-count work.
2. **Share subterms in the exporter** (`xtask/src/lean.rs`/`coverage.rs` render `ZLC`s
   flat): no circuit change, but the ECDSA export and its hashes change, and the Lean
   `rows` must still hash to the compiler's rows (share only in the *plugs* of `Call`s,
   whose rows hash from the template, not from the rendered LC).

Until one lands, the row→step-identity bridge stays prose in `docs/security.md` §2.18.

## Workflow lessons (hard-won)

- **Model, then `decide +kernel`.** A 400 KB template works: write the generic
  rows in a small `.lean` file (`RangeDerived.lean`), show
  `template.rows = rows (limbs L B Wtop)` by `decide +kernel`, transfer with one
  `soundness_of`. `Formal/Templates/RangeCheckLimbs17x121.lean` (343 KB) is the
  precedent. Never export a monolithic `grouped_columns` (130 MB).
- **Variable layout of `range_derived::<W>`.** Bits at `wit (base + 2i)`,
  `base = (2B-1)·j`; `2W-1` variables per block (odds and the last are unused);
  `W-1` boolean rows plus `⟨top, top − 2^(W-1), 0⟩`. `top` is affine, so no
  top variable exists.
- **`simp` rewrites `a * b = 0` to a disjunction** (`mul_eq_zero` is simp), which
  breaks `simpa [Row.Sat]` against a product-equality goal: use `simpa only
  [Row.Sat, LC.eval, List.map_nil, List.sum_nil, add_zero]`.
- **`omega` does not see through projections**: after `obtain ⟨v, base, W⟩ := b`,
  `hW : b.2.2 ≤ 253` stays `(v,base,W).2.2 ≤ 253` and is a different atom from
  `W`; add `have hW' : W ≤ 253 := hW` before any `omega`/pow goal.
- **`rw [h]` with `h : W = (W-1)+1` rewrites inside `W-1`**: use `conv_rhs` or a
  `calc` with `pow_succ`.
- **LC plugs need a `Consts` obligation**: a gadget called with non-variable
  plugs and no assumptions needs `Formal/Templates/Consts/<Gadget>.lean`'s
  `theorem soundness_free`; hand-write the 2-line file the generator would emit
  and import it from `Formal.lean`.
- **Coverage is per example**: `cargo xtask lean-export --coverage --circuit
  examples/rsa2048` is the fast loop; `--update` (all examples) only rewrites
  `Consts/`.
- `lake`: `source $HOME/.elan/env`; `lake build` is the kernel gate;
  `AxiomCheck.lean` must print "standard axioms only" (71 harnesses).

## Mapping xark → zkGolf/Clean

| xark | zkGolf/Clean |
|---|---|
| `RequireLt25x82` | `LessThan` |
| `grouped_columns` / `square_lazy` / `fused_final` | `MulMod` + `EqViaCarries` |
| `convert_wide` | `Normalize` |
| terminal `fused_final` + EM | `Equal` |
| `bytes_to_wide` | `BytesToBigInt` |
| `sha256_em_bits_82` / `sha256_em` | `PadDigest` |
| `verify_wide` / `verify_sha256_bytes` | `Main` |
| `xark build` / `lean-export` / `coverage` / `digests` | `Cost` / `IsR1CS` / `Witgen` |

## Bridge order

1. `grouped_columns`: carry = `num/2^164` affinely; `num < 2^253`; `2^164*c <
   2^253`; both below Fr; divisibility; top column.
2. `square_lazy`: q/r bounds, 16 squarings, the 25×82 columns.
3. `fused_final`: q and EM pin.
4. `convert_wide`: 17×121→25×82, nonzero remainder; do not use the affine-carry
   trick there.
5. `bytes_to_wide`: `to_bits::<8>`; big-endian bit placement; top 2 bits zero;
   `n_top`.
6. `minus_one`: `m−1`; the `RequireLt25x82` LC plugs.
7. `verify_wide`: `n` exactly 2048 bits; `sig<n`; the chain; the EM.

## No-go

- No pinned/constant modulus.
- No relation changes (even modulus stays accepted).
- No `native_decide`; no statement changes; no new axioms.
- No deleting q/r or carry checks without a sound replacement.
- No 24×86/23×90 paired widths (they violate `S_j < Fr`).

## Where the rsa2048 composition stands (end of session)

Every ingredient exists and is proven:

| ingredient | lemma |
|---|---|
| a call's rows give its template's `Sat` | `Call.sat_rows` |
| a step's rows give its integer row (`num = 2^164·k`) | `GroupedCarry.carry_of_sat_shadow` |
| a plug's shadow is its products' sum | `Shadow.shadow_of_products` |
| 24 step rows → `CarrySpec` | `GroupedColumns.carry_spec_of_steps` |
| `CarrySpec` → the column identity → `a·b = q·m + r` | `GroupedColumns.soundness`, `mul_eq` |
| 16 squarings + the final multiply | `RsaChain.chain` |
| the encoded message | `RsaEm.em` |
| the production circuit's call contracts | `Rsa2048Calls` (408 / 17 / 16, `decide +kernel`) |

What is left is the **row-level model of the `grouped_columns` template**: 704 KB,
`plugs := 125`, `wits := 5546`, 3,435 rows = 1,250 products + 24 × 91 step rows + 1 top row.
Its exact shape (verified against the exported rows):

* plugs: `a` = 0..24, `b` = 25..49, `m` = 50..74, `q` = 75..99, `rhs` = 100..124;
* products: `wit (2(i·25+k))` = `a i · b k`, `wit (2(i·25+k)+1)` = `q i · m k`, i,k < 25
  (the `hints` list is exactly these `.product` entries, in that order);
* columns: `lhs c = Σ_{i+k=c} wit (2(i·25+k))`,
  `rhs c = Σ_{i+k=c} wit (2(i·25+k)+1) + (if c < 25 then plug (100+c) else 0)`;
* step instance j < 24 starts at `1250 + 179j`: `q_j` = that, `r_j` = +1, bits at
  `+2+2t` (t < 88), the derived top at `+178`; its rows are the step template's 91 rows
  with plugs `lhs (2j), lhs (2j+1), rhs (2j), rhs (2j+1), cb` (`cb` = `2^88` at j = 0,
  else `wit (1250+179(j−1))`);
* the top row is `lhs 48 − rhs 48 + wit 5367 − 2^88 = 0` (5367 = `1250 + 179·23`),
  matching `wit 1248 = lhs 48`, `wit 1249 = rhs 48`.

Then `rows_eq` by `decide +kernel`, the assembly above, and (only then) the marker.

**Measured against the real template (round 48):** the 1,250 product rows above are exactly
right — `decide` over `template.rows[0..1250]` against the model finds no mismatch. The 24
step instances do **not** match `Row.bind` alone: the exported template holds the
frontend's *normalized* linear combinations (terms sorted by variable, duplicate
coefficients merged, zeros dropped), while `LC.bind` is a raw `flatMap` that preserves the
step template's term order and repeats variables. So the model needs a `norm : LC → LC` applied to each bound row before comparing, and only
then does `rows_eq` reduce to `decide`. The invariant to reproduce (`xtask/src/lean.rs`'s
`var`, `lean.rs:553`): a term's variable code is `v < plugs ? .plug v : .wit (v - plugs)`,
and the exported list merges each variable into its **first occurrence** (summing its
coefficients, dropping zeros) — *not* sorted by code (a sampled row ran `wit 3, wit 51,
plug 101, wit 1250`). `normTerms` should therefore `partition` on the head's variable,
merge, and recurse on the remainder (recursion needs `termination_by l.length`; the
`List.length_filter_le` bound is immediate), with `eval_norm : (norm l).eval σ = l.eval σ`
as the soundness fact. (`CircuitHash`
is unaffected because its hash canonicalizes before hashing; `Call.rows` vs the compiler's
rows differ only in representation.) Marking the function as a
`#[gadget]` and exporting the harness is already measured to work; the marker cannot land
until the proof imports `Formal.Templates.GroupedColumns` (the exporter enforces it). After
that, re-export the circuit: 17 top-level calls, and the composition is 17 `sat_call`s
with the q/r `Spec`s supplying the limb bounds.

The work is a single large proof plus mechanical instantiation, not an open design
question; every number it needs is in this file.

## The composition (done, at the limb level)

`Formal/Circuits/Rsa2048Verify.lean` reaches the 17 chain calls by index
(`seg`/`callAt`/`segSat`, no `callsOf` template comparisons), applies
`GroupedColumnsSquareGadget.soundness` / `GroupedColumnsGadget.soundness` to each
(`square_contract`/`general_contract`), builds each call's `Assumptions` from the
adjacent `range_check_q`/`range_check_r` `Spec`s (`q_call_bound`/`r_call_bound`
plus the LC window equalities), and matches the chain's limb vectors by LC
equality (`val_limb_eq`). `Formal/Circuits/Rsa2048Chain.lean` then proves
`chain_congruence`:

```
chainEm σ ≡ (val (limb sq0 σ 0)) ^ (2^16 + 1) [ZMOD chainN σ]
```

with only three hypotheses left, the packed limbs' bounds:
`hSig`/`hN` (the first call's `a` and `m` plugs, i.e. the signature and modulus
limbs) and `hEm` (the terminal call's right-hand-side plugs). Those, and the
integer identities `chainN = n`'s big-endian integer, `chainA 0 = sig`'s, and
`chainEm = RsaEm.em digestBits`, are the byte packing's: 544 `to_bits` calls
`s0..s543` (byte `b` at base `544+7b`, outputs `[bit7, bit0..bit6]`), whose
`Spec` is `ins < 2^8 ∧ outs = bits of ins`. `bytes_to_wide`'s limb LCs are
literal sums of those bits (`(2^t, bitvar)` and the affine bit7), so a limb's
bound and integer identity follow from the `to_bits` `Spec`s by evaluating the
LC. `RequireLt25x82` (s545) gives `sig < n` at the limb level; `n_top` is the
`bytes_to_wide` glue row. Anything after that (e.g. the host-level byte
statement) is the same identities rearranged.

Packing progress: `Formal/Circuits/Rsa2048Packing.lean` has the bit model —
`to_bits::<8>` returns `[bit 0, …, bit 7]` with **bit 0 affine**
(`byte − Σ_{s<7} 2^{s+1}·wit_s`) and bits 1..7 the witnesses `base = 544 + 7b`;
`bytes_to_wide`'s bit `j` is byte `off + 255 − j/8`, bit `j % 8`, weight
`2^{j % 82}` (off 0 for `n`, 256 for `sig`; `j < 2048` only), and the `em` limbs
add `EM82_CONST` (digest bits `j < 256`, byte `512 + 31 − j/8`). All 75 packed-limb
LCs are proved equal to that model after `normTerms` (`nTerms*`, `sigTerms*`,
`emTerms*`, `emConst*`, `decide +kernel`). `Formal/Circuits/Rsa2048PackBound.lean`
proves the generic bound: `pack_bound` (a 25×82 limb is `< 2^82` once each bit is)
via `eval_normTerms` and a weighted-sum/`ZMod.val` argument. Remaining: the 75
concrete specializations (`eval_eq_of_norm_eq rfl (nTerms q)`), the bit-is-a-bit
fact from the 544 `to_bits` specs (`ToBits.SpecAt`: `ins < 2^8`,
`outs = bits of ins`; `bitOf` is 0/1), the integer identities
(`val (n limbs) = big-endian n`, same for `sig`, `val em = EM_PREFIX + digest`), and
`RequireLt25x82`/`n_top` for `sig < n` and the 2048-bit bound. The machine's swap is
full, but the earlier multi-minute hangs were `maxHeartbeats 0` hiding a bad
`omega` metavariable in `val_weighted`; with that fixed the module compiles in
seconds (plus ~1s per `decide`).

Progress: `Formal/Circuits/Rsa2048PackBound.lean` now proves
`nBound0..24`, `sigBound0..24` (via `packCanon`/`decide +kernel` and
`pack_bound`) and `emBound` for every limb except **q = 3** (q ≤ 2 use
`pack_bound 288 q`, since `emTerms q = packTermsAt 288 q`; q ≥ 4 are
constant-only and `decide`). Left: em q=3 (constant `em82 3` plus the 10 digest
bits `j = 246..255`; bound `em82 3 + 2^10 - 1 < 2^82`), the 544 `to_bits` bit
facts (`hbit`: per call `call_sat_of`, `ToBits.SpecAt` gives
`outs = bits of ins`; note `(callAt b).t = ToBits.template` is `rfl`, and
`(bitGLC b tb).eval σ = outs.getD tb 0` needs the output LCs unfolded — bit 0 is
the affine combination, bits 1..7 are `var (544+7b9+s)`), then the integer
identities, `RequireLt25x82`'s limb order and `n_top`, and the final statement.

Status: all of the above now holds. `Formal/Circuits/Rsa2048PackBoundW.lean` (width-`w`
bound, `emBound3`, `bitOut`/`bitGLC_eq_bitOut`/`bitOf_val_le`),
`Formal/Circuits/Rsa2048Bits.lean` (`bits0..543`, `hbit`; the `callAt b` facts are
`rfl`, not `decide`, or the 544 proofs blow up), and
`Formal/Circuits/Rsa2048Statement.lean`:

```
theorem chain_congruence_sat (σ : ℕ → F) (h : Sat circuit σ) :
    chainEm σ ≡ (val (limb sq0 σ 0)) ^ (2 ^ 16 + 1) [ZMOD chainN σ]
```

are all checked (`lake build` green, AxiomCheck 2,789 theorems standard axioms).
`Formal.lean` imports the packing modules. Left for the byte-level statement:
`RequireLt25x82` at `s545` (its 50 plugs are `sq0`'s 0..49; `Spec` is a `limbs`
comparison, so `sig ≤ n − 1`), the `n_top` row, and the integer identities
(`chainN`/`sig`/`chainEm` versus the big-endian byte values and
`EM_PREFIX + SHA-256 digest`). The limb-level chain statement is the composition
the objective names; the byte identities are the encoding layer around it.

Proven-proof layout: the hand-written files live in `formal/Formal/Circuits/Rsa2048/`
(`Verify`, `Chain`, `Packing`, `PackBound`, `PackBoundW`, `Bits`, `Statement`) because
`cargo xtask lean-export --check` scans every `Formal/Circuits/*.lean` for a
`--example` header and would fail on them in the parent directory. `s545` is the
`RequireLt25x82` call: its first 50 plugs are the packed 25×82 limbs of `sig` and of
`n − 1` (the last m plug carries a `-1` on a wire), so its `Spec` (`RequireLt.Spec`,
a `limbs` comparison) gives `sig ≤ n − 1`, i.e. `sig < n` once the plug LCs are
matched to `sq0`'s by window equality. The `n_top` row is the `bytes_to_wide` glue
pinning `n`'s top bit.

Next piece (in progress, no repo file yet): connect `chainEm` to `RsaEm.em`. Define
`digestBits σ j = (((bitGLC (543 - j/8) (j%8)).eval σ).val : ℤ)` (digest byte
`512 + 31 - j/8`, bit `j%8`), `emCanon q = ⟨em82 q, normTerms (emTerms q)⟩`, and prove
`emOut (digestBits σ) q = (pn fin σ (100+q) : ℤ)` for each `q < 25` (q ≤ 2: use
`packCanon 288 q` since `emTerms q = packTermsAt 288 q`, then `eval_packTerms` +
`val_weighted`; q = 3: `emCanon3_eval` + `eval_packTermsW` + `val_weightedW 10`;
q ≥ 4: the plug is the constant, `em82 q`). Then
`val (limb fin σ 100) = Σ q pn·W^q = Σ q emOut q·W^q = val (emOut (digestBits σ))`,
and `RsaEm.em` gives `chainEm = EM_PREFIX + Σ digestBit_j·2^j`, so the final theorem
is `Em.em (digestBits σ) ≡ (val (limb sq0 σ 0))^(2^16+1) [ZMOD chainN σ]`.

Done: `Formal/Circuits/Rsa2048/EmBits.lean` proves `pn_emOut_0..24`,
`val_em_limb` (`val (limb fin σ 100) = val (emOut (digestBits σ))`), `chainEm_eq`
(`chainEm σ = EM_PREFIX + Σ_{j<256} digestBits σ j · 2^j`) and
`chain_congruence_em` (`EM_PREFIX + Σ digest bits ≡ sig^(2^16+1) [ZMOD n]` for every
satisfying assignment). Its `limbOf_small` helper (`82q + w = 256` ⇒ the range-82
`limbOf` sum is the first `w` terms) is what limb 3 needs. The run-time gotcha:
`pn_emOut_k` takes `(σ) (h)` only for `k ≤ 3` (the higher limbs are constants, no
`hbit`). Gates: `lake build`, AxiomCheck (2,820 theorems, standard axioms),
`lean-export --check` (71/71), `lean-export --coverage`, `CircuitHash` (Rsa2048
`860142cc226105b8`) all green.

Byte layer (in progress, `Formal/Circuits/Rsa2048/ChainBits.lean`, committed): `nBits σ j`
= the modulus's big-endian bit (`bitGLC (255 - j/8) (j%8)`), `sigBits` = bytes
`256 + 255 - j/8`; `pn_n_0..24`/`pn_sig_0..24` prove each chain limb is
`RsaBytes.limbOf … 82 2048 q` (q ≤ 23 with `limbOf_full`, q = 24 with
`limbOf_last` at width 80 and an `hL` sum-subset step before `Nat.cast_sum`), and
`chainN_limb`/`chainSig_limb` put the 25 limbs back into a `val`. Remaining:
(1) `chainN_packing` (`RsaBytes.packing`), (2) 512 per-byte decomposition theorems
`((σ i).val : ℤ) = Σ_{t<8} nBits (8*(255-i)+t) * 2^t` — they must be *concrete* in
`i` because `callAt i`/`seg i` don't reduce symbolically; per byte: `call_sat_of` +
`ToBits.SpecAt` gives `outs = bitOf (σ i)`, `Add32.word_testBit` decomposes
`(σ i).val < 2^8`, and `bitGLC_eq_bitOut`/`bitOut_eval` link `nBits` to `outs` (gotcha:
`bitGLC_eq_bitOut`'s explicit arguments and `hins`'s `simp` over `Template.ins`), then
(3) `RsaBytes.bytes_of_bits` gives `chainN = ↑(Σ_i (σ i).val · 256^(255-i))`, same
for `sigBits` with bytes 256..511. `sig < n` still needs the s545 subtraction/glue
layer (its m plugs are not `sq0`'s modulus limbs — `decide` confirms).

Done since: `Formal/Circuits/Rsa2048/ByteBits.lean` generates all 512 per-byte
decompositions (`nbyte_0..255`, `sbyte_0..255`; each concrete byte uses `call_sat_of`
+ `ToBits.SpecAt`, `Add32.word_testBit`, `bitGLC_eq_bitOut`/`bitOut_eval`, with
`hins`/`hlt`/`hbitval` exactly as in `nbyte_0`), lifts them to `nBits_eq`/`sigBits_eq`
by `interval_cases`, and proves `chainN_packing`/`chainSig_packing` (`RsaBytes.packing`)
and `chainN_eq_bytes`/`chainSig_eq_bytes` (`RsaBytes.bytes_of_bits`):
`chainN = Σ_i (σ i).val·256^(255-i)` and `val (limb sq0 σ 0) = Σ_i (σ (256+i)).val·256^(255-i)`.
`chain_congruence_bytes` then states the chain congruence over the public bytes with
the RFC EM prefix+digest bits. The digest bytes (512..543) still enter as bits; a
32-byte `bytes_of_bits` variant (or the shift-into-256-bytes trick) would make
`chainEm` byte-level.

`n_top`: s544's first glue row is `-2^79 + 2^79·var 550 = 0` (const `Int.negSucc
604462909807314587353087`, term `2^79` at 550), i.e. `σ 550 = 1`. Var 550 is byte 0's
bit 7 (`bitBase 0 + 6`), and byte 0 is the modulus's most significant byte, so
`nBits σ 2047 = 1` and `n ≥ 2^2047`; the upper bound is each byte `< 256`. Extracting
that row needs the `Sat`-to-row helper (`segSat` in `Verify.lean`).

`n_top`/`n_bits` are now proven in `ByteBits.lean`: `n_top` extracts s544's first glue
row (`Sat (seg 544).rows σ` via `segSat`, then `List.getElem_mem` and unfolding
`ZRow.toF`/`LC.eval`), `nByte0_ge`/`chainN_ge` (the `128·256^255` term), `nByte_lt`
(each byte `< 256` from `nBits_eq` + `hbit`), `chainN_lt` (geometric
`(255)·Σ256^k = 256^256−1` via `Finset.sum_range_reflect` + induction), and
`n_bits : 2^2047 ≤ chainN ∧ chainN < 2^2048`.

`sig < n`: the Rust is `minus_one` then `require_lt` (gadgets/xark-rsa/src/lib.rs:610).
`minus_one` (xark-bignum) computes `out[i] = m[i] − borrow_i + borrow_{i+1}·2^82`,
`borrow_0 = 1`, `borrow_{i+1} = borrow_i · (m[i] == 0)`, and `require_eq(borrow_25, 0)`.
Summing gives `Σ out_i·W^i = Σ m_i·W^i − 1` (telescoping), so s545's m limbs are
`chainN − 1` once the `==0` hint bits satisfy their rows (s544's glue); the Spec then
gives `sig ≤ chainN − 1`. Remaining: model the `==0`/borrow glue rows and the LC
identification `val (limb (callAt 545) σ 25) = chainN − 1`, plus the first-25-plug
window (`(callAt 545).plugs[j] = (sq0).plugs[j]` for j<25, `decide`).

`s544` has 101 rows (`#eval s544.rows.length`); per limb `i` (top to bottom) it has
three rows plus a borrow-product row. Row 0 is `(-1 + var 550) * 1 = 0` (n_top).
For limb `i`, with `x_i` its packing LC and `w`/`z` two hint vars (e.g. 4352/4353):
`x_i·w = z`, `x_i·(1 + z) = 0`, `w·(1 + z) = 0`, which force `z = −1` when `x_i ≠ 0`
and `z = 0` when `x_i = 0`, so `1 + z` is the `is_zero(x_i)` bit; the fourth row is a
`z_i·z_{i+1} = product` (the frontend's `borrow·(1+z)` mul hint). Decode the exact
per-limb rows (`(s544.rows.drop (1+4*k)).take 4`) and telescope
`Σ (x_i − (1+z_i)·borrow?)·W^i = chainN − 1` next.

Concrete forms (`#eval`, coefficients included): with `b_i := 1 − z_i` (the is_zero
bit), s544 has per limb `x_i·w_i = z_i`, `x_i·b_i = 0`, `w_i·b_i = 0` (so `b_i = 1`
iff `x_i = 0`), plus 24 product rows `borrow_i·z_i = u_i` (the mul hint `c`), and a
final `borrow_25 = 0`. The m plugs are `out_i = N_i − borrow_i + W·borrow_{i+1}`
with `borrow_0 = 1`, `borrow_{i+1} = borrow_i − u_i`, which reproduces plug 25
(`N0 + (W−1) − W z_0 = N0 − 1 + W b_0`) and plug 26. Telescoping
`Σ out_i W^i = Σ N_i W^i − borrow_0 + W^25·borrow_25 = chainN − 1`. So the proof is:
write the borrow LCs recursively (`b_0 = 1 − z_0`, `b_{i+1} = b_i − u_i`), prove each
`out_i` identity and the final row's `b_25 = 0`, telescope, and convert to
`val (limb (callAt 545) σ 25) = chainN − 1` (both sides `< r`).

Row layout (101 rows): row 0 = n_top; then, in order, 3 `is_zero` rows for limb 0,
3 for limb 1, product row `borrow_2 = b_0·b_1` (row 7), 3 for limb 2, product
`borrow_3`, …, 3 for limb 24, and the final top-borrow row (100, `a = var 4475`,
`b = c = 0`, i.e. `borrow_25 = 0`). The rows are `ZRow`s; `s544.rows` is the
`ZRow.toF` image, so to get the integer rows pattern-match
`match s544 with | .glue rs => rs`. The is_zero rows for a limb are
`N_i·w_i = z_i`, `N_i·(1−z_i) = 0`, `w_i·(1−z_i) = 0` (row `a` = the 17–20-term
limb LC), and the product row is `b_i·b_{i+1} = u` (or `borrow_i·(1−z_i) = u` for
the later borrows).

`Formal/Circuits/Rsa2048/SigLt.lean` (committed, builds in ~4 s) now has the tables
`zvar j = if j=0 then 4353 else 4357 + 5(j−1)`, `nxt i = 4360 + 5i`, the borrow LCs
`borrow 0 = 1`, `borrow 1 = 1 − z_0`, `borrow (i+2) = var (nxt i)`, and **proves by
`decide +kernel`**: `hout_0..24` (`(callAt 545).plugs[25+i] = (callAt 548).plugs[25+i]
− borrow i + W·borrow (i+1)`) and `hprod_0..23` (the product row `4i+7` has
`a = borrow (i+1)`, `b = 1 − z_{i+1}`, `c = borrow (i+2)`) and `htop` (row 100's
`a = borrow 25`). Remaining: the integer-level induction — the is_zero rows make
`b_i = 1 − z_i` a 0/1 bit (case split `x_i = 0` vs not: `x·w = z`, `x·b = 0`,
`w·b = 0`), the product rows keep the borrows 0/1, then
`(out_i.eval).val = n_i.val − b_i.val + W·b_{i+1}.val` (each out_i in `[0,W)`), so
`val (limb (callAt 545) σ 25) = chainN − 1`; the `RequireLt25x82` Spec (first 25
plugs = sig, `Assumptions` from the sig bounds) then gives `sig < n`.

`SigLt.lean` now also has, all by `decide +kernel` (committed `78f7a2f7`): for each
limb `i`, `hNa_i` (`(rowAt s_i).a = (callAt 548).plugs[25+i]`), `hNb_i`
(`.b = var w_i`, `w_0 = 4352`, `w_i = z_i − 1`), `hNc_i` (`.c = var z_i`),
`hNb2_i` (`(rowAt s_i+1).b = 1 − z_i`), `hNd_i`/`hNe_i` (third row `a = w_i`,
`b = 1 − z_i`), where the is_zero rows for limb `i` are at `s_i = 1` (i=0) or `4i`.
Together with `hout`/`hprod`/`htop` this is every algebraic fact the integer
induction needs; the next step is to turn `Sat` into the field equations
(`(ZLC.toF row.a).eval σ = shadow σ row.a` via `Xark.R1cs.shadow_toF`) and run the
0/1 case split, then finish the RequireLt Spec application (first-25 window for
`(callAt 545).plugs[j] = (callAt 548).plugs[j]`, `Assumptions` from the sig bounds).

Done (committed `871ea58e`): `s544_sat`/`rowSat`, `nF/wF/zF`, and the field equations
`E1_i : nF i * wF i = zF i`, `E2_i : nF i * (1 − zF i) = 0`,
`E3_i : wF i * (1 − zF i) = 0` for every limb, `P_i :
(ZLC.toF (borrow (i+1))).eval σ * (1 − zF (i+1) σ) = (ZLC.toF (borrow (i+2))).eval σ`
for i<24, and `T : (ZLC.toF (borrow 25)).eval σ = 0`. Each row is reached with
`rowSat` and the bridging `show (s544.rows[k]).a/b/c = ZLC.toF … from by decide +kernel`,
then `simpa [ZLC.toF, LC.eval, …, zvar, sub_eq_add_neg]`. Note: `borrow` is a `ZLC`,
so its field value is `(ZLC.toF (borrow i)).eval σ`, not `(borrow i).eval σ`.
Remaining: the 0/1 induction (`b_i = 1 − z_i` is `is_zero(n_i)`: `n_i = 0` ⇒ `z_i = 0`;
`n_i ≠ 0` ⇒ `b_i = 0`), the value formula
`(outF i).val = (nF i).val − (borrow_i).val + 2^82·(borrow_{i+1}).val` (each `out_i` in
`[0,W)`), the integer telescoping to `val (limb (callAt 545) σ 25) = chainN − 1`,
and the RequireLt Spec application.

0/1 induction done (committed `74704698`): `bF i σ = 1 − zF i σ`, `borrowF i σ =
(ZLC.toF (borrow i)).eval σ`, `bBit_0..24` (`bF i = 0 ∨ = 1`; `n_i = 0` ⇒ z=0 ⇒ b=1;
`n_i ≠ 0` ⇒ `mul_eq_zero` from `E2` ⇒ b=0), `borrowBit_0..25` (`borrow 0 = 1`,
`borrow 1 = b_0`, `borrow_{i+2} = borrow_{i+1}·b_{i+1}` from `P_i`, product of bits).
Remaining: `outVal_i` (from `hout_i`'s eval: `outF i = nF i − borrowF i + (W:F)·borrowF
(i+1)`; the integer `I = n_i.val − borrow_i.val + 2^82·borrow_{i+1}.val` is in `[0,W)`
by cases on `n_i = 0`/`borrow_i` with the recurrence, so `(outF i).val = I`), then the
telescoping `Σ outF_i·W^i = Σ nF_i·W^i − borrow_0 + W^25·borrow_25 = chainN − 1`, then
`RequireLt25x82.soundness` (first-25 window, `Assumptions` from `sigBound`) for
`sig ≤ chainN − 1`.

The step `outF i = nF i − borrowF i + (W:F)·borrowF (i+1)` needs the evaluations of the
LC combinators `addLC`/`negLC`/`smulLC` under `ZLC.toF`; a direct `simp`/list-induction
attempt hit the `↑(-t.1)` vs `-(↑t.1)` and composed-map forms (`Int.cast_neg`,
`Int.cast_mul`, `List.sum_map_mul_left`). A simpler route: state `hout` at the *value*
level by `decide`-checking the coefficient lists (`ZLC.eval` needs a `ℤ`-assignment;
use `Xark.R1cs.shadow`/`shadow_toF` instead), or prove
`(ZLC.toF (addLC l m)).eval σ = …` via `Xark.R1cs.eval_add`-style lemmas if present.

Solved (committed `a81fec94`, `SigLt3.lean`): work at the `GLC` level instead — define
`addG`/`negG`/`smulG` (F coefficients, no casts), prove
`eval_addG` (`List.map_append`/`sum_append`, `ring`),
`eval_negG`/`eval_smulG` via the list lemmas
`sum_neg : (ts.map fun t => (-t.1) * σ t.2).sum = -(…)` and
`sum_mul : (ts.map fun t => (c * t.1) * σ t.2).sum = c * (…)` (induction with
`rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]; ring` — the two
`map_cons/sum_cons` pairs rewrite **both** sides), and `houtE_0..24`:
`outF i σ = nF i σ − (ZLC.toF (borrow i)).eval σ + (W:F) * (ZLC.toF (borrow (i+1))).eval σ`
via `congrArg ZLC.toF (hout_i)` and
`simpa [addLC, negLC, smulLC, addG, negG, smulG, ZLC.toF, Int.cast_add, Int.cast_neg,
List.map_append, List.map_map, Function.comp_def]`. Remaining: the `.val` formula (the
integer `I = n_i.val − borrow_i.val + 2^82·borrow_{i+1}.val ∈ [0,W)` by cases), the
telescoping, and `RequireLt25x82.soundness`. The Rust's
`out[i] = m[i] − borrow_i + next_{i+1}·W`, `borrow_0 = 1`,
`next = borrow·is_zero`, expanded through these LCs, is the identity to prove; the
sign/constant bookkeeping (`W−1`, `−W·s_0`) needs care. All byte-level modules are
now imported by `Formal.lean` and the gates are green (`lake build` 3355 jobs,
AxiomCheck 3440 theorems, `lean-export --check` 71/71, coverage, digests,
CircuitHash `860142cc226105b8`).

Digest bytes (drafted in `/tmp/gen_embytes.py`): a generic
`bytes_of_bits_n (n) (_hn) (bits bytes) (hbyte) : Σ_{i<n} bytes_i·256^(n-1-i) = Σ_{j<8n} bits_j·2^j`
(compiles, 2.4 s), 32 per-byte `dbyte_k` (`((σ (512+k)).val : ℤ) = Σ_{t<8} digestBits (8*(31-k)+t)·2^t`,
same proof as `sbyte`), `digestBits_eq` by `interval_cases`, and then
`chainEm_bytes … = EM_PREFIX + Σ_{k<32} (σ (512+k)).val·256^(31-k)`. The first three
compile in ~5 s; `chainEm_bytes`'s `exact (bytes_of_bits_n 32 …).symm` (also with
`add_left_inj.mpr`, and with `rw`/`congr`) stalls for many minutes — likely the
big-sum/`8*32` unification at the instantiation. Next: specialize
`bytes_of_bits_n` to `n = 32` (a concrete copy) or prove the 32-byte identity with an
inline `calc`/`sum_bij`, avoiding the instantiation. `n_top`/`n_bits` are committed
in `ByteBits.lean` (`9acb7842`). Gotchas:
`pn` unfolds to `((ZLC.toF (c.plugs.getD i)).eval σ).val` (rewrite `hplug` directly),
and `((bitTerms ...).map ...).sum = (bitGLC ...).eval σ` needs `LC.eval`'s `0 + …`
unfolded (`simp only [bitGLC, LC.eval, zero_add]` on a standalone goal).

## `sig < n` (done, 2026-11)

`SigLt3.lean` (committed `39c5555c`): `val_formula` is the generic value formula,
`(out.val : ℤ) = n.val - bo.val + W·bn.val` under `hout : out = n - bo + W·bn`,
`hrec : bn = bo·b`, the 0/1 facts for `bo`/`b`, and `n = 0 ↔ b = 1`; the proof splits
`bo = 0` (`bn = 0`), `bo = 1, b = 1` (`n = 0`, `bn = 1`, `out.val = W−1`), and
`bo = 1, b = 0` (`n ≠ 0`, `bn = 0`, `out.val = n.val − 1`), all by `ZMod.val_sub`/
`val_cast_of_lt` and `Nat.cast_sub`, so no subtraction crosses a cast. `hrec_0` needs no
`h` (`borrow 1 = bLC 0`, `borrow 0 = 1`); `hrec_{i+1}` is `(P_i).symm` with `bF`
unfolded. `hnb_i` is `E1` (`n = 0 ⇒ z = 0 ⇒ b = 1`) and `E2` (`b = 1 ⇒ n·1 = 0`).
Then `outVal_0..24` instantiate it. **Gotcha:** state the formula in `ℤ` (`((outF i σ).val : ℤ)`);
written without the coercion, Lean elaborates the goal in `ℕ` (nat subtraction), and the
`exact`/`simpa` against the `ℤ` lemma hangs for minutes instead of failing.

`SigLt4.lean` (committed `00301b3d`): `telescope` sums
`a i = b i − c i + W·c(i+1)` over `range 25` and cancels the shifted sum
(`Finset.sum_range_succ'` on the RHS via `conv_rhs`, `Finset.sum_range_succ` for
`range 26`), giving `Σ a·W^i = Σ b·W^i − 1` from `c 0 = 1`, `c 25 = 0`.
`val_minus_one : val (limb (callAt 545) σ 25) = chainN σ - 1`; `hleft`/`hright` are the
`limb`/`pv` unfoldings (`rfl`/`simp [val, limb, pv]`, `Nat.zero_add` for offset 0).
The `outVal` dispatch is `interval_cases i` with 25 bullets (a `<;>` chain of
`exact outVal_k` type-checks too slowly).

`SigLt5.lean` (committed `f78fc29e`): `req_ins`/`req_ins_take` read the range check's
50 inputs from `RequireLt25x82.is_model.1` and `RequireLt.inputs` (the literal
`template.inputs` would unfold the whole 1,700-row template; never `simp [template]`).
`first25_window` is `(callAt 545).plugs.take 25 = (callAt 548).plugs.take 25`
(`decide +kernel`), `first25_bound` combines it with `sigBound0..24` via
`getD_of_window0`. The bound side uses `RequireLt.spec_iff is_model` (avoids the
`getD` bookkeeping entirely), then `limbs_cast : ↑(limbs a 82 n) = Σ (a j : ℤ)·W^j`
(`Nat.cast_sum/mul/pow`, `Nat.cast_ofNat`, `pow_mul`), and `val_limb_eq` for the
first-25 window: `sig_le_minus_one : val (limb sq0 σ 0) ≤ chainN σ - 1`. Finally
`chainSig_lt_chainN` (`n ≥ 2^2047`), and over the bytes `chainSig_bytes_lt_chainN` /
`chainSig_bytes_lt_bytes` (the host-level `sig < n`). Together with
`chain_congruence_bytes` the byte-level verification statement (2048-bit `n`,
`sig < n`, `em ≡ sig^65537 mod n`) is complete.

Gates after importing `SigLt`/`SigLt3`/`SigLt4`/`SigLt5` into `Formal.lean` (committed
`1c6150e0`): `lake build` 3,359 jobs; AxiomCheck 3,915 theorems standard axioms;
`lean-export --check` 71/71; `lean-export --coverage` green (136 s); `digests --check`
all 76 circuits (1.99.1); `CircuitHash` Rsa2048 `fnv1a64:860142cc226105b8`.

## End to end (2026-11)

`Formal/Circuits/Rsa2048/VerifyWide.lean` (committed `d014479f`) names the three byte
operands (`nBytes`, `sigBytes`, `digestBytes`) and bundles the three facts as
`verify_wide_spec` (a `Prop` structure) and `verify_wide` (the same as a conjunction):

* `2^2047 ≤ n < 2^2048` (`nBytes_bits`, from `n_bits` + `chainN_eq_bytes`);
* `sig < n` (`sigBytes_lt_nBytes`, from `chainSig_bytes_lt_bytes`);
* `EM_PREFIX + Σ_{k<32} digest_k·256^(31−k) ≡ sig^65537 (mod n)` (`emBytes_congruence`,
  from `chain_congruence_public`).

Gotcha: `simp [chainN]` unfolds `chainN = val (limb sq0 σ 25)` and keeps going into
`callAt 548`'s plug list and the 597-element `circuit` — it hangs. Rewrite with
`chainN_eq_bytes` instead, never unfold `chainN` under `simp`.

`docs/security.md` §2.18 (committed `a558b4b3`) no longer lists the composition,
`minus_one`/`sig < n`, or the whole-circuit assembly as audit residuals; it records
them as theorems and keeps the two deliberate exclusions (the digest is a public
input, `n`'s oddness/semiprimality is unproven). `bytes_to_wide` and
`sha256_em_bits_82` are plain functions with no exported template, so there is no
row-level model for them; their values are proved from the exported rows
(`chainN_eq_bytes`, `chainSig_eq_bytes`, `chainEm_bytes_32`). Giving them a template
would mean marking them `#[gadget]`, i.e. touching the gadget source.

Gates after the bundle: `lake build` 3,360 jobs; AxiomCheck 3,923 theorems standard
axioms; `lean-export --check` 71/71; coverage 152 s; `digests --check` 76/76 (1.99.1);
`CircuitHash` Rsa2048 `fnv1a64:860142cc226105b8`.

### The canonical-residue lemma (2026-11)

`VerifyWide.lean` also proves `emBytes_lt_nBytes` / `chainEm_lt_chainN`: the encoded
message is below the modulus. The prefix's leading byte is `0x00`, so
`EM_PREFIX < 2^2040`, and `digestBytes < 2^256` (each digest byte is a sum of 8 bits,
`digestByte_lt`); with `n ≥ 2^2047` that gives `EM < 2^2041 < n`. `rsa_verify_equation`
then turns the congruence into the standard check `sig^65537 % n = EM`. Without `EM < n`
the congruence alone does not say `RSAVP1 = EM` (a larger encoding could be hit at
`sig^e mod n = EM − n`), so this is the fact that makes `verify_wide_spec` the PKCS#1
verifier's contract. `VerifyWideSpec` has fields `n_bits`, `sig_lt`, `em_lt`, `em`.

Gotchas on that proof (`Exponentiation` and `positivity`):
* `norm_num` will not evaluate `2^2040` at its default cap — set
  `set_option exponentiation.threshold 4096`, and `EM_PREFIX < 2^2040` itself is a
  `decide +kernel` (the literal is 2040 bits).
* **Do not call `positivity` on `digestBytes σ`** (a `Finset.sum` over 32 byte
  products): it does not terminate in reasonable time. Prove `0 ≤ digestBytes` with
  `Finset.sum_nonneg` and `mul_nonneg (Int.natCast_nonneg _) (pow_nonneg (by norm_num) _)`.
* `chainEm = EM_PREFIX + digestBytes` is `chainEm_eq` composed with
  `chainEm_bytes_32`, then `rfl` (the sums are the same expression).

### zk.golf and the RFC 8017 bridge (2026-11)

zk.golf's challenge repo (`zksecurity/zk-golf-challenges`,
`Challenge/Specs/RSASSAPKCS1v15.lean`) states the RSA instance as
`verifySignature alg e n h sig = true` over RFC 8017's `OS2IP`/`I2OSP` and
EMSA-PKCS1-v1_5, with `Assumptions` = octet strings + `HasBitSize (os2ip n) (8·len)`;
its `Interface.lean` puts the signature in `Input` (public), and its `Challenge.lean`
also demands `Completeness` and `ComputableWitnesses`. Two cautions: the repo has
**no license** (`license: null`), so do not vendor or `require` it, and its interface
uses `axiom hCircomPrime`, which our AxiomCheck rejects.

`Formal/Circuits/Rsa2048/Rfc8017.lean` is our independent transcription of the RFC:
`os2ip`, `i2osp` (an `Option`, as theirs), `Octets`, `HasBitSize`,
`sha256DigestInfoPrefix`, `emsaPkcs1v15Encode` (2 + 202×0xff + 1 + 19 + 32 octets),
`rsavp1`, `verifySignature`; then `verify_wide_spec`'s facts give
`verifySignature_true` and `rfc8017_assumptions`. The load-bearing lemmas:
`os2ip_range_map` (`os2ip (range n |>.map f) = Σ f i·256^(n-1-i)`); `i2osp_cons`
(the digit split at the head) and `i2osp_os2ip` (the OS2IP/I2OSP round trip on octet
strings); `os2ip_emsa_prefix` (`decide +kernel`: the 224-octet prefix shifted by 32
octets is `EM_PREFIX`); `os2ip_append`.
Gotchas: `List.range (n+1) = 0 :: (range n).map (·+1)` needs `List.range_add` +
`List.range_one` + `List.map_congr_left`; the digit arithmetic is
`Nat.add_mul_div_right` and `Nat.add_mul_mod_self_left`; `Int.natCast_emod` and
`Int.natCast_inj` move the ℤ congruence to ℕ; `Octets` is a `∀`, so `decide` does
not fire on it — go through `List.all_eq_true` and `of_decide_eq_true`.

Not closeable from zk.golf: xark's template models (different framework), the 17×121
entry point (no example circuit), the signature's visibility (their public `Input` is
a precedent, but changing ours re-keys), completeness (Clean-specific; it would need
a Lean model of the Rust witness generator), Groth16 soundness/ZK, and
`digest = H(M)` (both specs leave it as an assumption).

### `sha256_em_bits_82` is a proven gadget (2026-11, round 2)

Landed: `#[xark::gadget]` + `#[doc(hidden)] pub` on `sha256_em_bits_82`, a harness at
`formal/templates/sha256_em_bits_82/`, the generated zero-row template
(`Formal/Templates/Sha256EmBits82.lean`: 256 plugs, 0 wits, 25 output LCs) and
`Formal/Sha256EmBits82.lean`. The proof uses the conventional gadget shape:
`Assumptions (_) := True`, `Spec ins outs := ∀ q < 25, outs.getD q 0 = emOut ins q`, and
`soundness : Spec (template.ins σ) (template.outs σ)`. The key lemmas: `outputs_eq`
(`interval_cases q <;> rfl`: the generated output LC is *definitionally*
`⟨em82 q, (range w).map (2^t, plug (82q+t))⟩`), `eval_model` (a `List.sum` over `range`
is a `Finset.sum`), and `limbOf_full`/`limbOf_small`/the zero case. Coverage now says
`1 of 1 calls covered; 1 covered with LC plugs (no assumptions)`; `--update` wrote the
empty-vector `Consts/Sha256EmBits82.lean` (`soundness_free`), which `Formal.lean`
imports. `lean-export --check` is 72 templates; `CircuitHash` is unchanged.

Two traps:
* The coverage tool decides `trivial` by the *exact line*
  `theorem soundness (σ : TVar → F) (h : template.Sat σ) :`. A `_h` binder makes it
  think the gadget assumes something, and the call falls to "LC plugs: the caller must
  enforce Assumptions" (an allowlist entry). Keep the binder named `h`; reference it
  (`have _ := h`) to silence the unused-variable linter.
* A zero-row call is filtered from the example export
  (`c.parent.is_none() && c.rows > 0`), so the circuit is not renumbered; the export
  diff is empty and `CircuitHash` is unchanged.

### The other two unmodelled gadgets (2026-11, round 2)

The previous round tried `sha256_em_bits_82` and established these facts:

* It exports as a **zero-row** template: `plugs := 256`, `wits := 0`, `rows := []`, and
  the 25 `outputs` are exactly `em82 k + Σ (2^t, plug (82k+t))` — the EM limb LCs.
  `cargo xtask lean-export sha256_em_bits_82` writes
  `Formal/Templates/Sha256EmBits82.lean` (29 lines, hash `sha256:ba5286f…`).
* The example exporter only emits a segment for a top-level call with `rows > 0`
  (`calls.filter(|c| c.parent.is_none() && c.rows > 0)`), so a zero-row gadget does
  **not** renumber the circuit. That is the one safe case.
* It still refuses to export the example until exactly one *direct* file under
  `formal/Formal/` imports the template (`coverage::proof_of` scans only that
  directory), and `AxiomCheck` wants
  `Xark.Templates.Sha256EmBits82.soundness` mentioning `template` and
  `Template.Sat`.
* The contract `output q = emOut digest q` is already proven at the circuit level
  (`EmBits.lean`'s `pn_emOut_0..24`, `val_em_limb`, `chainEm_eq`), so the template
  proof would duplicate the `limbOf`/weighted-sum work for no new fact. Reverted.

The other two are worse: `bytes_to_wide` owns the 544 `to_bits` calls, and marking it
turns them into children, collapsing them from the top-level export — every `callAt`
index in `Bits.lean`, `ByteBits.lean`, `Verify.lean`, `SigLt.lean` and `Chain.lean`
shifts. `minus_one` lives in `xark-bignum` and is called by `mul_divmod`/`sub2`, so
marking it changes the curve examples' exports too. Both need a re-export and a
re-prove of the compositions, not a mechanical template.

### The 17×121 example and its circuit export (2026-11, round 3)

`examples/rsa2048_words` (commit `ce7d9dbe`) is the whole-number entry point:
`#[circuit] fn rsa2048_words(n: Public<U2048>, sig: Private<U2048>, digest: Public<[u8; 32]>)`
calling `xark_rsa::verify_sha256`. `U2048 = Bignum<17, 121>` reads a whole number
(the input reader range-checks every limb) and `convert_wide` re-limbs it to 25×82.
The KAT reuses the byte path's vector; `cargo test --release` passes; `digests
--update` under 1.99.1 gives keyed `b9ce25…`, flat `7970866a…` (77 circuits); coverage
is green with one new allowlist entry for `require_lt`'s LC plugs (the `Consts` user
lists of GroupedColumns and Sha256EmBits82 gained `rsa2048_words`).

The exported circuit (`cargo xtask lean-export --example rsa2048_words`) is **89
segments / 139,868 rows**, `fnv1a64:1758a6b6ad3aeb24`, with
`publics = [0..16] ++ [8262..8293]` (n's 17 limbs, the digest's 32 bytes; the 17
signature limbs are private). Its one 9,913-row glue segment (`convert_wide`'s plain
`range_derived` block) nested deeper than the generator's limit, so `xtask/src/lean.rs`
now emits `set_option maxRecDepth 1000000 in` for a glue segment over 1,024 rows (no
other circuit's text changes; `--check` confirms). `CircuitHash.lean` checks all three
circuits. The Lean composition of this circuit (input-reader bounds + `convert_wide`
identity + the 25×82 chain) is the remaining part of item (2).

### The words circuit's segment map and input bounds (2026-11, round 4)

`Formal/Circuits/Rsa2048/Words.lean` adds the words plumbing (`wseg`, `wcallAt`,
`wsegSat`, `wcall_sat_of`, mirroring `Verify.lean`) and the input-reader bounds:
`rcl_call_bound` with `n_limb_bound` on s0 and `sig_limb_bound` on s1 — every 17×121
limb is below `2^121`. The `Rsa2048Words` segment map (89 segments): s0/s1 the
input-reader `range_check_limbs`, s2..s33 the digest's 32 `to_bits`, s34/s35
`verify_sha256`'s explicit `range_check`, s36 the `convert_wide` glue (9,913 rows),
s37 `RequireLt25x82`, s38..s85 the 16 (q, r, square) triples, s86 the fused q check,
s87 glue, s88 the general `grouped_columns`. Next: the `convert_wide` row model (the
glue's 25 column equations for n and sig, then `RsaConvert.telescoping`) and the chain
assembly with the gadget contracts.

### The `convert_wide` glue model (2026-11, round 5)

s36 (9,913 rows) is the lowering of *two* `convert_wide` calls (n, sig). Per column:
one `num = W·carry + limb` row (`a = num − W·carry − limb`, `b = 1`, `c = 0`), then
`range_derived::<82>(limb)` and `range_derived::<118>(carry)` (W−1 booleanity rows and
the top row `top·(top − 2^(W−1)) = 0`); the last column adds `require_eq(carry, 0)` and
`range_derived_top::<80>`. `Formal/Circuits/Rsa2048/ConvertGlue.lean` models one block
over *circuit* variables (`gbit base i = base + 2i`, `gacc`, `gtopA`/`gtopB`,
`gblockRows`) and proves `gblock_sound` — the glue-level `RangeDerived.block_sound`.
Next: check the ~50 blocks of s36 against it by `decide`, extract the 25 column
equations per operand, and apply `Xark.Rsa.Convert.telescoping` (`cols_sum`,
`partial_sum`).

### s36's exact decomposition (2026-11, round 5 continued)

Parsing the 9,913 rows of s36 (Part1.lean) against the Rust: **two `convert_wide`
calls, the `n_top` check, then `minus_one`**.

* rows 0..4905 — `convert_wide(n)`: 25 carry rows at 0, 201, …, 4824 (each followed
  by the 82-row `limb` block and the 118-row `carry` block) and the `require_eq(carry,0)`
  at 4825 (the final column's `range_derived_top::<80>` is rows 4826..4905).
* rows 4906..9811 — `convert_wide(sig)`, the same shift by 4906 (num rows at
  4906..9730, require at 9731, top block 9732..9811).
* row 9812 — `require_eq(n_top, 2^79)` (`a = n_top − 2^79`, `b = 1`, `c = 0`), the
  2048-bit check.
* rows 9813..9912 — `minus_one(n)`: 25 limbs × 4 rows (is_zero and product/out rows),
  ending with `borrow_24 = 0` at 9912.

The first carry row is
`a = x_0 − W·carry_0 − limb_0`, `b = 1`, `c = 0` (vars 16746/16747); column j's is
`a = 2^(121j%82)·x_j + carry_{j-1} − W·carry_j − limb_j` (one input term, since
121/82 < 2 so each column gets at most one input limb). So:
`cols x j + carry_{j-1} = W·carry_j + limb_j`, exactly `RsaConvert.partial_sum`'s
hypothesis, with `carry_{-1} = 0` and the final `carry_24 = 0`; the 82/118-bit blocks
give `limb_j < 2^82`, `carry_j < 2^118` (the last `limb_24 < 2^80` via
`range_derived_top::<80>`). That is the whole convert ingredient; `RsaConvert.telescoping`
then gives `Σ limb_j·W^j = Σ x_i·2^(121i)`. The words minus_one rows are the byte
path's `SigLt` analysis with the variables shifted (s544's rows in that circuit), so
that part can be re-instantiated from `SigLt.lean`'s pattern.

### The first convert column, proven end to end (2026-11, round 7)

`ConvertGlue.lean` now has the whole pipeline for one column: `growAt`/`growAt_sat`
(row facts from `Sat s36.rows`), `sat_slice`/`gblock_sat` (a `gblockRows` slice of
s36 inherits `Sat`), `int_eq_zero_of_cast` (a field zero whose integer form is
`-r < E < r` is zero — via `ZMod.val_natCast_of_lt`), and `col0_eq`:
`(σ 0).val = W·(σ 16746).val + (σ 16747).val`. Two traps: the input limb bound needs
`pn (wcallAt 0) σ 0 = (σ 0).val` (the plug is `LC.var 0`; `rfl` for the `env` fact,
then `simp [pn, Call.lift, ...]`), and `open Xark.Rsa.GroupedColumns (val W)` must be
in scope or `W` is silently auto-bound (Lean's `autoImplicit`), making the statement
about an arbitrary `W`. Next: the same for the remaining 24 columns of each operand
(the row facts and block slices are `decide +kernel`; the variable numbers come from
the generated rows), then `RsaConvert.partial_sum`/`cols_sum`, `n_top`, and the
`minus_one` tail.

### The generic convert column (2026-11, round 8)

`convert_col_x` (in `ConvertGlue.lean`) proves a generic carry row with an input term
and the previous carry: from the row shape
`[(2^e, x), (1, prev), (-W, carry), (-1, limb)]`, the block bounds, and the input
bound, it derives `2^e·x + prev = W·carry + limb` over `ℤ` (via `int_eq_zero_of_cast`
with the integer `E` below `2^243 < r`). It works on real data: column 1 of
`convert_wide(n)` (row 201, x = var 1, prev 16746, carry 17146, limb 17147) is proved
by calling it with `hrow : ... := by decide +kernel` and the block slices
(`gblock_sat (k := 83/284/202)`). Traps: `mul_le_mul_of_nonneg_left` needs
`le_of_lt hb4` (and `positivity` on `2^e` works via `pow_nonneg`, not `positivity` on
`W`); `gblock_sat`'s `k` must be passed explicitly or the expected type has a
metavariable; and `2^243 < r` via `Nat.cast_lt` + `Nat.cast_pow` (plain `exact_mod_cast`
on the huge numeral hits the recursion limit). Next: the `prev`-only and input-only
shapes, then the generated 25 callers per operand.

### All 25 modulus columns, generated (2026-11, round 9)

`Formal/Circuits/Rsa2048/ConvertCols.lean` is generated from the s36 parse (a Python
script, not committed): `n_plug1..16`/`pn_n1..16` (plug i is var i), then one theorem
per column `n_col0..n_col24`, each a call of `convert_col_x` (input+prev), `convert_col_prev`
(no input: columns 3, 6, 9, 12, 15, 18, 21, 24) or `convert_col_x0` (column 0), with
the `decide` row shape and the block-slice bounds. The final column 24 proves
`n_col24_row : σ 26346 = 0` (the `require_eq(carry, 0)` row) and then
`σ 25946 = W·0 + σ 26347` (`simpa`, since `W·0 + x = x`). The whole file elaborates in
~31s; `lake build` is 3,371 jobs, AxiomCheck 4,044 theorems. Next: the same for the
signature operand (base 4906, reader 1, input vars 4131..4147), then
`RsaConvert.partial_sum`/`cols_sum` to get `Σ limb·W^j = Σ x_i·2^(121i)`.

### Both operands' columns, and the next assembly (2026-11, round 10)

`ConvertColsSig.lean` mirrors `ConvertCols.lean` for the signature: `s_plug0..16`/
`pn_s0..16` (plug i is var 4131+i), `s_col0..s_col24`, and `s_col24_row`
(`σ 36107 = 0`). `RsaConvert.telescoping` is exactly the consumer: it needs
`hrow : ∀ j < 25, cols x j + (if j = 0 then 0 else c (j-1)) = W·c j + y j` and
`c 24 = 0`, and returns `Σ_{j<25} y j·W^j = Σ_{i<17} x i·2^(121i)`. The remaining
assembly: define `xN/yN/cN` (and `xS/yS/cS`) from the var lists, prove
`cols x j = x i₀·2^(121i₀%82)` (one input term) or `= 0` (no input) per column
(`Finset.sum_eq_single` with the uniqueness over `Fin 17`, so `decide` closes it),
then `hrow` per column and `telescoping`. `lake build` is 3,372 jobs; AxiomCheck
4,104 theorems.

### The convert telescope, both operands (2026-11, round 11)

`ConvertWide.lean` (generated) defines `nIn/nLimb/nCarry` and `sIn/sLimb/sCarry` (the
concrete variable lists from the s36 parse), `xN/yN/cN`/`xS/yS/cS`, and the two `cols`
lemmas: `cols_single` (one input limb; uniqueness over `Fin 17` so `decide` closes it)
and `cols_none`. Per column it turns the `n_col<j>`/`s_col<j>` fact into
`cols x j + (if j=0 then 0 else c (j-1)) = W·c j + y j`, then `n_hrow`/`s_hrow` (by
`interval_cases`), `n_c24`/`s_c24` (the final carry is 0), and
`n_convert_eq`/`s_convert_eq` via `Xark.Rsa.Convert.telescoping`:
`Σ_{j<25} y j·W^j = Σ_{i<17} x i·2^(121i)` for both n and sig. Note `Convert.W` and
`GroupedColumns.W` are two defs of `2^82`; `simpa [Xark.Rsa.Convert.W, W]` reconciles
them. `lake build` is 3,373 jobs; AxiomCheck 4,162 theorems.

### Converted-limb bounds (2026-11, round 12)

`ConvertBounds.lean` (generated) gives `n_limb_bnd<j>`/`n_carry_bnd<j>` (and the `s_`
counterparts) from the same block slices, plus `n_limb_lt82`/`s_limb_lt82`:
every converted limb below `2^82` (the top one is proved `< 2^80` and relaxed with
`Nat.lt_of_lt_of_le`). These are what `square_contract`/`general_contract` take as
`ha`/`hm`/`hq`/`hr` — `pn c σ i < 2^82` for the four 25-limb arrays of each chain
call. `lake build` is 3,374 jobs; AxiomCheck 4,262 theorems. Next: the `n_top` row
(9812) pins `σ 26347 = 2^79 + Σ bits`, so the top limb is `≥ 2^79`; then the
mixed-radix bound `Σ y_j·W^j < 2^2048` (top limb `< 2^80`) and the chain.

### The mixed-radix bound (2026-11, round 13)

`ConvertValue.lean`: `geom_lt` (`Σ_{j<k} y j·W^j < W^k` when every `y j < W`, by
induction, fast) and `n_val_lt`/`s_val_lt`: the converted values are below `2^2048`
(split `range 25 = range 24 + {24}`; the top limb `< 2^80`, the others `< W`;
`2^80·W^24 = 2^2048` by `← pow_mul, ← pow_add`). The *lower* bound `n ≥ 2^2047` still
needs the `n_top` row: a first attempt (`n_top_eq` with `linear_combination ha` and
`nlinarith` over the 79-term bit sum) did not finish in 10 minutes and was reverted —
prove it in the `gblock_sound` style instead (`hcast` for the bit sum via
`sum_map_range`/`ZMod.natCast_zmod_val`, `word_lt` for `Σ < 2^79`, then
`int_eq_zero_of_cast`), keeping the `Finset.sum` opaque. `lake build` is 3,375 jobs;
AxiomCheck 4,265 theorems.

### The `n_top` row's verified pieces (2026-11, round 14)

`ConvertTop.lean`: `topNLC`/`topN_row` (row 9812 = `(limb_24 − Σ bits) − 2^79`, by
`decide +kernel`), `topN_eval` (the row as `−2^79 + σ 26347 − Σ_i 2^i·bit_i`; the
`LC.eval` output is `(-a)·x`, so `simp only [neg_mul]` + `Finset.sum_neg_distrib`
before `ring`), `topN_bits` (the top block's 79 bits are boolean), and `topN_hcast`
(the ℕ bit sum casts to `(gacc 26348 80).eval σ` — **`gacc base W` is over `W−1`
bits**, so the 79-bit top block needs `W = 80`, not 79; and `ring` fails on the two
`∑ i, … σ (gbit …)` vs `σ (26348+2i)` sums because they are defeq but not
syntactically equal — `simp only [gbit, zero_add]` closes). Still to do: `h1`
(`σ 26347 = ↑(2^79 + S)` from `ha`/`topN_hcast`) and `hval`
(`ZMod.val_natCast_of_lt`), then `n_top_ge` and the lower value bound. A first
attempt with `linear_combination`/`nlinarith` over the expanded 79-term sum did not
finish and was reverted — keep `S` opaque (`set`). `lake build` is 3,376 jobs;
AxiomCheck 4,269 theorems.

### `n_top_eq` and `n_top_ge` (2026-11, round 15)

`ConvertTop.lean` now proves `n_top_eq` (`σ 26347 = 2^79 + Σ bits`, with `S` opaque
via `set`, `topN_hcast` for the cast, `linear_combination ha` for the field step, and
`ZMod.val_natCast_of_lt` since `2^79 + S < 2^80 < r`) and `n_top_ge` (`2^79 ≤ σ 26347`
by `Nat.le_add_right` after `rw [n_top_eq]` — `omega` over the sum was the 10-minute
bottleneck; avoid it). The file compiles in 2.7s. The lower value bound `n_val_ge`
(needs `mul_le_mul_of_nonneg_right` and a `set` for the top term; a first version was
slow and was reverted) and the `minus_one` tail + chain remain. `lake build` is 3,376
jobs; AxiomCheck 4,271 theorems.

### `n_val_ge`: the modulus is at least `2^2047` (2026-11, round 16)

`n_val_ge` in `ConvertTop.lean`: `2^2047 ≤ Σ_{j<25} yN j·W^j`. Use
`Finset.single_le_sum` for the top term (`y24·W^24 ≤ Σ`), `mul_le_mul_of_nonneg_right`
for `2^79·W^24 ≤ y24·W^24`, and a `calc` chain; the `2^2047 = 2^79·W^24` identity is
`rw [show W = 2^82 from rfl]; ring_nf` (the `← pow_mul, ← pow_add` rewrites *loop*).
The slow trap was `positivity` on `(W : ℤ)^j` with symbolic `j`: it loops; prove
`0 ≤ W` once (`hW0`) and use `pow_nonneg hW0 j`. `n_limb_bnd24`/`n_limb_lt82` feed
`yN 24`/`nLimb.getD 24 0 = 26347`. `lake build` is 3,376 jobs; AxiomCheck 4,272
theorems. Remaining: the `minus_one` tail (9813..9912) and the chain.

### The words `minus_one` tail model (2026-11, round 17)

`MinusOneFacts.lean` (generated): the words circuit's `minus_one(n)` is s36's *tail*,
s36 indices **9813..9912** (s36 has 9,913 rows: convert(n) 0..4905, convert(sig)
4906..9811, the `n_top` check 9812, `minus_one` 9813..9912). It is the byte path's
`s544` lowering at new variables: per limb `j` an `is_zero` gadget (`m_j·w_j = z_j`,
`m_j·(1−z_j) = 0`, `w_j·(1−z_j) = 0`) and the borrow product
`borrow_{i+1}·(1−z_{i+1}) = borrow_{i+2}`, ending `borrow_25 = 0`. Variables:
`mzvar j = if j=0 then 36269 else 36273 + 5(j−1)`, `mwvar j = mzvar j − 1`,
`mnxt i = 36276 + 5i`, `mbLC j = 1 − z_j`, `mborrow 0 = 1`, `mborrow 1 = mbLC 0`,
`mborrow (i+2) = mnxt i`. The 100 row-shape facts (`mE1/mE2/mE3_j`, `mP_i`, `mF`)
are `decide +kernel` on `growAt (9813 + i)`; the names are prefixed (`mzvar` not
`zvar`) because `SigLt.lean` already has the byte-path names in the same namespace.
`lake build` is 3,377 jobs; AxiomCheck 4,372 theorems. Next: the `hout_i` plugs, then
`SigLt3`-style `hrec/hnb/outVal` + `SigLt4.telescope` for `val (limb s37 σ 25) =
n_val − 1`.

### The words minus_one plugs and the generic is_zero (2026-11, round 18)

`MinusOneFacts.lean` now imports `SigLt` (for `addLC`/`negLC`/`smulLC`/`ZLC.toF`) and
adds the 25 `mhout_i` facts: the `require_lt` call (s37) reads its `m` argument
(`plugs[25+i]`) as the first square's `m` plugs (`wcallAt 40`, `plugs[25+i]`, the
converted n limbs) minus `mborrow i` plus `W·mborrow (i+1)` — all `decide +kernel`.
Also `isZero_iff` (generic): from `n·w = z` and `n·(1−z) = 0`, `n = 0 ↔ 1−z = 1`.
The byte stack's per-limb algebra (`SigLt3`'s `E1/E2/E3`/`P`/`houtE`/`hnb`/`hrec`/
`outVal`, `SigLt4.telescope`) is generic in the row equations, so the words version is:
the `mE*` row shapes (done), the `mE1q`/`mE2q`/`mPq` equations and `mhoutE_i`, then
`val_formula`/`telescope` with `mborrow 0 = 1`, `mborrow 25 = 0`. `lake build` is
3,377 jobs; AxiomCheck 4,398 theorems.
