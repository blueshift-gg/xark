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
