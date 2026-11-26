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

Proven and exported (`lean-export --check` is green on 69 templates):

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
| `Consts` obligation for LC plugs | `Templates/Consts/GroupedColumnStep.lean` (`soundness_free`) | needed because `grouped_columns` calls the step with LC plugs |

Coverage on `examples/rsa2048`: 408/408 `grouped_column_step`, 17/17
`range_check_q`, 16/16 `range_check_r` calls, no allowlist entries. Digests
pinned (`rsa2048 68ef4df3… 98b4c751…` under the keyed rustc; run
`rustup toolchain install 1.99.1` then `rustup run 1.99.1 cargo xtask digests
--check` — the workspace rustc also passes, with a different *keyed* digest).

Model-level theorems now cover every named step except the EM vector
(`sha256_em_bits_82`'s constant prefix plus the digest's bits). Still hand-proved
(the remaining gap, in order):

1. The bridge from `grouped_columns`' actual rows to the `GroupedColumns` model:
   the per-row `CarrySpec` instance. `GroupedColumnStep.Spec` is only the
   range bound; the affine `k = num·2^-164` is the template's output expression.
   `Formal/GroupedColumns.lean` gives the telescope; composing the 24 step calls
   plus the top row into `CarrySpec` is the missing glue theorem.
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
`lean-export --example rsa2048` viable: **9.2 MB, 36 parts, 125,856 rows, 1,021
segments**, hash-gated in `CircuitHash.lean`. The affine-carry design would have
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
  `AxiomCheck.lean` must print "standard axioms only" (69 harnesses).

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

What is left is the **row-level model of the `grouped_columns` template** (704 KB, 3,435
rows = 1,250 products + 24 × 91 step rows + 1 top row): its `rows_eq` by `decide +kernel`
with products at `base + 2(i·25+k)`, then the assembly above. Marking the function as a
`#[gadget]` and exporting the harness is already measured to work; the marker cannot land
until the proof imports `Formal.Templates.GroupedColumns` (the exporter enforces it). After
that, re-export the circuit: 17 top-level calls, and the composition is 17 `sat_call`s
with the q/r `Spec`s supplying the limb bounds.

The work is a single large proof plus mechanical instantiation, not an open design
question; every number it needs is in this file.
