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
