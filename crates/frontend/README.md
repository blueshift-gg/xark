# xark-frontend

xark's frontend: compiles a circuit with any stable `rustc` (1.89+) and lowers it to
the `circuit.xbc` the prover reads.

```bash
xark build examples/sha256
```

## How it works

1. `cargo rustc` builds the circuit crate for `wasm32-unknown-unknown` with `--cfg xark`
   (installing the target with `rustup` on first use). In that build every circuit
   operation — `Field` arithmetic, comparisons, hints, `require_eq`, input binding — is a
   call to an `xark.*` wasm import (`crates/lang/src/wasm.rs`). Imports are opaque to
   rustc/LLVM, so optimization can't drop, duplicate or reorder them, and every witness
   value only exists inside them.
2. The frontend runs the module (`interp.rs`) with the imports implemented as the circuit
   builder (`host.rs`, `builder.rs`). Concrete values (constants, loop counters,
   indices) simply execute; that *is* the unrolling, const-evaluation and inlining.
3. Values derived from a witness that aren't `Field`s — comparison `bool`s and native
   `uN` inputs — are symbolic. A branch on one runs both arms and merges what differs into
   selects (muxes); an arm that can only panic is pinned impossible instead (so `assert!`
   and checked `uN` arithmetic become constraints). Native integer ops on witnesses lower
   to range-checked gadgets.
4. After lowering, repeated wasm call bodies are found post hoc and encoded once as
   templates (`templates.rs`) — compression only; the circuit is the flat one.
   Templates nest: a def's body is its first call's rows, with its own repeated
   sub-calls as calls. `circuit.xbc` is written as container version 2 (pooled
   constants, delta-coded vars and plugs, back-references to repeated LCs; see
   `output.rs`). The `XARK_VERIFY`-style check (`verify_blob_matches`) confirms the
   artifact expands to it.

`#[circuit]` generates the module's `__xark_main` export (input binding + call) and its
`xark.entry` name section; `schema.json` is rebuilt from the input bindings.

## Semantics

Everything is inlined, so a circuit is the same no matter how rustc/LLVM inline or
schedule it. Compared with the removed MIR frontend (`xark-rustc`), whose circuits it
replaces:

* **Large linear combinations stay inline** in multiplication rows (the MIR frontend
  named any operand over 8 terms with an extra constraint). Fewer constraints: Poseidon
  400 → 238, Pedersen 5575 → 3340.
* **Repeated products are reused**: a second `A · B` of an existing row `A · B = x`
  returns `x` (the row is re-checked to be literally that). SHA-256's `Maj` reuses
  the previous round's `a ∧ b` (−1952 rows); a 3-limb square's cross terms (−9).
* **Powers of constants are folded** (`rc⁵` on Poseidon's constant capacity lane: −3).
* **Constants are reduced mod p** (to the symmetric range), so folded round constants
  don't grow to thousands of bits (Poseidon's `circuit.xbc`: 6.3 MB → 0.44 MB).
* `usize` is 32-bit (wasm32); gadgets must not shift a `usize` by ≥ 32.
* More Rust is accepted: `+=` on `Field`, iterator adapters over constant ranges, `as`
  narrowing casts (truncating), `assert!` on witness `bool`s (a constraint), and on
  witness `uN`: `/` and `%` by anything (hinted `q`, `r` pinned by `a = q·b + r`,
  `r < b`), signed comparisons, sign extension and arithmetic shifts (LLVM emits these
  for unsigned code too), and branches on "is it nonzero".
* `==` pins its inverse advice (`inv · out = 0`, one row), so an equal pair leaves no
  free variable for the under-constraint gate `xark prove` runs (both frontends).

### Panics become constraints

A witness branch whose arm can only panic (`assert!`, overflow and bounds checks,
`/ 0`) is impossible for a valid witness, so the frontend requires the other arm.
Each arm is first *probed*: run concretely — following it past the branch's rejoin
point, through nested witness branches (a path panics if both ways on do) — until it
panics, calls an import other than `panic`, or exhausts a small step budget. A path
that reaches a panic without touching witness data can't be taken by any valid
witness, wherever the panic sits. When both arms panic, the branch point itself is
unreachable.

Both arms of any other witness branch run unconditionally and their results are
muxed. What an arm emits comes in three kinds:

* *Total* ones — every input satisfies them (products, `==`, `<` on known-width
  integers, bit decompositions of known width) — are emitted as they are: an untaken
  arm's outputs are simply never selected.
* *Requirements* — `assert!`, checked arithmetic, `require_eq`, the equalities of an
  integer division, `Field` range proofs (`to_bits`, `lt`), `x · inv = 1` — are
  emitted *guarded*: `g · (a − b) = 0`, where `g` is the `{0,1}` conjunction of the
  enclosing arms' conditions (one product per nesting level). They bind exactly when
  the arm is taken and are vacuous otherwise.
* *Hints* in an arm read `g · x` instead of `x` and are pinned by `(1 − g) · h = 0`;
  a range proof's bits recompose to `g · value`. Where the arm isn't taken every hint
  sees `0` (so an untaken `inv` of 0, `to_bits` of an out-of-range value or division
  by 0 still solves) and is forced to `0`, so every variable stays determined by the
  inputs — what `xark prove`'s under-constraint gate checks. A division's hint divides
  by `b + 1 − g`.

The Lean side is `gated_sat`, `guard_mul`, `pin_dead` and `select_taken` in
`formal/Formal/Rewrites.lean`. The gadget hints work the same way: `div_rem` divides
`g · num` by `g · den + 1 − g`, and the bignum hints (mulmod, mod-inverse, sub2) see
gated limbs with a modulus of `1 − g` (`2 − 2g` for the inverse, whose untaken output
`1⁻¹ mod 2 = 1` is pinned to 1). `advice` in an arm is pinned to `0` where it isn't
taken. A `to_bits` of a constant that doesn't fit makes its arm unreachable, like a
panic. (A division by a *select* is muxed first, never distributed over the select's
arms.) If an arm turns out to panic only
once both arms are run on to their rejoin point, the other arm is pinned as taken, as
for a probed panic.

A `match` on a witness integer (a wasm `br_table`) runs as a chain of `c == k`
branches. A load at a witness-dependent address `base + o` is a select over every
possible address when `o` provably takes at most 1024 values: a sum of pinned-boolean
and known-width (≤ 20-bit) variables with any signed coefficients (a narrow index,
`x & 7`, `!x & 7 = 7 − Σ bits`, `x as u8`, OR/XOR bits — LLVM's lookup tables for
`match` too), enumerated as every subset sum or the grid of its range. Candidates
are allowed to over-approximate (an impossible one is never selected); an
out-of-bounds one is ruled out (it would trap). A store `t[i] = v` through such an
address writes `i == o ? v : old` to every candidate slot, and a store through a
select of such pointers does the same over the union of their addresses. An index
bounded only by an earlier check (LLVM rewrites `x & 7` to `x` once `1 − x` is known
not to underflow) is bounded by that check: an unsigned comparison of a variable with
a constant that is required outside any witness branch records the bound it proves,
which also lets a provably small 64-bit value skip truncation. Shifts by a witness amount use
`2^k = Π (1 + (2^2^i − 1)·kᵢ)`.

### Witness-only regions

Between `witness_begin()` and `witness_end()` nothing is constrained: values are computed
for the witness only, and requirements are dropped. Nothing computed there counts as
proven afterwards — the bit-decomposition cache, select and product reuse, the set of
proven booleans and the bounds learned from comparisons are only fed by emitted rows — so
redoing an operation after the region constrains it again.

### Native-semantics fuzzing

`crates/lang/tests/semantics_fuzz.rs` generates random programs over witness `uN`
(every arithmetic, bit, shift, wrapping and narrowing op, selects, `assert!`, `match`
on a witness byte, loads and stores at a witness index, loops whose bodies branch on
witness bits, nested witness `if`s whose arms compute — and may panic — or `assert!`,
and `inv` / `to_bits` / `lt` in witness arms), evaluates them with Rust's
overflow-checked semantics, and decides every input with an **exhaustive witness
search** (`xark_ir::witness_search`): with the inputs fixed, a constraint-propagation
solver with complete case splitting enumerates *all* satisfying assignments — the
adversary, not the honest hint program. The circuit must have exactly one witness for
Rust's result, none for result + 1, and none for any output where Rust panics; the
honest solver must find that witness too. Over 3,000 programs / 48,000 searches have
run clean with none undecided (`XARK_FUZZ_CASES`, `XARK_FUZZ_SEED`; CI runs 200 per
push and 5,000 weekly on a fresh seed). `cargo xtask difftest` runs the same
search on every example under 200k rows, on its own test inputs and mutations; all
are decided except the non-native EC examples (`ec_incomplete*`), whose 256-bit
modular-inverse relations the search can't reason about. Those gadgets are checked at
small scale instead: the same `weierstrass!` code over 3 × 2- and 3-bit limbs (p = 13,
127) has every input decided — the right output, no witness where the formula is
undefined, every non-canonical encoding rejected at `enforce_on_curve` — and its gate
count is exactly affine in the limb width up to 86 bits, where it is the shipped
secp256k1 circuit digest-for-digest (`small_field_curve_gadgets_are_sound`,
`scaled_curve_gadget_rows_match_secp256k1`).

Mutation testing (each guard, pin and gated range check removed in turn; see the
plan) is caught by these tests, except a handful that only a specific shape reaches —
those shapes are regression tests in `snapshot.rs` (`pruned_arms_constrain_the_condition`,
`conditional_*`). About 0.3% of fuzz programs are still refused with a diagnostic
(beyond ones that always panic): a loop whose exit LLVM made witness-dependent, and the
odd store whose index the frontend can't bound. A comparison the operands' proven bounds
already decide is folded to a constant, so a loop over `0..n` with `n` a narrow witness
(`x & 3`) unrolls; one whose witness branches keep nesting (an unbounded witness length)
is refused after 48 levels.

**Soundness of the reductions.** The lowering differed from the MIR one only by those
four rules (the switches are `mat_threshold`, `cse`, `reduce` and the `pow` fold; when
both frontends existed, turning them off made every example's circuit identical to the
MIR frontend's flat build), and each is an exact rewrite, proven in Lean in
`formal/Formal/Rewrites.lean`: `cse_sound`, `inline_sound`, `fold_sound` /
`const_mul_sound` (built on `elim_sound`) show the rewritten rows' solutions are
exactly the original's with the dropped variable forgotten — nothing new for a
forger, nothing lost for an honest prover; mod-`p` reduction is the identity in
`ZMod p`. The Lean bridge tests (`crates/lang/tests/snapshot.rs`) pin the gate counts
and name the rewrite behind each difference from the models. Diagnostics: `XARK_NO_CSE`,
`XARK_NO_POWFOLD`, `XARK_NO_REDUCE`, `XARK_MAT_THRESHOLD=<n>`, `XARK_CSE_LOG`.

## Source locations (`xark profile`, `xark check`)

Every build (`build`, `profile`, `check`, `test`) carries DWARF line tables. While lowering, each
emitted constraint records the wasm call stack it came from (`(function, pc)` per frame,
interned; only when profiling), and a lowering error records where execution stopped.
`debuginfo.rs` maps those through `addr2line` — inlined frames included — to the line in
the `#[circuit]` fn plus the chain of functions below it, down to the `xark` API call
(arithmetic operator impls elided).
`xark check` reports a rejection as a rustc-style diagnostic at the innermost user line
(a cargo `compiler-message` with `--message-format=json`, for rust-analyzer). A module
without line tables (`BuildOptions { line_tables: false, .. }`) gets errors naming the
wasm functions instead.

## Dev tool

```bash
cargo run -p xark-frontend --release --example stablec -- examples/ed25519 \
    [--compare other/circuit.xbc] [--out circuit.xbc]   # digest, sizes, timing; faithfulness check
XARK_FRONTEND_TIME=1 …                     # phase timings
cargo test --release --test snapshot                 # (in crates/lang) the snapshot suite
cargo run -p xark-frontend --release --example xbcstat -- a.xbc b.xbc   # sizes
cargo xtask difftest                                 # examples' inputs, adversarially
```
