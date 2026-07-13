# DAG functions & the JIT prover

This document describes how xark compiles a circuit whose functions are treated
as **reusable functions**, stores it as a **DAG-compact bytecode artifact**
(templates + call sites, not a flat constraint stream), and **expands it on
demand** at setup/prove time — the "JIT prover" model. It covers the end-to-end
pipeline, the version-1 bytecode format byte-for-byte, the
bytecode- and R1CS-layer optimizations, and how soundness is preserved and
checked at every hop.

## Why

A circuit like an ed25519 scalar multiplication is ~7.4M constraints, but it is
built from a handful of functions (`ec_double`, `ec_add`, field mul, …) invoked
hundreds of times. Encoding the *flat* expansion is wasteful on two axes:

- **Build time.** Function structure is captured *for free* during lowering (no
  separate ~30s periodic-run pass). Loops of *primitives* — which a plain function
  capture wouldn't compress — are still handled: the container also folds periodic
  runs of inline rows into `REPEAT` items (the same affine detection the old loop
  encoding used, now embedded in the one format).
- **Artifact size.** Flat ed25519 is ~99MB; the DAG-compact form is ~1.1MB
  (≈90×). ecdsa 33MB→2.4MB, keccak 2.7MB→0.8MB.

The DAG artifact stores each distinct function body **once** and records each call
site as a small `(def, base, plugs)` record. Expansion replays the bodies with
variable remapping to reproduce the exact flat circuit.

## Pipeline

```
Rust source
  │  rustc frontend (parse / type-check / borrow-check / MIR)
  ▼
lower_mir::lower          MIR → circuit IR
  │   • a function that is all-Field and not #[inline(never)] is a FUNCTION
  │   • first call: WALK the body, capture a template (constraints + witness +
  │     plug/var kinds); later calls: REPLAY the template with vars remapped
  ▼
LowerOutput { r1cs, primitive, function_xbc }
  │   • function_xbc = build_function_blob(env)  (built for EVERY circuit — the sole format)
  ▼
driver::emit_outputs      writes circuit.xbc = function_xbc
  │   • XARK_VERIFY: decode(function_xbc) ≡ from_lowered(r1cs, primitive), else abort
  ▼
circuit.xbc  (version 1, self-describing: defs + top-level Row/Call/Repeat items)
  │
  ▼   setup / prove
function_decode::expand_function_blob → CircuitProgram
  │   • constraints + witness program + variable table, byte-identical to flat
  ▼
minimize  boundary pass (default) · XARK_FLAT_MINIMIZE (guarded flat) · XARK_NO_MINIMIZE
  ▼
Groth16 (arkworks, BN254)
```

`circuit.xbc` carries both consumer views: `to_r1cs()` for the Groth16 backend and
`to_primitive()` for the witness solver, so nothing downstream needs to know the
circuit was function-encoded.

## Function capture & replay

A **function** is a function whose signature is entirely `Field`-typed and which is
*not* `#[inline(never)]` (operators `+ - * neg` are `#[inline(never)]`, so they
always inline as free linear ops). Detection is cached per `DefId`.

On a function call with all-`Field` args:

1. **Materialize plugs.** Each argument leaf is forced to a single variable (a
   *plug*). Aliased plugs (the same var in two positions) are copied to distinct
   vars so the var→var replay remap can't collapse them.
2. **First call — walk & capture.** The body is lowered normally, but inside a
   function body cross-call caches (bit-decomposition memo, mul→assert_eq merge)
   are suppressed so the body is a *pure function of its plugs*. The emitted
   constraints, witness ops, plug vars, and per-var visibilities are captured as
   a `FunctionTemplate`, keyed by `def_id | substs | plug-arity`.
3. **Later calls — replay.** The template is re-emitted with variables remapped:
   an internal var `v ≥ base_var` maps to `call_base + (v − base_var)`; a plug maps
   to the caller's plug var. Replay is byte-identical to a fresh walk (see
   *Soundness*), so it's a sound, much cheaper substitute.

Recursive functions (a function calling functions) form the DAG.

### `#[inline(never)]` — the compactness opt-out (and why lang keeps it)

`#[inline(never)]` plays two distinct roles that are easy to conflate:

- **On the lang primitives** (the operator impls, `__xark_*`, `constrain_eq`,
  `assert_eq`, `Field::constant`) it is a *recognition anchor*: it guarantees
  rustc emits them as distinct MIR calls that `classify_call` matches by `DefId`,
  rather than inlining the `loop {}` marker bodies away. These are handled as
  `KnownCall`s and lowered *directly* — recognition runs before `is_function`, so
  they are never walked or functionized regardless. This must stay; it is what makes
  recognition robust instead of dependent on rustc's default MIR inlining.

- **On a user circuit function** it is the *compactness opt-out*. `is_function`
  requires `!inline_never`, so marking a helper `#[inline(never)]` excludes it from
  caching: it is walked/spliced inline instead of stored as a reusable
  template. This is *bytecode-only* — the proven R1CS is byte-identical either way
  (checked by `XARK_VERIFY`), so it trades artifact compactness, not circuit cost.
  With the prune/inline post-pass already inlining single-use functions
  automatically, the opt-out matters mainly to force a *multi-use* function to stay
  inline (e.g. to read the flat form). See `examples/optout`.

## The version-1 bytecode format

The `XBC1` container magic + a `u16` version (`1`); `is_function_artifact` checks it
so a stale/foreign file is rejected. This is the **sole** format — it captures
function defs, records call sites, and rolls periodic runs of inline rows, so the
earlier flat / loop / function encodings (versions 6/7/8) were collapsed into it.

### Primitives

- **`uv`** — LEB128 unsigned varint: 7 bits/byte, high bit = continuation.
- **`iv`** — zig-zag signed varint (`(v<<1) ^ (v>>63)`), read back as `uv`.
- **`fc`** (field constant) — `0x00` + `iv` for an `i64`-representable value, else
  `0x01` + `uv(len)` + decimal-string bytes.
- **`str`** — `uv(len)` + UTF-8 bytes.
- **`lc`** (linear combination) — `fc(constant)` + `uv(nterms)` + `nterms ×
  [fc(coeff) + uv(var)]`.
- **`ids`** — `uv(len)` + `len × uv(id)`.
- **`vis`** — one byte: `0` Public, `1` Private, `2` Internal.

### Container layout

```
"XBC1"                         4 bytes magic
u16  version = 1               little-endian
str  field.name                e.g. "bn254"
str  field.modulus_decimal     "" if unknown
uv   num_vars                  total variable count (before prune)
uv   num_inputs                signature inputs occupy ids 0..num_inputs
     num_inputs × { vis; str name }     input role + name (matched at prove time)
uv   n_defs                    kept function defs (see prune/inline below)
     n_defs × FUNCTION_DEF
     CITEMS  (top-level constraint stream)
     WITEMS  (top-level witness stream)
ids  keep_extra                unreferenced-advice var ids the decoder must keep
```

`FUNCTION_DEF`:
```
uv   base_var                  the def's internal-var base (for remap)
ids  plugs                     the def's plug vars (its inputs)
CITEMS                         the def body's constraint stream
WITEMS                         the def body's witness stream
```

`CITEMS` — `uv(count)` then `count` items, each:
- `0x00` + `lc a` + `lc b` + `lc c` — a `Row`: one R1CS constraint `a·b = c`.
- `0x01` + `uv(def)` + `uv(base)` + `ids(plugs)` — a `Call` to def `def`, whose
  body is expanded at `base` with `plugs`.
- `0x02` + `uv(len)` + `len` bytes — a `Rolled` run: a maximal run of ≥2 consecutive
  inline rows, compressed with the affine periodic-run detector (loops of
  primitives) and decoded back to the exact rows.

`WITEMS` — `uv(count)` then `count` items, each:
- `0x00` + `WITNESS_OP` — a `Row`: one witness-generation op.
- `0x01` + `uv(def)` + `uv(base)` + `ids(plugs)` — the same `Call` shape.
- `0x02` + `uv(len)` + `len` bytes — a `Rolled` run of ≥2 witness ops (same form).

`WITNESS_OP` — a tag byte selecting the `WitnessGen` variant, then its fields
(each `out`/id as `uv`, each linear combination as `lc`, id-vectors as `ids`,
lc-vectors as `uv(len)+lc…`):

| tag | op | fields |
|----|----|--------|
| 0 | `Product`       | out, a, b |
| 1 | `Linear`        | out, lc |
| 2 | `Xor`           | out, a, b |
| 3 | `Or`            | out, a, b |
| 4 | `Inverse`       | out, in |
| 5 | `InverseOrZero` | out, in |
| 6 | `Bit`           | out, in, index |
| 7 | `Bits`          | outs, in |
| 8 | `DivRem`        | q, r, num, den |
| 9 | `MulModDivMod`  | q, r, a, b, mod, limb_bits |
| 10| `ModInverse`    | out, a, mod, limb_bits |
| 11| `Sub2`          | qabs, r, a, b, c, mod, limb_bits |

## Bytecode optimization — prune / inline / keep

After the def/call streams are built, `build_function_blob` counts how many times
each def is **statically** `Call`ed and rewrites:

- **0 calls → prune.** A captured-but-dead def is dropped.
- **1 call → inline.** The single call is the def's own defining site (identity
  remap), so the def body is spliced in place and the def removed. Recursive: an
  inlined def's own calls are spliced/re-pointed too.
- **≥2 calls → keep.** Shared bodies stay as defs; calls are re-pointed to
  contiguous new indices.

This is the bytecode-layer optimum: the artifact stores **no def that isn't
reused**. It never changes the flat expansion (checked by `XARK_VERIFY`). Example
(ed25519): 19 captured defs → 11 kept, 7 inlined, 1 pruned.

## Decode & variable-table reconstruction

`expand_function_blob(bytes) → CircuitProgram`:

1. Parse the header, inputs, defs, top streams, `keep_extra`.
2. `expand_c` / `expand_w` walk the top streams; a `Call` recurses into the def
   with the sub-map `v ≥ def.base_var ↦ call_base + (v − def.base_var)`, `plug ↦
   caller plug`. This reproduces the flat constraint and witness streams.
3. **Roles are id-based, not visibility-based.** Ids `0..num_inputs` take the
   stored input role/name; every other var is `Derived` — *including* hint/advice
   vars, which carry `Visibility::Private` in lowering but are computed by the
   witness program, never supplied. (Getting this wrong makes the solver demand an
   input for an advice var.)
4. **Prune to match `finish`.** `finish` drops unreferenced `Internal` vars but
   keeps `Private`/advice ones. The decoder drops every unreferenced non-input var
   *except* the `keep_extra` set (the rare unreferenced advice), and drops witness
   ops whose output was dropped. Result is byte-identical to the flat lowering.

## R1CS minimization

Independent of the bytecode: a **linear-variable-elimination** pass on the
`a·b=c` R1CS (Gaussian elimination over the prime field, occurrence-indexed).
Every `Internal` var defined by a linear constraint — a materialized plug, a copy,
or a mul output later pinned by an equality — is substituted away to a fixpoint.
Because the eliminated var is a *function* of the survivors, satisfiability is
preserved exactly in both directions (soundness *and* completeness). It lands at
or below the inline baseline and is where "optimal R1CS" lives for a flat prover.

By **default** this runs as a *template-minimize + boundary pass*: each function
template body is minimized once (plugs/outputs pinned) during the reduced expand,
then one unguarded pass over the flattened result eliminates the remaining
cross-template plug materializations — reaching the same fixpoint as a full flat
minimize without ever materializing the full unreduced R1CS. `XARK_FLAT_MINIMIZE`
selects the guarded flat pass over the whole expansion instead (fill cap
`XARK_MAX_FILL`, default 32); `XARK_NO_MINIMIZE` skips it. `xark setup --cache`
persists the minimized R1CS (`r1cs.min.wcz`) so a later `xark prove` reloads it and
skips both the minimize and the structural `validate()`.

The cost model is vanilla Groth16, whose proving key / FFT domain is
`next_pow2(#constraints + #public)` — so the big win is crossing below a power of
two; the pk also scales with variable count, so elimination shrinks it even within
a bucket.

## Soundness — preserved and checked at every hop

- **Replay ≡ walk.** A replayed function is byte-identical to a fresh walk of the
  body (constraints sorted, `∧` unordered, notes are debug-only): mathematically
  the same R1CS. Verified canonically across the whole corpus.
- **Artifact ≡ flat.** `XARK_VERIFY` (build-time, opt-in / CI) decodes the
  artifact with the *independent* `function_decode` reimplementation and asserts it
  equals `from_lowered(r1cs, primitive)` — constraints, witness, and var roles.
  Any encode/decode divergence aborts the build with a precise diff, on that
  circuit, immediately.
- **Prune/inline ≡ identity** on the expansion, also under `XARK_VERIFY`.
- **Minimizer preserves satisfiability** by construction (Gaussian elimination),
  and end-to-end by producing verifying Groth16 proofs that reject wrong witnesses.
- **Under-constraint gate.** Independently, `finish` rejects any hint/advice or
  public var left unpinned by a constraint (a structural, label-independent check).

## Environment flags

Function detection + capture/replay and the version-1 artifact are **always on** —
every all-`Field` function is auto-cached from its MIR (there is no opt-out flag);
it is the sole codegen and the sole on-disk format. The remaining knobs are
developer-only (compiled in behind the `debug` feature) or CLI flags:

| flag | effect |
|------|--------|
| *(minimize default)* | boundary pass: eliminate cross-template plug vars on the per-template-reduced R1CS |
| `XARK_FLAT_MINIMIZE` | guarded flat minimize on the full expansion instead of the boundary pass |
| `XARK_NO_MINIMIZE` | skip R1CS minimization entirely |
| `XARK_MAX_FILL` | fill-in cap for the guarded flat minimize (default 32) |
| `xark setup --cache` / `xark prove --cache` | write/reuse `r1cs.min.wcz`, the minimized R1CS, so a later prove skips the minimize + validate |
| `XARK_VERIFY` | build-time faithfulness gate (artifact ≡ flat lowering); on for every test build |
| `XARK_BUILD_TIME` / `PROVE_TIME` | print per-phase build / prove timings |
