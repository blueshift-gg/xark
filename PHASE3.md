# Phase 3 — Deep Circuit Diagnostics

Three tiers of additional LSP/VS Code diagnostics beyond constraint costs.

---

## Tier 1 — Gadget-Call CodeLens + Hint Warnings

Uses existing `profile.json` data — no new artifacts needed.

### 3a. Gadget-Call CodeLens

**What**: Above each gadget call site (e.g. `keccak::permute(state)`), show the
total constraint cost contributed by that call and its descendants.

**How it works**:
- The `chain` field in `ConstraintProfile` captures caller→callee chains, e.g.
  `["circuit", "keccak::permute", "keccak::theta"]`.
- Aggregate constraints by the **first non-circuit function** in each chain
  (i.e. the gadget entry point).
- CodeLens above calls like `keccak::permute(state)` → `permute → 156,672c`.

**Files to change**:
- `clients/vscode/src/extension.ts` — extend `ConstraintCodeLensProvider` to
  also match gadget call expressions (not just `fn` definitions). Use a regex
  like `(\w+::)?(\w+)\(` to find call sites, then cross-reference with chain
  data.
- `clients/vscode/src/profile.ts` — add `gadgetCosts(summary)` that groups by
  top-level chain entry, returning `Map<string, { total, kinds }>`.

### 3b. Hint-Usage Annotations

**What**: Lines that produce `HintPin` constraints get a distinctive gutter marker
(⚡ or similar) and the hover warns that unpinned hints are a soundness risk.

**How it works**:
- `kind: HintPin` is already in profile.json.
- In the gutter annotation, when a line has HintPin constraints, prepend a
  distinctive marker (e.g. `⚡ 5c (3 HintPin, 2 Mul)`).
- In the hover, add a note: "💡 Hint constraints — ensure this value is pinned by
  an `assert_eq` or it will be under-constrained."
- In the status bar, show total hint count.

**Files to change**:
- `clients/vscode/src/annotations.ts` — detect HintPin in `line.kinds`, change
  gutter prefix.
- `clients/vscode/src/extension.ts` — update `ConstraintHoverProvider` to add
  hint warning text.
- `clients/vscode/src/status.ts` — show hint count in tooltip.

---

## Tier 2 — Private/Public InlayHints + Under-Constrained Detection

### 3c. Private/Public InlayHints

**What**: Show `🔒 Private` / `🌐 Public` after function parameter names,
matching the circuit's declared visibility.

**How it works**:
- `xark check --profile` already writes metadata. We need the variable table
  (names, roles, visibilities) which is part of `circuit.xbc`.
- Option A: Parse `circuit.xbc` in the VS Code extension via WASM (`xark-wasm`'s
  `circuit_inputs()` already returns `[{"name":"…","role":"public"|"private"}, …]`).
- Option B: Add a new `metadata.json` to the `--profile` output that includes
  the variable table in plain JSON (simpler, avoids WASM dependency).
- Register an `InlayHintsProvider` for Rust files that reads the metadata and
  inserts hints after parameter patterns that match circuit input names.

**New artifact**: `target/xark/<pkg>/metadata.json` containing:
```json
{
  "entry_fn": "circuit",
  "field": "bn254",
  "inputs": [
    { "name": "secret", "role": "private" },
    { "name": "result", "role": "public" }
  ],
  "num_vars": 5,
  "num_constraints": 2,
  "num_witness_ops": 1
}
```

**Files to change**:
- `crates/xark-rustc/src/driver.rs` — in `write_profile_only`, also write
  `metadata.json` with the variable table and circuit stats.
- `clients/vscode/src/profile.ts` — add `CircuitMetadata` type and loading.
- `clients/vscode/src/extension.ts` — register `InlayHintsProvider`.

### 3d. Under-Constrained Variable Detection

**What**: When `xark check --inputs` is run, surface any under-constrained
variables as **Error** diagnostics at their declaration/use site.

**How it works**:
- Add a new command `xark: Soundness Check` that prompts for inputs (like
  `xark: Generate Proof`) and runs `xark check --inputs`.
- Parse the output for under-constrained variable messages.
- Map them to source locations and create LSP Error diagnostics via a
  DiagnosticCollection.

**Files to change**:
- `clients/vscode/src/commands.ts` — add `cmdSoundnessCheck` command.
- `clients/vscode/src/extension.ts` — create a `DiagnosticCollection` for
  soundness findings, parse `xark check --inputs` output.

---

## Tier 3 — Dead Code + Status Bar Drill-Down

### 3e. Dead Circuit Code Detection

**What**: Functions that produce zero constraints get a subtle "0 constraints"
CodeLens, helping authors identify code that isn't wired into the circuit.

**How it works**:
- After loading profile.json, find all `pub fn` / `fn` definitions in the source
  file that have no constraints attributed to them (no chain entries matching).
- Show a dimmed `0 constraints` CodeLens above those functions.

**Files to change**:
- `clients/vscode/src/extension.ts` — extend `ConstraintCodeLensProvider` to
  emit zero-count lenses for functions not in the profile.

### 3f. Status Bar Drill-Down

**What**: Clicking the status bar constraint count shows a rich hover with
circuit statistics.

**How it works**:
- Use the status bar item's `command` to trigger a hover/notification showing:
  - Total constraints
  - Variable breakdown (public/private/derived)
  - Witness-gen op count
  - Field name
  - Circuit hash (first 8 hex chars)
- Data comes from `metadata.json` (from 3c).

**Files to change**:
- `clients/vscode/src/status.ts` — add click handler that shows a QuickPick or
  notification with stats.

---

## Implementation Order

1. **3a** — Gadget-call CodeLens (pure TypeScript, leverages existing profile.json)
2. **3b** — Hint-usage annotations (pure TypeScript)
3. **3c** — Private/Public InlayHints (needs new `metadata.json` artifact)
4. **3d** — Under-constrained detection (needs new command + output parsing)
5. **3e** — Dead circuit code CodeLens (pure TypeScript)
6. **3f** — Status bar drill-down (needs `metadata.json` from 3c)

---

## Success Criteria

### Tier 1
- [x] Gadget calls show constraint costs in CodeLens (e.g. `permute → 156,672c`)
- [x] Lines with hints show ⚡ marker in gutter annotations
- [x] Hover on hint lines shows soundness warning

### Tier 2
- [~] ~~`secret: Field` shows `🔒 private` as inlay hint~~ — **Dropped**. `Private<Field>` /
  `Public<Field>` types already encode visibility. Redundant with the type system.
- [~] ~~`result: Field` shows `🌐 public` as inlay hint~~ — same as above.
- [ ] `xark: Soundness Check` finds and reports under-constrained variables as errors.
  Requires witness inputs from user → needs CLI invocation, not compile-time analysis.
  Best delivered as a VS Code command that prompts for inputs and parses output.

### Tier 3
- [x] Functions with zero constraints show `⊘ 0 constraints` CodeLens
- [x] Clicking status bar shows circuit overview (vars, constraints, field, hash)
