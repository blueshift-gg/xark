# LSP Inline Diagnostics for xark

Two-phase plan to surface constraint-cost data and circuit diagnostics inline in editors.

## Current State

| Tool | What | Editor-Integrated? |
|------|------|--------------------|
| `xark check` | Subset validation — every disallowed Rust pattern with `file:line:col` span | ✅ via `rust-analyzer.check.overrideCommand` |
| `xark profile` | Per-constraint attribution: source line, function chain, kind (Mul, Booleanity, RangeCheck, …) | ❌ CLI-only (tree or JSON) |
| `xark check --inputs` | Under-constrained variable soundness check | ❌ CLI-only |
| `xark inspect` | Circuit stats | ❌ CLI-only |

---

## Phase 1 — Profile data as LSP diagnostics via `xark check --profile`

**Goal**: Constraint-cost annotations appear inline in *any* LSP editor (VS Code,
Zed, Neovim, Helix, …) with zero extension install. Achieved by extending
`xark check` to emit constraint counts as `INFORMATION`-severity diagnostics
through the existing rustc diagnostic pipeline.

### How it works

1. `xark check --profile <crate-dir>` runs the full `cargo check` with MIR
   extraction **and** constraint profile attribution, injecting BOTH
   ERROR/WARNING diagnostics (subset rejections) AND INFORMATION diagnostics
   (per-line constraint counts) through rustc's `DiagCtxt`.

2. The editor's rust-analyzer is pointed at this command:
   ```toml
   # rust-analyzer.toml
   [check]
   overrideCommand = ["xark", "check", ".", "--message-format=json", "--profile"]
   ```

3. Rust-analyzer surfaces the INFO diagnostics as green/blue "hints" inline —
   no extension required.

### Tasks

- [x] **1a.** Add `--profile` flag to `xark check` (CLI plumbing).
  - `crates/xark-cli/src/commands/mod.rs`: add `profile` field to `CheckArgs`, pass through `to_argv()`.

- [x] **1b.** Thread the `--profile` flag through `cmd_check` → `RUSTFLAGS` as
  `--check --profile`. Also set `XARK_OUT` so the driver knows where to write
  `profile.json`.
  - `crates/xark-cli/src/cli.rs`: parse `--profile` from args, resolve output dir,
    set `XARK_OUT` env, append to `RUSTFLAGS`.

- [x] **1c.** In the rustc driver, when `--check --profile` is present, write
  `profile.json` to `target/xark/<pkg>/profile.json`.
  - `crates/xark-rustc/src/main.rs`: removed the `!check_here` guard on profile.
  - `crates/xark-rustc/src/driver.rs`: added `write_profile_only()` method that
    writes `profile.json` when `check_only && profile` and `XARK_OUT` is set.

- [x] **1d.** Investigated LSP severity options. **Conclusion: cannot emit
  Information-level hints through the `cargo check → rust-analyzer` pipeline.**
  rust-analyzer maps ALL rustc diagnostic levels (`error`, `warning`, `note`,
  `help`) to LSP Warning at minimum. There is no way to get Information/Hint
  severity. Inline rendering is deferred to Phase 2 (VS Code extension).

- [ ] **1e.** Test with the VS Code extension (Phase 2): verify the extension
  reads `profile.json` and renders constraint-cost hints with Information severity.

- [x] **1f.** Update `xark init` scaffold to include `--profile` in the
  `overrideCommand` by default.
  - `crates/xark-cli/src/cli.rs`: changed `ra_cmd` to include `--profile`.

### Implementation notes

- **Design decision**: `--check --profile` writes `profile.json` to disk rather
  than emitting inline diagnostics through rustc. The rust-analyzer LSP pipeline
  cannot produce Information-severity hints; all diagnostics become Warning-level
  yellow squiggles. The profile data is available for direct consumption by the
  Phase 2 VS Code extension.
- **Output location**: `<crate>/target/xark/<pkg>/profile.json` — same path as
  `xark build --profile`, so both `xark check --profile` and `xark build --profile`
  write to the same location.

### Files touched

| Crate | File | Change |
|-------|------|--------|
| `xark-cli` | `src/commands/mod.rs` | `CheckArgs.profile` field + `to_argv` |
| `xark-cli` | `src/cli.rs` (`cmd_check`) | Parse `--profile`, thread to `RUSTFLAGS` |
| `xark-cli` | `src/cli.rs` (`cmd_init`) | Include `--profile` in scaffolded `ra_cmd` |
| `xark-rustc` | `src/main.rs` | Remove `!check_here` guard on profile |
| `xark-rustc` | `src/driver.rs` | Add `emit_profile_diagnostics()` + imports |

---

## Phase 2 — VS Code extension (`xark-vscode`)

**Goal**: Rich inline diagnostics (gutter annotations, CodeLens, status bar,
hover tooltips, one-click commands) for VS Code users. Lives in `clients/vscode/`
alongside the existing `clients/typescript/`.

### Features

1. **Gutter annotations**: Per-line constraint count rendered as an after-gutter
   decoration, similar to code-coverage overlays. Source = `profile.json`.

2. **CodeLens**: Above `pub fn circuit(..)` and gadget-call sites:
   "`45 constraints (30 Mul, 10 Booleanity, 5 RangeCheck)`"

3. **Status bar item**: Live total constraint count for the crate.

4. **Hover provider**: Hover over a line or a function call to see detailed
   constraint breakdown (function chain, per-kind counts).

5. **Commands**:
   - `xark: Build Circuit` — run `xark build`
   - `xark: Profile Circuit` — run `xark profile` and show inline
   - `xark: Generate Proof` — run `xark prove` with input prompts
   - `xark: Inspect Circuit` — show stats in a notification

6. **Auto-configuration**: On activation in a circuit crate, offer to write
   `rust-analyzer.toml` / `.vscode/settings.json` with the correct
   `overrideCommand` (including `--profile`).

7. **Problem matcher**: Terminal-based `xark check` output maps to the Problems
   panel (in addition to the inline diagnostics from Phase 1).

### Architecture

```
clients/vscode/
├── .vscodeignore
├── package.json          # extension manifest + contributes
├── tsconfig.json
├── src/
│   ├── extension.ts      # activate/deactivate, register providers
│   ├── profile.ts        # parse profile.json, aggregate, cache
│   ├── annotations.ts    # gutter decoration management
│   ├── codelens.ts       # CodeLensProvider impl
│   ├── hover.ts          # HoverProvider impl
│   ├── status.ts         # StatusBarItem
│   ├── commands.ts       # xark:* command implementations
│   └── config.ts         # rust-analyzer.toml / settings.json auto-config
└── test/
    └── smoke.ts
```

### Data flow

```
  xark build --profile
       │
       ▼
  profile.json  ←─── read by extension on file-save or command
       │
       ▼
  extension.ts:
    ├─ parse + aggregate (profile.ts)
    ├─ update gutter decorations (annotations.ts)
    ├─ update CodeLens (codelens.ts)
    └─ update status bar (status.ts)
```

### Tasks

- [x] **2a.** Scaffold extension package (`clients/vscode/`) with `package.json`,
  `tsconfig.json`, build scripts. Packaged as `xark-vscode-0.1.0.vsix`.
- [x] **2b.** Implement `profile.ts`: parse `profile.json`, aggregate by line,
  expose query functions for gutter/CodeLens/hover.
- [x] **2c.** Implement gutter annotations (`annotations.ts`):
  - On profile load, create `TextEditorDecorationType` with `after` content
    showing per-line constraint count.
  - Dimmed by total cost (more constraints = brighter text).
- [x] **2d.** Implement CodeLens (`ConstraintCodeLensProvider`):
  - Above `pub fn` / `fn` definitions, show total constraint count + kind breakdown.
  - Matches by function name from profile chain data.
- [ ] **2e.** Implement status bar (`status.ts`): ✅ done — shows total constraint
  count in the status bar with `$(graph)` icon.
- [x] **2f.** Implement hover (`ConstraintHoverProvider`):
  - On hover over a line with constraints, show detailed breakdown:
    per-kind table, function chains, source snippet.
- [x] **2g.** Implement commands (`commands.ts`):
  - `xark: Validate Circuit` → `xark check --profile`
  - `xark: Build Circuit` → `xark build`
  - `xark: Profile Circuit` → `xark profile --json`
  - `xark: Generate Proof` → `xark prove` (prompts for inputs)
  - `xark: Generate Keys` → `xark setup`
  - `xark: Inspect Circuit` → `xark inspect`
  - Output to a dedicated `xark` OutputChannel.
- [x] **2h.** Implement auto-config (`config.ts`):
  - `xark: Configure rust-analyzer` writes `rust-analyzer.toml` +
    `.vscode/settings.json` with the correct `overrideCommand`.
- [ ] **2i.** Add README, marketplace metadata, icon. (README stub done, icon needed)

### Files created

| Path | Purpose |
|------|---------|
| `clients/vscode/package.json` | Extension manifest |
| `clients/vscode/tsconfig.json` | TypeScript config |
| `clients/vscode/src/extension.ts` | Activation entry point |
| `clients/vscode/src/profile.ts` | Profile data parsing/aggregation |
| `clients/vscode/src/annotations.ts` | Gutter decoration management |
| `clients/vscode/src/codelens.ts` | CodeLens provider |
| `clients/vscode/src/hover.ts` | Hover provider |
| `clients/vscode/src/status.ts` | Status bar item |
| `clients/vscode/src/commands.ts` | Command implementations |
| `clients/vscode/src/config.ts` | Auto-config helpers |
| `clients/vscode/README.md` | Extension docs |
| `clients/vscode/.vscodeignore` | Packaging excludes |

---

## Non-Goals (for now)

- **Custom LSP server**: Too heavy; xark circuits are Rust, rust-analyzer +
  `xark check` already covers the "is this valid?" use case. Phase 1 extends
  this without a new server.
- **InlayHints for constraint kind per expression**: LSP InlayHint would be
  ideal for showing "• 1 Equality" after `assert_eq(..)` lines, but the
  resolution of span-to-expression is coarse (line-level). Defer until line-level
  gutter + CodeLens are solid.
- **WASM-based inline analysis**: The `xark-wasm` crate exists but the
  profile data requires a full `xark build` run anyway. Phase 2 extension reads
  the profile.json produced by the CLI rather than running its own analysis.

---

## Success Criteria

### Phase 1
- [ ] `xark check --profile examples/cube` produces valid `--message-format=json` output
  with INFO diagnostics for constraint-cost lines
- [ ] rust-analyzer surfaces those diagnostics as inline hints in VS Code
- [ ] Zero user-visible regression: `xark check` without `--profile` is unchanged

### Phase 2
- [ ] `xark-vscode` extension installs from local `.vsix`
- [ ] Gutter shows per-line constraint counts for a built circuit
- [ ] CodeLens shows function-level totals
- [ ] Status bar shows crate-level total
- [ ] Commands run successfully (`xark: Build`, `xark: Profile`)
- [ ] Auto-config writes correct `rust-analyzer.toml`
