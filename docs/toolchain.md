# Toolchain: the nightly pin

xark's compiler driver (`crates/rustc`) is a `rustc_driver` — it links against rustc internals to run the
frontend and read MIR. That requires **nightly Rust** and the `rustc-dev` component; there is no
stable API for MIR access. This records what is pinned, why, its fragility, and how to bump it.

## What is pinned

The pin lives in **`crates/rustc/rust-toolchain.toml`** (not the repo root — the root workspace is
plain stable Rust):

```toml
[toolchain]
channel = "nightly-2026-05-03"
components = ["rustc-dev", "llvm-tools-preview"]
```

- The dated channel enables `#![feature(rustc_private)]` while keeping every install reproducible.
- `rustc-dev` — ships the `librustc_*` shared libraries the driver links against (`rustc_driver`,
  `rustc_interface`, `rustc_middle`, …).
- `llvm-tools-preview` — LLVM tools rustc-dev's runtime expects on `PATH`.

Only `xark-rustc` touches nightly; the `xark` CLI and circuit crates use stable Rust. See
`docs/architecture.md` → "How MIR is used").

## Why nightly

`crates/rustc` uses `rustc_private` to: run the frontend (`rustc_driver::Callbacks`,
`rustc_interface`); obtain the `TyCtxt` and pull the `#[circuit]` entry's MIR `Body` in `after_analysis`;
walk MIR (`rustc_middle::mir`) to validate the accepted subset and lower it; emit diagnostics with
source spans via `DiagCtxt`. Gadget crates are compiled with `-Zalways-encode-mir` (also nightly)
so their MIR is available for cross-crate inlining.

## Fragility

rustc's internal APIs are **unstable and drift across nightlies**. Bumps have historically broken:

- `TyCtxt` query signatures and `rustc_interface`/`rustc_driver` `Callbacks` method shapes (e.g.
  `after_analysis`'s arguments),
- MIR data structures in `rustc_middle::mir` (statement/rvalue/terminator variants, `Place`
  projections),
- the diagnostics API (`DiagCtxt`, `Diag` builder methods),
- `-Z` flag names and defaults.

The dated pin prevents `rustup update nightly` from silently changing the driver's ABI.
The driver remains outside the stable root workspace, and its snapshot suite is a separate CI job.

## Bump procedure

1. Update the dated pin in `crates/rustc/rust-toolchain.toml` and run
   `rustup toolchain install <nightly-YYYY-MM-DD> --profile minimal --component rust-src --component rustc-dev --component llvm-tools`.
2. Rebuild the compiler:
   ```bash
   cd crates/rustc && cargo build
   ```
   Fix any `rustc_private` API breaks (usually `TyCtxt` queries, MIR variants, or the
   `DiagCtxt`/`Callbacks` shapes — keep the churn behind the small wrappers in `crates/rustc/src`).
3. Run the compiler snapshot suite:
   ```bash
   cd crates/lang && cargo test --test snapshot
   ```
   The `xark-test-harness` builds every gadget crate with `-Zalways-encode-mir` into an isolated
   `target/xark-compile` and the compiler into `crates/rustc/target`, then diffs each example's
   emitted R1CS/IR against the committed snapshots (`crates/lang/tests/snapshots/`). If a gate count
   changed intentionally, refresh with `UPDATE_SNAPSHOTS=1` and re-check the Lean-model bridges.
4. Run the heavy known-answer vectors (they gate real hash/curve correctness):
   ```bash
   cd crates/lang && cargo test --test snapshot -- --include-ignored
   cargo test -p xark-ed25519 --release
   ```
   These also run daily in CI via `.github/workflows/nightly-kats.yml`.
