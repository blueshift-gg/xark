# Toolchains

xark needs **only stable Rust, 1.89 or newer**, both to install the CLI and to build
circuits (the workspace and `xark` crate `rust-version`). The circuit crate is compiled by the ambient
`cargo`/`rustc` for `wasm32-unknown-unknown` (added with `rustup` on first use), and
`crates/frontend` runs the module to lower it. Every circuit operation is an opaque
wasm import, so the constraint system doesn't depend on the compiler version:
`cargo xtask digests --check` rebuilds every example and compares its R1CS digest
with `tests/stable-digests.txt` (`--toolchain 1.89` builds the circuits with another
installed toolchain), and CI runs it on 1.89, stable and beta. It also builds the
`client.wasm` of each example with Rust client functions (`#[input]` on an `impl`),
which has to build on every supported rustc too.
(All 70 examples were identical on 1.88, 1.89, 1.93, 1.96, 1.98 and a 2026-10
nightly when this was introduced.) See `crates/frontend/README.md` for the design.

`build`, `check` (editor diagnostics, `--message-format=json` included), `profile`
and `test` all share one cache (`target/xark-wasm`). Builds carry DWARF line tables
(`debug = "line-tables-only"`) so constraints and rejections are attributed to source
lines; they don't change the circuit or the lowering time, and compile time is the
same within noise (only the `.wasm` grows).

Nothing in the repository needs nightly. (Earlier releases had a second frontend,
`xark-rustc`, that read MIR through `rustc_private` on a pinned nightly. It was
removed once the stable frontend matched or beat it on every example: setup-minimized
circuits within +0.3% everywhere and up to 7% smaller, the same accept/reject verdict
on every example's test inputs, and faster, smaller builds.)

## Toolchain policy

A circuit's proving and verifying keys are made for one exact constraint system,
so the thing that matters is the **circuit digest**: a fingerprint of the R1CS
that `xark build` prints and writes to `target/xark/<name>/digest`. Keys record it
(`metadata.json`'s `digest`), and a key fits every build with that digest. The
`circuit.xbc` file itself can differ between Rust versions (how calls were inlined
decides how repeats are stored), so `xark prove` accepts a key from another build
with the same digest, says so, and its self-check confirms the proof.

- **Rust version.** Any stable Rust from 1.89 on builds circuits, and a circuit's
  digest is the same on every one of them. That is a tested guarantee, not a
  hope: `ci.yml` checks all 70 examples on 1.89, stable and beta on every push,
  and `scheduled.yml` re-checks stable and beta weekly, so a Rust release that
  would change a circuit is caught while it is still in beta. If one
  does, we fix xark so the old digest comes back; we don't ask anyone to make new
  keys. You don't need to pin Rust (a `rust-toolchain.toml` does no harm).
- **xark version.** Only your code or an xark upgrade may change a circuit. An
  xark release that changes any circuit (a gadget fix, a lowering change) gets a
  minor version bump before 1.0 (0.3 → 0.4) and is listed under "Circuits that
  changed" in [CHANGELOG.md](../CHANGELOG.md); a patch release never changes one.
  Lock the xark version (commit `Cargo.lock`) for anything deployed.
- **Minimum Rust.** Raised only in a minor release, and noted in the changelog.
  Nightly Rust isn't supported or tested.

## When a circuit digest changes

`cargo xtask digests --check` failing means one of two things:

- **A toolchain changed a circuit** — rustc lowered some witness operation
  differently (LLVM rewriting integer ops). That is a bug: report it with the
  toolchain and example, and pin the operation through an intrinsic so the
  circuit (and its digest) goes back to what it was.
- **The lowering changed on purpose** — run `cargo xtask digests --update`,
  review the diff, re-check the snapshot suite (`cd crates/lang && cargo test
  --release --test snapshot -- --include-ignored`) and the Lean-model bridges, and
  regenerate any keys built from the old circuits. Name every changed circuit in
  CHANGELOG.md and bump the minor version (see the policy above).
