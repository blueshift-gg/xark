# Working in xark

xark compiles Rust circuits to R1CS and proves them with Groth16. Read
`docs/architecture.md` first (the crate map and the pipeline), then the README of
the area you touch: `crates/frontend/README.md` (wasm → IR), `formal/README.md`
(Lean proofs), `docs/toolchain.md` (why circuits must not change by accident).

## Toolchain

Stable Rust, 1.89 or newer, with the `wasm32-unknown-unknown` target. Nightly is
unsupported and some dependencies don't build on it: if `rustup default` is a
nightly, run everything as `cargo +stable …`. The keyed digests are pinned under
one rustc (`ci.yml`, job `keyed-rows`); `cargo xtask ci` runs those steps under it
and says which `rustup toolchain install` it needs when it is missing.

## The gates

Every pull request runs `.github/workflows/{ci,slow,lean,kani,solana-ci}.yml`.
Locally, `cargo xtask ci --since origin/master` runs the steps your changed files
can affect, side by side, logs in `target/ci/`; `cargo xtask ci --list` names them.
Before opening a PR, `cargo xtask ci` (everything) must be green: fmt, clippy with
`-D warnings`, the workspace tests under the `ci` profile (the `xark` crate's compiler
suite in release), the digests, the Lean exports and coverage, the minimizer certificates and
the publish plan.

## Invariants the gates enforce

- **A circuit changes only on purpose.** `tests/stable-digests.txt` pins every
  example's R1CS. If your change alters any digest, it is a circuit change: run
  `cargo xtask digests --update`, review the diff, name each changed circuit under
  "Circuits that changed" in `CHANGELOG.md` and bump the minor version
  (`docs/toolchain.md`, "When a circuit digest changes"). A gadget fix changes
  every example using that gadget; expect many.
- **A proven gadget emits exactly its proven rows.** `cargo xtask lean-export
  --check` compares each `#[gadget]`'s R1CS with the Lean template under
  `formal/templates/`; `--coverage` checks every production call of it. Changing
  such a gadget means re-exporting and re-proving in `formal/`. Pull requests run
  the coverage in four shards; a stale allowlist entry or constant-plug obligation
  shows up in the full run (`cargo xtask ci`, and weekly on master).
- **The keyed rows are certified.** `cargo xtask minimize-check` runs the Lean
  checker over every minimizer run; a minimizer change must still pass it.
- **Kept tests are end to end** and live in `gadgets/tests/tests/it/` (CLI and
  prover, one binary), `crates/lang/tests/` (compiler snapshots, semantics fuzz), the gadget
  crates' `tests/` (known-answer vectors) and `xtask/tests/`. Heavy vectors are
  `#[ignore]`d and run in `slow.yml`.

## Conventions

- Commit subjects are lowercase sentences without a type prefix: `the 1.89 check
  skips xark-tests`. No AI attribution trailers.
- Comments explain why, in prose, as the existing ones do; a magic number cites
  its source.
- Release-mode tests only: a Groth16 prove or an exhaustive witness search is
  10–50× slower in debug.
- A test that does many independent searches or compiles runs them across the
  cores (`std::thread::scope`, as `snapshot.rs` and `semantics_fuzz.rs` do): CI's
  runner has four, and one test on one core is the suite's tail.
- `cargo xtask difftest` deals the examples whose searches run out their budget
  (`HEAVY` in `xtask/src/difftest.rs`) out first; a new example that takes minutes
  there belongs on that list, with its time from the run's output.

## Taking an idea to a pull request

1. Measure first. A claim about speed or memory needs a before/after on the real
   target: `PROVE_TIME=1 target/release/xark prove …` (a `--features debug`
   build) splits solve from prove; `cargo run --release -p xark-groth16 --example
   bench_prove -- solve <circuit.xbc> <pk> <inputs.json>` isolates the witness
   solve and the soundness gate the tests run (`xark prove` runs no gate), and `RAYON_NUM_THREADS=1` makes the number about the work rather than
   the machine; the semantics fuzzer and `cargo xtask difftest` are the soundness
   oracles. For a profile, `samply record --save-only -o p.json.gz <binary> …`,
   then `atos -o <binary> -arch arm64 -offset <addr>` names the hot addresses.
   The inputs a test fed a circuit: `XARK_DUMP_INPUTS=<dir> xark test <example>`.
2. Write down the change before the code: which files, how many lines, which
   invariant above it touches. Smaller is better; the review bar is a human reading
   the diff in one sitting.
3. Branch from `origin/master`, implement, run `cargo xtask ci --since
   origin/master`, then the full `cargo xtask ci`.
4. Open the PR with the measurement, the invariants checked and what was left out.
