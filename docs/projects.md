# Projects: a circuit, its program and its clients

Status: unreleased after 0.4, except the `prove` feature of the generated Rust
crate (planned).

Before projects, getting from a circuit to a working Solana program took five xark
commands, a `cargo build-sbf` whose stack warnings had to be grepped for, and
public inputs packed by hand. Every example in xark-examples carried the same
glue, each in its own `package.json`:

- `build && setup && prove && export && client`, then `cargo build-sbf`, then a grep
  for `overflows the maximum allowed frame space`;
- a program that rebuilds `[[u8; 32]; N]` by hand: zKYC's `policy.rs` repeats
  `#[input]`'s bit packing (`today` in bits 0–16, `born_by` in 17–33, …) and splits
  an address into its hi/lo halves. Nothing checks that order or packing against
  the circuit: a reordered `#[input]` fails verification with nothing pointing at
  the cause;
- a `client/harness.ts` (four versions across six examples) and one Cargo
  workspace per piece.

The generated code also lands in two places: the verifier crate beside the
circuit (`<crate>/<name>-verifier/`) and the TypeScript client under `target/`,
where `cargo clean` deletes it.

## A project

`xark init my-app` makes a project: a directory with a `xark.toml`, one Cargo
workspace, and a starter circuit in `circuits/my-app/`. On a terminal it asks
whether to scaffold a Pinocchio (LiteSVM) program; `--program pinocchio` and
`--program none` skip the question, and `--program-name` names it (default: the
first circuit). `xark add` grows it, and refuses to run
outside one.

```console
$ xark init claim --program pinocchio && cd claim
$ xark test                   # the circuit loop: build + witness tests, no keys
$ xark setup                  # optional: an explicit key; a build bootstraps a dev one
$ xark build --check          # circuit, clients and keys
$ cargo build-sbf             # the program
$ cargo test-sbf              # its SBF tests
$ npm install && npm test     # its LiteSVM test
```

`xark build` and `xark test` are circuit-only. Program builds and tests use the
framework's own commands; `xark add program` can add a Pinocchio program to an
existing project or add a second one.

```text
claim/
  xark.toml             # the pinned xark release
  Cargo.toml            # the workspace: members, the programs' profile (and default-members with a program)
  rust-analyzer.toml    # `xark check .` at the root (and .vscode/settings.json)
  package.json  tsconfig.json  vitest.config.ts
  circuits/claim/       # the starter circuit and its tests
  programs/claim/       # Pinocchio: lib.rs, errors.rs, instructions/verify.rs
  clients/claim/rust/   # generated, committed: the verifier crate `claim-verifier`
  clients/claim/ts/     # generated, committed: the TypeScript client
  keys/claim/           # committed: pk.bin, vk.bin, metadata.json, circuit.xbc
  tests/claim.test.ts   # LiteSVM
  .github/workflows/ci.yml   # xark build --check, xark test (circuits)
  .github/workflows/programs.yml   # optional: cargo build-sbf, cargo test-sbf, npm test
```

- **Fixed folders.** `circuits/*`, `programs/*` and `clients/*/rust` are globbed
  in the root `Cargo.toml`, so `xark.toml` lists nothing. Cargo reads a glob that
  matches nothing as a missing path, so `xark init`, `xark add`, `xark build` and
  `xark export` keep `members` to the globs that hold a crate; a `programs/*` left
  behind by a deleted program is dropped so cargo can load the workspace again.
  Restoring that program from git restores its directory but not the manifest
  entries: since `xark add program` refuses an existing directory, add
  `programs/*` (and `default-members`) back by hand.
- **The Pinocchio scaffold makes the programs the default members.** `xark add
  program` sets `default-members = ["programs/*"]` (keeping any of your own
  entries) so a bare `cargo test` or `cargo build` at the root targets the
  programs. The SBF commands do not use `default-members`: `cargo build-sbf` and
  `cargo test-sbf` select the workspace's `cdylib` members, which is why a bare
  command works here (and would also build another `cdylib` member), whatever the
  default-members say. `xark build` leaves the setting alone, dropping only a
  stale `programs/*` entry. `xark test` tests the circuits only; the program has
  its own commands.
- **Programs are native.** The Pinocchio scaffold writes a LiteSVM test and an
  optional `.github/workflows/programs.yml` that runs `cargo build-sbf`, the
  4 KiB stack check, `cargo test-sbf`, the generated verifier self-tests, and
  `npm test`. `xark` does not build or test programs. `xark add program` is the
  incremental path; the init wizard is the normal one.
- **Crate names.** A workspace can't hold two packages of one name: the program in
  `programs/claim/` is the crate `claim-program`, the client `claim-verifier`.
  `xark add program claim` uses the circuit of the same name; `--circuit` picks
  another.
- **One workspace is safe for circuits.** The circuit build sets its own
  `overflow-checks`, `opt-level` and `panic` through `--config`
  (`crates/frontend/src/lib.rs`), so the root `[profile.release]` can be the
  program's (fat LTO, no overflow checks) without changing any circuit.
- **Keys are committed.** The verifier crate embeds the verifying key and is
  committed, so the keys are too, in `keys/<circuit>/`: a key only in the
  gitignored `target/` would be replaced on a fresh clone, and the verifier with
  it. A key proves only with the build of the circuit it was made from, so that
  `circuit.xbc` is kept beside it and every prover uses it: a clone that compiles
  the same circuit differently still proves. `xark build` compares the kept build's
  constraint digest with the current build's: the same, the key fits; different,
  the circuit changed and needs new keys. `xark build` makes a key when there is
  none, and rotates a plain OS-random single-party key when the constraints
  change (saying the verifier changes too). A ceremony key, a phase-2 key from a
  `.ptau`, a seeded test key, or a key with no metadata is never rotated by a
  build: use `xark setup`/`xark ceremony`. A missing key is bootstrapped from OS
  randomness, ignoring a `.ptau`. `xark prove` keeps its first-proof
  convenience. A proving key over 50 MB belongs in Git LFS (the zKYC circuit's is
  265 KB, SHA-256's 3.2 MB, Ed25519's 450 MB).
- **Stable clients.** A rebuild leaves `clients/` byte for byte as it was: the
  sample proof a verifier crate bundles is kept while it verifies, since a proof
  is randomized and only whoever proved last has one. `xark build --check` (CI)
  stages the generated clients under `target/xark/check/` and compares them; it
  writes nothing under `clients/`, `keys/` or the workspace manifest, and fails
  when the committed clients aren't what the source generates.
- **One release.** `xark.toml` records the xark release; the root commands warn
  when the CLI is another.
- **Commands at the root.** One circuit is the default for every command that
  takes one (`xark prove`, `xark export`, `xark inspect`); with several, name it
  (`xark prove circuits/claim`).

A crate made by an earlier `xark init` (no `xark.toml`) still works as before: its
clients go in its own `clients/{rust,ts}`.

## Generated clients go in `clients/`

A circuit's generated code goes in `clients/<circuit>/{rust,ts}` at the project
root. `--out` still overrides it. It is committed, so a fresh
clone builds the program without running xark first; CI checks it is up to date.

- **`clients/…/rust`** is the crate `xark export` writes. With no features it is
  the `no_std` verifier a program depends on. A planned `prove` feature would prove
  from typed inputs on the host, for Rust tests and relayers.
- **`clients/…/ts`** is what `xark client` writes: `prove()` and typed inputs. A
  proof's `toInstructionData()` is the proof and its public inputs as the
  program's `Fields`.

The tests use `@blueshift-gg/xark/testing`: a circuit's build output by name
(`circuit("claim")`), a LiteSVM with the project's programs
(`program("claim")`),
a funded payer and `send`. Every example carried its own copy of these.

## Typed public inputs

`xark export` generates, from `schema.json`, a `PublicInputs` struct with the
circuit's public inputs as named fields, and `verify(&proof, inputs)` (a `PublicInputs`, by value). It
packs them into field elements as `#[input]` does, from the packing `schema.json`
records (`"packed": { "offset", "bits" }`), so a program never does it by hand:

```rust
use zkyc_verifier::{Bitfield, Country, Days, Policy, PublicInputs};

let today = Days::<1900, 2100>::from_unix(clock.unix_timestamp).ok_or(…)?;
let inputs = PublicInputs {
    commitment: record.commitment,
    policy: Policy {
        today,
        born_by: …,
        min_net_worth: 500_000,
        allowed: Bitfield::<Country>::EMPTY.with(Country::DE).with(Country::FR),
    },
    holder: holder.address().to_bytes(), // an `Address`: its 32 bytes, split into hi/lo for you
};
if !zkyc_verifier::verify(&proof, inputs) { … }
```

`verify` takes `impl Into<Fields>` (`[[u8; 32]; N]`), so `PublicInputs` is a
convenience, not a requirement: a program can pass the elements, or its own
struct with a `From` impl packed with `xark_verifier::fields`. `to_fields()` and
the `fields` packer are `const fn`s with each field's width a const generic
(`Packer::new().uint::<17>(day)`), so inputs known at compile time are constants
and a value too wide for its bits fails the build.

A circuit's own tests keep using the circuit's types (`use super::*`): they are
the source the generated crate comes from, and depending on `clients/rust` would
need an export before the tests compile. The host prover's
`CircuitProof::to_solana_public_inputs()` gives the elements' bytes (`N × 32`,
little-endian), which split into `Fields` for `verify`.

Each input type gets a `no_std` Rust form (`crates/cli/src/commands/public_inputs.rs`):
a field element `[u8; 32]`, an integer its Rust integer, a `Time`/`Days` range
with `from_unix`, a `Timestamp` an `i64`, `Text` a `Text`, a `Choice` a generated
enum, a `Bitfield` a set of it, an `Address` or a byte-encoded type such as `Hash` its bytes. A
type with no Rust form yet (a limbed number, an Ed25519 point) gives no
`PublicInputs`: `verify` then takes the field elements (`Fields`), which
`xark_verifier::fields` packs. Every export with a sample proof checks the
encoder against `xark_schema`, the codec `xark prove` uses: the crate's self-test
writes the sample's public inputs by name, packs them and verifies the proof.

## At the project root

- `xark build`: each circuit and its clients. A missing key is bootstrapped with
  `xark setup` from OS randomness, not a stray `.ptau`; a changed plain
  single-party dev key is rotated with the old warning, while a ceremony or
  phase-2 key stops with `xark setup`/`xark ceremony`.
- `xark test`: each circuit's tests and those of a library beside them.
  `--check` verifies the committed clients/keys instead of refreshing them.
- `xark check` (what rust-analyzer runs): `cargo check --workspace` once, then
  xark's own validation of each circuit. One override for the whole workspace;
  programs see ordinary cargo diagnostics.

`xark init --program pinocchio` and `xark add program` scaffold one Pinocchio
program with a LiteSVM test. `programs.yml` is optional and owned by the
scaffolder; it installs the framework tools and runs the native program steps.
The circuit workflow runs `xark build --check` and `xark test` only.

## Upgrading from 0.4

An existing 0.4 project's old `.github/workflows/ci.yml` calls `xark build --check`
and `xark test`. Those stay circuit-only, so their programs need the native
program workflow. Remove any `[programs]` metadata; xark ignores it. To move:

- add `.github/workflows/programs.yml` (copy it from a fresh `xark add program`
  project): it runs `cargo build-sbf`, the stack check, `cargo test-sbf`, the
  verifier self-tests, and `npm test`;
- keys stay committed; `xark build` bootstraps a missing key and rotates a plain
  dev key, while a ceremony key needs `xark ceremony` again;
- keep `programs/*` in the workspace's `members` and, for bare cargo commands,
  `default-members`; `xark build` no longer adds them for you;
- pin the release containing this change in `xark.toml` (and bump the workspace
  and npm package versions);
- if you restore a program directory from git after xark dropped a stale
  `programs/*` entry, add the manifest entries back by hand.

## Order of work

1. The `clients/` default for `xark export` and `xark client`. (Built.)
2. Typed `PublicInputs` in the generated Rust crate. (Built.)
3. `xark add circuit|program` and `xark.toml`. (Built.)
4. `xark init` makes the project; `xark build`, `xark test` and `xark check` at
   its root. (Built.)
5. The root commands stop at the circuit and its clients; a program's build and
   tests are its framework's. (Built.)

`xark init` making a project, and the default output folders moving, were 0.4. The
root commands stopping at the circuit and its clients is a breaking change in the
next release.
