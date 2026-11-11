# Projects: a circuit, its program and its clients

Status: design. Nothing here is built yet except where a section says so.

Getting from a circuit to a working Solana program takes five xark commands, a
`cargo build-sbf` whose stack warnings have to be grepped for, and public inputs
packed by hand. Every example in xark-examples carries the same glue, each in its
own `package.json`:

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
workspace, and a starter circuit in `circuits/my-app/`. `xark add` grows it, and
refuses to run outside one.

```console
$ xark init claim && cd claim
$ xark add program claim
$ xark build
$ npm install && xark test
```

```text
claim/
  xark.toml             # settings: the pinned xark release
  Cargo.toml            # the workspace: members, default-members, the programs' profile
  rust-analyzer.toml    # `xark check .` at the root (and .vscode/settings.json)
  package.json  tsconfig.json  vitest.config.ts
  circuits/claim/       # the starter circuit and its tests
  programs/claim/       # Pinocchio: lib.rs, errors.rs, instructions/verify.rs
  clients/claim/rust/   # generated, committed: the verifier crate `claim-verifier`
  clients/claim/ts/     # generated, committed: the TypeScript client
  keys/claim/           # committed: pk.bin, vk.bin, metadata.json
  tests/claim.test.ts   # LiteSVM
  .github/workflows/ci.yml   # xark build --check, then xark test
```

- **Fixed folders.** `circuits/*`, `programs/*` and `clients/*/rust` are globbed
  in the root `Cargo.toml`, so `xark.toml` lists nothing. Cargo reads a glob that
  matches nothing as a missing path, so `xark init`, `xark add` and `xark export`
  keep `members` to the globs that hold a crate.
- **`default-members` are the programs.** Cargo merges features across what it
  builds together, so the circuits' host dependencies (`getrandom` through
  `rand`) would join an SBF build of the whole workspace and break it. With the
  programs as the default, a bare `cargo build-sbf` at the root builds them alone.
  A bare `cargo test` is the programs' too; `xark test` runs everything.
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
  it. `xark build` and `xark prove` never make a key while a committed verifier
  embeds one; a new key is an explicit `xark setup`. A proving key over 50 MB
  belongs in Git LFS (the zKYC circuit's is 265 KB, SHA-256's 3.2 MB, Ed25519's
  450 MB).
- **Stable clients.** A rebuild leaves `clients/` byte for byte as it was: the
  sample proof a verifier crate bundles is kept while it verifies, since a proof
  is randomized and only whoever proved last has one. `xark build --check` (CI)
  fails when the committed clients aren't what the source generates.
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
  the `no_std` verifier a program depends on. With `prove` it proves from typed
  inputs on the host, for Rust tests and relayers.
- **`clients/…/ts`** is what `xark client` writes: `prove()` and typed inputs. A
  proof's `toInstructionData()` is the proof and its public inputs as the
  program's `Fields`.

The tests use `@blueshift-gg/xark/testing`: a circuit's build output by name
(`circuit("claim")`), a LiteSVM with the project's programs (`program("claim")`),
a funded payer and `send`. Every example carried its own copy of these.

## Typed public inputs

`xark export` generates, from `schema.json`, a `PublicInputs` struct with the
circuit's public inputs as named fields, and `verify(&proof, &PublicInputs)`. It
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
    holder: *holder.address(), // a `Hash`: its 32 bytes, split into hi/lo for you
};
if !zkyc_verifier::verify(&proof, &inputs) { … }
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
enum, a `Bitfield` a set of it, a byte-encoded type such as `Hash` its bytes. A
type with no Rust form yet (a limbed number, an Ed25519 point) gives
`PublicInputs([[u8; 32]; N])`. Every export with a sample proof checks the
encoder against `xark_schema`, the codec `xark prove` uses: the crate's self-test
writes the sample's public inputs by name, packs them and verifies the proof.

## At the project root

- `xark build`: each circuit, its keys when they're missing or for an older
  circuit, its clients, then `cargo build-sbf`, failing on the SBF 4 KiB frame
  warning that `cargo build-sbf` only prints.
- `xark test`: each circuit's tests, then (with programs) the build above, the
  programs' Rust tests and `npm test`.
- `xark check` (what rust-analyzer runs): `cargo check --workspace` once, then
  xark's own validation of each circuit. One override for the whole workspace;
  programs see ordinary cargo diagnostics.

## Order of work

1. The `clients/` default for `xark export` and `xark client`. (Built.)
2. Typed `PublicInputs` in the generated Rust crate. (Built.)
3. `xark add circuit|program` and `xark.toml`. (Built.)
4. `xark init` makes the project; `xark build`, `xark test` and `xark check` at
   its root. (Built.)

`xark init` making a project, and the default output folders moving, are breaking
changes, so this is 0.4.
