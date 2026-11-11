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

## Two shapes, one tool

`xark.toml` says what a directory is, the way a `Cargo.toml` is a package or a
workspace.

**A circuit** is what `xark init` makes today, unchanged. It has no `xark.toml`.

**A project** is a directory with a `xark.toml`. Nobody writes one by hand:
`xark add` makes it on first use.

```console
$ mkdir my-app && cd my-app
$ xark add circuit claim
$ xark add program claim
```

```text
my-app/
  xark.toml             # settings: the pinned xark version
  Cargo.toml            # [workspace] members = ["circuits/*", "programs/*", "clients/*/rust"]
  package.json          # vitest, litesvm, @blueshift-gg/xark
  circuits/claim/       # the same files `xark init claim` writes
  programs/claim/       # Pinocchio, `verify` wired to clients/claim/rust
  clients/claim/rust/   # generated, committed
  clients/claim/ts/     # generated, committed
  tests/claim.test.ts   # LiteSVM
```

- **Fixed folders.** `circuits/`, `programs/` and `clients/` are globbed in the
  root `Cargo.toml`, so `xark add` never edits `members` and `xark.toml` lists
  nothing.
- **Crate names.** A workspace can't hold two packages of one name: the program in
  `programs/claim/` is the crate `claim-program`, the client `claim-verifier`.
  `xark add program claim` uses the circuit of the same name; `--circuit` picks
  another.
- **One workspace is safe for circuits.** The circuit build sets its own
  `overflow-checks`, `opt-level` and `panic` through `--config`
  (`crates/frontend/src/lib.rs`), so the root `[profile.release]` can be the
  program's (fat LTO, no overflow checks) without changing any circuit.

## Generated clients go in `clients/`

One rule for both shapes: a circuit's generated code goes in
`clients/<circuit>/{rust,ts}` at the project root, or `clients/{rust,ts}` in a
lone circuit's crate. `--out` still overrides it. It is committed, so a fresh
clone builds the program without running xark first; CI checks it is up to date.

- **`clients/…/rust`** is the crate `xark export` writes. With no features it is
  the `no_std` verifier a program depends on. With `prove` it proves from typed
  inputs on the host, for Rust tests and relayers.
- **`clients/…/ts`** is what `xark client` writes: `prove()`, typed inputs and the
  instruction data.

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

- `xark build`: builds the circuits, re-runs setup when a key is stale, writes
  `clients/`, then runs `cargo build-sbf` and fails on the SBF 4 KiB frame warning.
- `xark test`: the circuits' tests, then the LiteSVM tests.
- `xark check` (what rust-analyzer runs): `cargo check --workspace` once, then
  xark's own validation on the members that are circuits (a crate that depends on
  `xark` and has a `#[circuit]`). One override for the whole workspace; programs
  see ordinary cargo diagnostics.

## Order of work

1. The `clients/` default for `xark export` and `xark client`. (Built.)
2. Typed `PublicInputs` in the generated Rust crate. (Built.)
3. `xark add circuit|program` and `xark.toml`.
4. `xark build`, `xark test` and `xark check` at the project root.

The first two stand on their own: a lone circuit gets them before projects exist.
Changing the default output folder is a breaking change, so this is 0.4.
