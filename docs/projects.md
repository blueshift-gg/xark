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
let inputs = zkyc_verifier::PublicInputs {
    commitment: record.commitment,
    policy: zkyc_verifier::Policy {
        today: Day::from_unix(clock.unix_timestamp)?,
        born_by: …,
        min_net_worth: 500_000,
        allowed: Countries::EMPTY.with(Country::DE).with(Country::FR),
    },
    holder: Address(*holder.address()),
};
if !zkyc_verifier::verify(&proof, &inputs) { … }
```

Each standard type (`crates/cli/src/commands/client/model.rs`) gets a `no_std`
Rust form: a field element `[u8; 32]`, an integer its Rust integer, a `Days`
range a step count with `from_unix`, a `Choice` or `Bitfield` a generated enum
and set, an address its 32 bytes (split into hi/lo when packed). A type with no
Rust form yet leaves `verify` taking `[[u8; 32]; N]`, as today. The encoder is
tested against `xark_schema`, the codec `xark prove` uses, on every example.

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
2. Typed `PublicInputs` in the generated Rust crate.
3. `xark add circuit|program` and `xark.toml`.
4. `xark build`, `xark test` and `xark check` at the project root.

The first two stand on their own: a lone circuit gets them before projects exist.
Changing the default output folder is a breaking change, so this is 0.4.
