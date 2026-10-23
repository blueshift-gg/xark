# xark — write, compile, prove and verify zero-knowledge circuits in Rust

[![CI](https://github.com/blueshift-gg/xark/actions/workflows/ci.yml/badge.svg)](https://github.com/blueshift-gg/xark/actions/workflows/ci.yml)

xark takes a circuit written as ordinary Rust all the way to an on-chain proof.
You write the circuit in Rust; xark compiles it with your stable `rustc` (to
wasm32), lowers the module to R1CS, and proves it with Groth16 over BN254 — with a verifier that runs on Solana. There is no
separate circuit DSL: **gadgets are ordinary Rust libraries** that lower to a
small primitive constraint set, so the backend stays lean and the frontend
stays expressive.

## Installation

xark needs only stable Rust, 1.89 or newer:

```bash
cargo install xark-cli
xark doctor        # checks your setup
```

`xark build` compiles your circuit crate with the toolchain you already have (to
`wasm32-unknown-unknown`, which it adds with `rustup` on first use). To build from source instead, append `--git https://github.com/blueshift-gg/xark`.

## As a language (library)

Write a circuit as a `#[circuit]` function over `Field` values, using the `xark`
prelude (`xark init` scaffolds the crate, `Cargo.toml` included; see
`examples/cube`). `require_eq` emits a circuit equality constraint (not a native `bool`);
`Private<T>` / `Public<T>` mark input visibility; `Field` supports `+ - *`,
`.pow(n)` for exponentiation by a constant, and `^` as boolean XOR.

```rust
use xark::prelude::*;

/// Prove knowledge of a cube root: `secret^3 == result`.
#[circuit]
pub fn cube(secret: Private<Field>, result: Public<Field>) {
    require_eq(secret.pow(3), result);
}
```

### Testing a circuit from Rust

`#[circuit]` also generates a validator under the circuit's name for tests and
host code: the same parameters, each taking whatever converts to it. A `Field`
takes an integer, a decimal or `0x`-hex string, or an `ark_bn254::Fr`; a
gadget's input types take their natural form, such as an Ed25519 public key's
32 bytes or a Grumpkin point's `(x, y)`.

```rust
#[test]
fn accepts_a_cube_root() {
    cube(3, 27).unwrap();
    assert!(cube(3, 28).is_err());
}
```

Inputs that fail a check are reported as the statement that fails, in tests, in
`xark prove` and in the TypeScript client alike:

```text
error: witness does not satisfy the circuit

  src/lib.rs:96:20  id.nationality.require_in(policy.allowed);
```

Every build writes `sources.json` beside `circuit.xbc` for this: which source
line each constraint came from (the circuit itself is unchanged by it).

Circuit code also runs as plain Rust on the host: `Field` arithmetic,
comparisons, hints and whole gadgets compute their values, and a failed
`require` panics at its line. So tests and services call the same helpers the
circuit does. `zkyc`'s tests make the issuer's commitment with
`id.commitment()`, the very function the circuit checks it with, and
`pubkey.verify(sig, digest)` checks an ECDSA signature off-circuit. (Calling the
`#[circuit]` fn itself still checks the circuit through the prover.)

### Inputs

Every circuit parameter's type implements `xark::Input`, which says how its value
maps to field elements and how clients see it. Group inputs into structs with
`#[input]` (which also derives `Clone`, `Copy` and `Debug` unless the type lists
them; `#[input(no_derive)]` for a type with its own), including gadget types:
`examples/grumpkin_ivc` takes a few
`Instance { cw, ce, u, x }` values instead of twenty separate parameters, and
`to_fields()` hashes one in a single call. The generated `<Fn>Inputs` struct
holds the same values for `xark::prover::circuit(..).check(..)`, `.prove(..)`
and friends. A circuit crate needs only the `xark` dependency.

### Everyday input types

`xark` ships the types most credential-style circuits need, each one field wide
and each with its natural form in tests, `--inputs` and the TypeScript client:

- `Date`: a calendar day: `"1990-01-01"` in Rust and `--inputs`, a `Date` (its
  UTC day) in TypeScript, and a 27-bit comparison for `<`/`>=` in the circuit.
- `Text`: a short string, up to 31 bytes (a document number, a name).
- `Choice<E>` and `Bitfield<E>`: one variant of an enum, or a set of them, such
  as a nationality and the allowed countries: `choice == Country::US`,
  `require_in`, `require_one_of`, `contains`. Any fieldless enum with `#[input]` works;
  `xark` ships ISO 3166 `Country`.

```rust
#[input]
pub struct Identity { document: Text, born: Date, nationality: Choice<Country>, net_worth: u64, expires: Date, salt: Field }

/// A verifier's rules, a public input: one circuit serves every policy.
#[input]
pub struct Policy { today: Date, born_by: Date, min_net_worth: u64, allowed: Bitfield<Country> }

#[circuit]
fn zkyc(id: Private<Identity>, commitment: Public<Field>, policy: Public<Policy>) {
    require_eq(id.commitment(), commitment);
    require(id.born <= policy.born_by);
    require(id.net_worth >= policy.min_net_worth);
    require(id.expires >= policy.today);
    id.nationality.require_in(policy.allowed);
}

// In a test:
// let policy = Policy::default().on("2026-10-20").min_age(18).worth_at_least(500_000).nationalities([US, GB, FR, DE]);
// zkyc(id, id.commitment(), policy)
```

`examples/zkyc` is this circuit in full. A `bool` input works too: one field
element, checked to be 0 or 1.

A type `#[input]` doesn't cover implements `Input` by hand, in one impl that
serves the circuit and the host alike:

```rust
impl Input for Hash {
    const TYPE: Type = Type::Named(
        &Type::named("Hash", Layout::fields(&[Member::new("hi", Type::Field), Member::new("lo", Type::Field)]))
            .encoded(Encoding::Bytes(Bytes::Split(&[16, 16]))), // clients give its 32 bytes
    );
    fn read(r: &mut Reader) -> Self { Hash { hi: r.field(), lo: r.field() } }
    fn write(&self, w: &mut Writer) { w.field(self.hi); w.field(self.lo) }
}
```

A `TYPE` is built from the standard types (field, `uN`, bytes, number, date,
text, choice, set, arrays, tuples, structs), and those are what client
generators map: adding a language means mapping that fixed list, never a
circuit's own types.

## As a toolchain (CLI)

```bash
# Scaffold a new circuit crate, pre-wired for rust-analyzer diagnostics.
xark init my-circuit

# Compile: Rust → wasm → xark-IR → R1CS. All output (artifacts + an isolated
# cargo target) lives under the crate's target/xark/.
xark build examples/cube
# → writes examples/cube/target/xark/cube/ (circuit.xbc + schema.json) and
#   prints the circuit digest (a fingerprint of the R1CS the keys are made for).

# Build, then run the crate's own `cargo test` circuit tests (they check inputs
# against the circuit and name the source line of a failing constraint).
# Arguments go to `cargo test`: `xark test examples/cube -- --nocapture`.
xark test examples/cube

# Generate a typed TypeScript client from schema.json: no setup or proof needed.
# Like every command, it defaults to the current directory: inside the crate,
# plain `xark client` is enough.
xark client examples/cube
# → examples/cube/target/xark/cube/cube.ts, and the cube.schema.ts it imports

# Generate Groth16 keys. With no .ptau this produces an INSECURE dev key
# (single-party OsRng); pass --ptau-file (or run `xark ceremony`) for production.
xark setup examples/cube

# Solve the witness from your inputs, then produce AND verify a Groth16 proof.
# Writes proof.bin and public_inputs.bin next to the keys.
xark prove examples/cube --inputs '{"secret": "3", "result": "27"}'
# → ✅ Proof produced and self-checked (1 public input(s)).
# A gadget type takes its natural form: an Ed25519 key or a hash as 0x-hex bytes,
# a scalar as a number. `xark setup` prints (or writes) a template to fill in.

# Check a proof against the verifying key and its public inputs.
xark verify examples/cube

# Generate the Solana verifier crate (the key embedded, the proof bundled as its
# self-test). Refuses a dev key unless you pass --allow-insecure.
xark export examples/cube

# Validate a circuit WITHOUT emitting artifacts — subset violations as rustc
# diagnostics with source spans (great for editors / CI).
xark check examples/cube

# Where the constraints go: by source line, function and kind, each kind explained.
# --html also writes target/xark/<name>/profile.html, the source shaded by cost.
xark profile examples/zkyc --html
```

### Typed clients

```sh
xark client                                  # writes <circuit>.ts and <circuit>.schema.ts
npm install @blueshift-gg/xark-wasm@0.3      # the runtime they import
```

`xark build` also writes `schema.json`: every input's name, visibility and
`Input::TYPE`, plus the public inputs in proof order. `xark client` resolves it
into the standard types and writes one `.ts` file: constants and a type per enum,
an interface per struct, the inputs, the public inputs as given and as decoded, and
the circuit, which makes its provers and verifiers. What every client shares
(`Field`, `Proof`, loading xark-wasm and the build output) is xark-wasm's
`@blueshift-gg/xark-wasm/client`, so the file holds only the circuit, and an app
imports only the file. Beside it, `xark client` writes the schema the file imports,
`zkyc.schema.ts` (the circuit's `schema.json` as a module's default export, so no
project settings are needed): the two are written together, so they always agree.
Each type is the one you'd write by hand:

```ts
export const Country = { AD: "AD", AE: "AE", /* … */ US: "US", ZW: "ZW" } as const;
export type Country = (typeof Country)[keyof typeof Country]; // "AD" | "AE" | …

export interface Identity {
  document: Text;              // a string, at most 31 bytes
  born: Day;                   // a Date: its UTC day
  nationality: Country;        // Country.US, or "US"; "XX" won't compile
  netWorth: U64;               // bigint | number, in the attestor's unit
  expires: Day;
  salt: FieldInput;            // a Field, or an integer
}
```

A field input takes a plain integer (a `bigint`, a safe integer, a decimal or
`0x`-hex string) or a `Field`; either way it must be below the field's modulus, so a
value that would wrap or round never reaches the prover, and a mistake names the
input. `new Field(x)` checks it where you make it, and also takes little-endian
bytes (as proofs and Rust's `Field::from_le_bytes` have them; `Field.fromBeBytes`
for the other order). Decoded public inputs and Rust functions return `Field`s.

A prover and a verifier are separate, each made from a URL serving a copy of
`target/xark/<circuit>/` or from the bytes, so each has only the methods it can
run. A proof travels as its bytes, `proof.toBytes()`; the verifier brings the public
inputs it requires:

```ts
import { Country, Field, Identity, Policy, Zkyc } from "./zkyc";

// In the app: fetches circuit.xbc, pk.bin, sources.json and client.wasm, and loads
// xark-wasm (node, web or workerd).
const prover = await Zkyc.prover("/circuits/zkyc/");
const id = { document: "A1938274", born: new Date("1990-01-01"), nationality: Country.US, netWorth: 1_000_000, expires: new Date("2030-01-01"), salt: new Field(saltBytes) };
const commitment = Identity.commitment(id); // the circuit's own Rust (below)
const policy = Policy.default().on(new Date()).minAge(18).nationalities([Country.US, Country.GB, "FR", "DE"]);
const proof = prover.prove({ id, commitment, policy });
proof.publicInputs.policy.allowed; // ["DE", "FR", "GB", "US"]: decoded, a Date stays a Date
send(proof.toBytes(), commitment);

// On the server: check it proves the policy you require, not just any.
const verifier = await Zkyc.verifier(vkBytes); // or a URL, or { verifyingKey, client }
verifier.verify(bytes, { commitment, policy: required }); // true
```

`proof.toBytes()` is the proof as the Solana verifier `xark export` generates reads
it (256 bytes; `Proof::from_le_bytes` on chain), so a program checks it against
public inputs it supplies itself, such as its policy or a root in its state.
`proof.toBytesCompressed()` is half the size, for anywhere else; a verifier reads
either.

To be sure the prover runs the circuit the client was generated from, and not
whatever a deployment serves, pin it: `Zkyc.prover(url, { digest: Zkyc.digest })`
refuses any other circuit (`Zkyc.digest` is the digest `xark build` printed). The
check is one pass over the circuit when the prover is made (about 2 s for Ed25519 in
node), not per proof. A verifier pins its key the same way: `Zkyc.verifier(vk, {
keyHash })` refuses any other `vk.bin` (`xark setup` prints its sha256).

`Policy.default().on(…).minAge(18)` and `Identity.commitment(id)` are the crate's Rust,
not a TypeScript copy of it: the same `#[input]`, on an `impl` block, makes its
methods client functions, typed from their signatures and documented with their doc
comments.

```rust
#[input]
impl Default for Policy {
    /// A policy every holder passes: no expiry, age, net worth or nationality check.
    fn default() -> Policy { … }
}

#[input]
impl Policy {
    /// Checked on `today`: the holder's document mustn't have expired by then.
    pub fn on(self, today: impl Into<Date>) -> Policy { … }
    /// At least `years` old on `today` (set it with `on` first).
    pub fn min_age(self, years: u16) -> Policy { … }
}
```

A trait's `impl` works the same way: `impl Default` gives `Policy.default()`.

`xark client` builds the crate's host code once more as `client.wasm` (beside
`circuit.xbc`; a prover or verifier made from a URL fetches it, or
`await Zkyc.ready(url)` loads it alone), with no JS glue, and
each call runs it: values cross in their natural forms, a Rust panic arrives as an
exception with its message. Parameters and results are any `Input` type. It
works from any crate: a gadget that puts `#[input]` on its types and their `impl`s
brings those functions to the client of every circuit that takes them, with
nothing added to xark. A method that takes `self` is also a method on the values
these functions return and on decoded public inputs, so a chain reads as in Rust:
`Policy.default().on(today).minAge(18).worthAtLeast(500_000)`. A method named like a field
can't be both in TypeScript: it stays `Policy.method(value, …)`, and `xark client`
warns, so you can rename it.

The client holds no encoding logic of its own: xark-wasm encodes values against
the schema with the same Rust code as `xark prove --inputs`, so the two can't
drift, and a mistake names its input (`id.document: "…" is longer than 31 bytes`).
Errors are typed for a UI to act on: an `InputError` carries the input's `path`
(`"id.document"`), and a `CheckFailed` the failing statement's `site` (`file`,
`line`, `col`, `text`, the functions it called into).
`clients/check/{zkyc,cube,sha256,merkle}/` hold those examples' generated clients
and their vitest tests. `npm test` there (run in CI) builds xark, xark-wasm and each
example, fails if a committed client is stale (`npm run update` rewrites it),
typechecks, and runs the tests in Node; a folder with a `<name>.test.ts` is all a new
example needs.

## Editor diagnostics (rust-analyzer)

`xark check <crate-dir>` runs the full `rustc` frontend *and* the xark subset
validator, surfacing every rejection as a **real `rustc` diagnostic with a source
span**. With `--message-format=json` it emits the same JSON stream as `cargo
check`, so an editor shows live rejections on save. In that mode it first runs the
`cargo check --all-targets` it replaces, so errors in tests and other host-only
code still show. `xark init` writes this
wiring; to add it to an existing crate, point `rust-analyzer`'s check command at
`xark` (which must be on `PATH`):

```toml
# rust-analyzer.toml
[check]
overrideCommand = ["xark", "check", ".", "--message-format=json"]
```

```jsonc
// .vscode/settings.json (VS Code equivalent)
{
  "rust-analyzer.check.overrideCommand": ["xark", "check", ".", "--message-format=json"]
}
```

Replace `.` with the crate directory (e.g. `examples/cube`) when the editor is
opened above the circuit crate. A violation then appears inline, e.g.:

```text
error: witness-dependent control flow is not supported
 --> src/lib.rs:7:5
note: branch conditions must be compile-time constants (e.g. loop bounds)
```

## The pipeline

```text
Rust source  →  rustc (stable, wasm32)  →  xark-IR  →  R1CS  →  Groth16 (BN254)  →  Solana verifier
```

`xark build` runs `cargo` on your circuit crate for `wasm32-unknown-unknown` with
`--cfg xark`, where every circuit operation (`Field` arithmetic, comparisons,
hints, `require_eq`, input binding) is a call to an `xark.*` wasm import. rustc
does the hard work — parse, type-check, borrow-check, monomorphize, optimize — and
xark then runs the module with those imports implemented as the circuit builder:
loops and calls with known values simply execute (that *is* the unrolling), and
witness values flow into constraints. The circuit is the same under every stable
rustc (CI checks every example on 1.89, stable and beta), and constraint-reducing
rewrites are proven exact in Lean (`formal/Formal/Rewrites.lean`). Details:
[`crates/frontend/README.md`](crates/frontend/README.md).

## Proving and verifying in JavaScript

Prove and verify anywhere JavaScript runs with
[`@blueshift-gg/xark-wasm`](crates/wasm/README.md) (`prove(circuit, pk, inputs, sources?)`,
`verify(vk, proof, publicInputs)`), or through the typed client `xark client`
generates over it (above). `xark prove` writes the same bytes `verify` takes:
`proof.bin` and `public_inputs.bin`.

## Crates and gadgets

* **`xark`** (`crates/lang`, `#![no_std]`, stable) — the language library; its
  `prelude` provides the marker primitives (`Field`, `require_eq`,
  `Private`/`Public`). The CLI is the **`xark`** binary (stable; published as the
  `xark-cli` crate); **`xark-frontend`** turns a circuit's wasm into R1CS.
* **Backend** — `xark-backend` (Groth16 setup/prove/verify, trusted setup,
  serialization) and `xark-verifier` (the `no_std` on-chain Solana verifier).
  Both are frontend-agnostic.
* **`xark-schema`** — `schema.json` and the one codec for input values (natural
  JSON forms to field elements and back), shared by the CLI, xark-wasm (so every
  generated client) and `client.wasm`. It needs only the BN254 scalar field and
  JSON, not the prover, so a client for another language binds just this.

Gadgets are **separate crates you add only when you need them**, all under
**`gadgets/`** — kept apart from the core toolchain so they're easy to fork or
use standalone. Shared circuit libraries: `xark-bits` (booleanity /
bit-decomposition), `xark-bignum` (non-native arithmetic, used by the EC
gadgets), `xark-curve` (curve macros), `xark-hash` (`Hash`/`Digest` types). Leaf
gadgets: `xark-poseidon`, `xark-poseidon2`, `xark-sha256`, `xark-keccak`,
`xark-mimc`, `xark-blake3`, `xark-blake2s`, `xark-aes`, `xark-pedersen`,
`xark-grumpkin`, `xark-secp256k1`, `xark-secp256r1`, `xark-ed25519`.

Adding a gadget is just a Cargo dependency:

```toml
# examples/poseidon/Cargo.toml
[dependencies]
xark = { path = "../../crates/lang" }
xark-poseidon = { path = "../../gadgets/xark-poseidon" }
```

```rust
use xark::prelude::*;
use xark_poseidon::hash;
// ... call `hash(..)` inside the `#[circuit]` fn and `require_eq` the result.
```

## Examples

`examples/` holds runnable circuits. The simple ones (`cube`,
`difference_of_squares`, `linear`, `inverse`) depend only on `xark`; the rest
pull in the gadget crates they exercise. Build any with `xark build
examples/<name>`.

## Status

> **Experimental.** Do not use generated Groth16 parameters or proofs in
> production until the lowering, serialization, and setup process have been
> independently audited. For real deployments run a multi-party phase-2 trusted
> setup (`xark`'s ceremony path); never ship a key produced in insecure dev mode.

* **Trusted setup** — `.ptau` phase-1 parsing with admissibility checks, phase-2
  setup derived from a `.ptau`, and a multi-contributor phase-2 MPC ceremony with
  Schnorr proofs of knowledge and δ-consistency pairing checks. See
  [`docs/trusted-setup.md`](docs/trusted-setup.md).
* **Verifier** — `xark-verifier` verifies proofs on Solana via the `alt_bn128`
  syscalls.

No external audit has been performed; see [`docs/audit-status.md`](docs/audit-status.md).

## Development

```bash
# Install the CLI (puts `xark` on PATH):
cargo install --path crates/cli

cargo test --workspace --release
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --all -- --check

# `crates/lang` is its own workspace, so its suites run separately:
cd crates/lang && cargo test --release
cd crates/lang && cargo test --release --test snapshot -- --include-ignored  # + heavy KATs
XARK_FUZZ_CASES=400 cargo test --release --test semantics_fuzz  # wider fuzzing

cargo xtask digests --check         # every example's circuit, unchanged
```

Toolchains and circuit reproducibility: [`docs/toolchain.md`](docs/toolchain.md).
Writing circuits — the supported subset and rejections: [`docs/subset.md`](docs/subset.md).
Architecture: [`docs/architecture.md`](docs/architecture.md).
Security walkthrough: [`docs/security.md`](docs/security.md).
