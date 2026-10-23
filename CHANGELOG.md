# Changelog

Before 1.0, a release that changes any circuit bumps the minor version, and each
such circuit is listed under "Circuits that changed": its keys must be made
again. See the toolchain policy in [docs/toolchain.md](docs/toolchain.md#toolchain-policy).

## 0.3.0

### Circuits that changed

**Every circuit.** 0.3 compiles circuits with a new frontend (below), so every
circuit built with 0.2 changes: rebuild and make new keys. Beyond that, these
gadgets now check more:

- `xark-ed25519` and `xark-secp256k1`: points must have canonical coordinates
  (each `< p`), so a point can't be given in two forms. About +1,000 constraints
  for an EdDSA verify and +560 for an ECDSA verify.
- `xark-secp256r1`: the same check, +3 constraints.
- `xark-bignum`: `mod_neg` gave a wrong result for some inputs at full 256-bit
  width; `mod_add` could overflow; `mod_neg(0)` is fixed.
- `grumpkin_nova_fold` takes its inputs grouped by instance.

### Highlights

- **Stable Rust only.** Circuits compile with any stable Rust from 1.89, and are
  identical on every supported version. The pinned-nightly `xark-rustc` is gone.
- **Typed inputs.** One `xark::Input` trait, implemented by `#[input]` or by hand,
  and everyday types (`Date`, `Text`, `Choice<E>`, `Bitfield<E>`, `Country`), in
  the circuit, in tests, on the command line and in clients.
- **Typed TypeScript clients.** `xark client` generates a client that proves and
  verifies through xark-wasm, with the circuit's types and its Rust constructors.
- **A streaming Groth16 prover** (`xark-groth16`) that never holds the whole
  constraint system or key in memory, with arkworks' Groth16 removed.
- **Failing checks name their source line**, everywhere inputs are checked.

### Changed

#### The toolchain and the frontend

- **Stable Rust only.** A circuit crate is compiled to wasm by the ambient stable
  `cargo` (1.89 or later, for the CLI too) and lowered by the new `xark-frontend`.
  The pinned-nightly MIR compiler `xark-rustc` is removed. A circuit's R1CS is the
  same on every supported Rust version (`cargo xtask digests` checks every example
  on 1.89, stable and beta in CI).
- **What compiles** is documented from the new frontend in
  [docs/subset.md](docs/subset.md). Branches on witness values, small witness
  indices and short witness-bounded loops work. Constructs that can't compile
  soundly (a witness-sized `memory.grow`, a circuit input declared inside a witness
  branch, a loop whose length depends on a witness and isn't provably short) are
  refused with a message naming the source line.
- **Circuit crates can use `std`.** `#![cfg_attr(xark, no_std)]` is no longer
  needed (`xark init` leaves it out): circuit code can use `std` and crates that
  assume it. `xark` and the gadgets stay `no_std` libraries, and the on-chain
  verifier doesn't depend on any of this.
- **Circuit code runs natively on the host.** In a host build the `Field`
  operations compute instead of panicking: arithmetic on BN254, comparisons, and
  every hint as the solver computes it. A failed `require`/`require_eq` panics at
  the caller's line, and `witness_begin`/`witness_end` regions skip their checks as
  a circuit does. So a helper such as `id.commitment()`, or a whole gadget
  (`xark_sha256::sha256`, ECDSA `verify`), runs in tests and services. Only
  hint-less `Field::advice()` has no host value.
- **Packing narrow values into a word is free.** An `|` (or `^`) of values whose
  bits can't overlap (`c << 16 | b << 8 | a`) is their sum, and reading a piece
  back (`>>`, a mask, `/` or `%` by a power of two, `as u8`, a byte through memory)
  takes it off that sum instead of splitting the word into bits: such a round trip
  on three `u8` inputs costs 28 constraints rather than 151.
- **Failing checks name their source line.** `xark build` writes `sources.json`
  (which statement each constraint came from), and inputs that fail a check report
  that statement in Rust tests, `xark prove`/`check`, xark-wasm and clients:
  `src/lib.rs:96:20 id.nationality.require_in(policy.allowed);` rather than a
  constraint number.
- **`cargo test` rebuilds a stale circuit**, one older than any local source it
  came from (path-dependency gadgets and `xark` included, from cargo's dep-info),
  instead of testing the previous build, and one built over another field
  (`--field`). Without an `xark` to rebuild with, it warns (for another field, the
  tests fail, saying why).

#### Inputs

- **One `Input` trait for every circuit input.** A type is a circuit input when it
  implements `xark::Input`: its `TYPE` (how clients see it, built from a fixed set
  of standard types) and `read`/`write` of its field elements. The one impl serves
  the circuit build and the host (the prover's inputs, `to_fields()` for hashing,
  decoding public inputs), so a hand-written impl is a few lines with no `cfg`s.
  `#[input]` implements it for a struct (`#[input(number(bits = B))]` or
  `#[input(bytes)]` give it a standard encoding), `xark::Enum` for a fieldless
  enum, and client functions for an `impl` block. It derives `Clone`, `Copy` and
  `Debug` (and `PartialEq`, `Eq` on an enum) unless listed;
  `#[input(no_derive)]` leaves them to you. It replaces `#[derive(CircuitInput)]`,
  `#[derive(Transparent)]` and `NativeInput`.
- **Everyday input types**: `Date`, `Text`, `Choice<E>` (one variant of an enum)
  and `Bitfield<E>` (a set of them), each one field, with natural forms in tests
  (`"1990-01-01"`, `[US, GB]`), `--inputs` and clients, and the ISO 3166 `Country`
  enum. Each compares with `require_eq` and `==`, as does an `#[input]` struct.
  Checks are sized to the enum: a set splits into one bit per variant, and
  `Choice::require_in(set)` costs about 510 constraints over `Country`.
  `Date::parse`/`Text::parse` return a `Result` for input you didn't write.
  `examples/zkyc` uses them: a private `Identity` checked against a public
  `Policy` built with `Policy::default().on(today).min_age(18).worth_at_least(500_000)`.
- **`bool` inputs.** A `bool` parameter or field is one field element, checked to
  be 0 or 1, usable as a condition and a value.
- **`schema.json`.** `xark build` writes every input's name, visibility and type,
  and the public inputs in proof order. A build fails if one type name would stand
  for two different types, since clients look types up by name.
- **Natural input forms, read one way.** `xark prove/check/verify --inputs` read
  every value against `schema.json`, in its natural form: a date, a variant name,
  an Ed25519 key or a hash as `0x`-hex bytes (decompressed for you), a scalar as a
  number. A missing `schema.json` asks for `xark build` instead of guessing how a
  value splits into leaves. `xark setup`'s next step shows a template in these forms
  (or writes `inputs.example.json`), and `xark inspect` lists inputs by name and
  type.
- **Bytes are little-endian where they're an integer.** A wide integer (a limbed
  number: a scalar, a bignum) given as a list of bytes is read little-endian, like
  `Field::from_le_bytes`. A hex string is a number, most significant digit first.
- **Field inputs must be field elements.** A `Field` input outside `0 <= x < p` is
  rejected instead of silently reduced, everywhere inputs are read. A value that
  wraps proves a different number than the one written (a 256-bit hash passed as a
  `Field`). `xark_prover::hex_to_field_decimal` is replaced by `field_input_decimal`.
- **Typed host inputs.** The validator `#[circuit]` generates (and its `<Fn>Inputs`
  struct) takes typed values: a `Field` anything that converts (`cube(3, 27)`, an
  `ark_bn254::Fr`, a decimal or `0x`-hex string), a gadget type its natural form.
  A number string reads the same everywhere (`--inputs`, the host validator, a
  client's `Field`): decimal digits or `0x`/`0X` hex, nothing else (no `+` or `_`).
  Input structs can hold gadget types, and parameters can be arrays of them.
- **One dependency per circuit crate.** `xark` re-exports the prover as
  `xark::prover` (host builds), so a circuit crate needs only `xark`.
- A constant `Field` (`Field::constant`, `from_le_bytes`, `from_be_bytes`) is
  reduced mod p when made, so `to_decimal()` gives the value the circuit sees.

#### TypeScript clients

`xark client` now generates a typed client; in 0.2 it scaffolded a snarkjs
verification starter, and the `xark-client` npm package is removed.

- **What it writes:** `<circuit>.ts` and the `<circuit>.schema.ts` it imports
  without an extension (the circuit's `schema.json` as a module; a bundler, Turbopack
  included, and tsc's "bundler" resolution read it with no project settings), where
  `-o` says: a file, or a directory to write them in. A tuple struct's fields
  (`"0"`) and raw identifiers (`r#type`, named `type`) give a client that compiles. Names
  keep underscores around them (`_reserved`); a field JavaScript can't hold
  (`__proto__`, or `constructor` on a struct with Rust methods) is an error naming it. The
  types read like the circuit's: interfaces for input structs, enums as constants
  and a type (`Country.US` or `"US"`; `"XX"` doesn't compile), named aliases for
  xark's standard types (`Day`, `Text`, `U8` … `U128`), and arrays of up to 16
  elements as tuples, so a wrong length doesn't compile.
- **Proving and verifying:** `Zkyc.prover(source)` and `Zkyc.verifier(source)`,
  from a URL serving the build output or its bytes, each with only the methods it
  can run. They load xark-wasm themselves (node, web or workerd; `{ wasm }` passes
  your own). `prove` returns a `Proof`: `toBytes()` is the proof as an exported
  Solana verifier reads it (256 bytes, `Proof::from_le_bytes` on chain), and
  `toBytesCompressed()` is half the size; `verifier.verify(bytes, required)` reads
  either and checks it proves the public inputs you require. A malformed verifying
  key fails when the verifier is made.
- **The circuit's Rust in TypeScript:** `#[input]` on an `impl` makes its methods
  client functions, from any crate; on a trait's `impl` too (`impl Default for
  Policy` gives `Policy.default()`). Parameters may be `Self` or `&T`; a generic
  function is refused where it's written, since a client couldn't choose its type. `xark client` builds the crate's host code as
  `client.wasm`, so `Policy.default().on(day).minAge(18)` and `Identity.commitment(id)` run the
  crate's Rust, chaining as in Rust. A method named like a field stays
  `Policy.method(value, …)`, and `xark client` warns. A Rust panic is an exception
  with its message. `await Zkyc.ready(url)` loads `client.wasm` on its own.
- **Bytes are a `Uint8Array`**, given and decoded; `fromHex` and `toHex` (exported
  by every client) convert hex.
- **Field elements** are a `Field` class: `new Field(x)` takes a `bigint`, a safe
  integer, a decimal or `0x`-hex string, little-endian bytes (`Field.fromBeBytes`
  for big-endian) or another `Field`, and throws unless it's below the modulus. A
  field input (`FieldInput`) also takes a plain integer, checked the same way, and a
  number past 2^53 is refused rather than rounded.
- **One proof format for Solana and everywhere else:** a client's `toBytes()` is
  byte for byte what `xark export` makes of the same proof, and `xark verify`
  (`--proof`) and xark-wasm's `verify` read a proof in either form (xark-wasm's
  `solanaProof` converts; the encoders and the checked decoder are
  `xark_groth16::solana`, re-exported from `xark_backend::solana`).
- **Pinning a prover:** `Circuit.digest` is the circuit the client was generated
  from, and `prover(from, { digest })` refuses a `circuit.xbc` with another one
  (xark-wasm's `circuitDigest` computes it). A verifier pins its verifying key:
  `verifier(from, { keyHash })` refuses a `vk.bin` with another sha256, which
  `xark setup` and `xark ceremony finalize` print and record in `metadata.json`
  (`verifying_key_sha256`).
- **Loading and proving faster:** a circuit fetches `client.wasm` once, however
  many provers and verifiers are made from its URL, and `prover.preload()` keeps
  the proving key decoded (about 2.2× `pk.bin` in memory), so each proof skips
  decoding it: about half the proving time of a small circuit. xark-wasm's
  `ProvingSession` is that decoded circuit and key, one per prover.
- **Typed errors:** a refused input throws an `InputError` with its `path` in the
  caller's names (`id.netWorth`, or a Rust function's `allowed`), and inputs that
  fail a check a `CheckFailed` with the statement's `site` (file, line, column,
  text, the functions it called into). A JS `Set` goes as a list; a value that
  can't be sent (a `Map`, an `ArrayBuffer`) is an `InputError` too, not `{}`.
  `verify` is `false` for a bad proof and throws for public inputs that don't fit.
- **Hashing as the circuit does:** `prover.fields("Identity", id)` gives a value's
  field elements and `prover.poseidon2(fields)` hashes them.
- The shared code is xark-wasm's `@blueshift-gg/xark-wasm/client`, and every value
  is encoded by one Rust codec, `xark-schema`, shared with the CLI, so a client and
  `xark prove --inputs` can't disagree.

#### Proving and verifying

- **A streaming Groth16 prover.** `xark prove` uses `xark-groth16`, which never
  holds the whole constraint system or proving key in memory, always from
  `circuit.xbc`. Keys and proofs are compatible with the arkworks path
  (byte-identical for the same randomness), and existing key and proof files load.
- **arkworks' Groth16 removed.** `xark-groth16` owns key generation, proving,
  verification and the `Proof`/`VerifyingKey`/`ProvingKey` types; arkworks is only
  the BN254 arithmetic. `xark_backend::{setup, prove, stream_prove}` are gone,
  `xark_backend::ptau::setup_from_ptau` takes a constraint source,
  `xark_prover::XarkCircuit` no longer implements arkworks' circuit trait, and
  verification rejects a wrong number of public inputs.
- **Proving from Rust:** `xark_prover::circuit("name").prove(inputs)` proves with the
  built circuit and its `pk.bin` and returns the same bytes `xark prove` writes;
  `prove_with_key` takes another key, and `prove_dev` makes throwaway keys.
  `prove_only`, `prove_and_verify` and `check_fields` are no longer public.
- The on-chain verifier skips the scalar multiplication for public inputs of 0, 1
  or up to 128: booleans, enum values and counts verify cheaper (up to 38% less
  compute when all are small, about 0.5% more when all are large). The reference
  program's hash changes.
- xark-wasm: `public_inputs_to_snarkjs` becomes `decode_public_inputs`; `Schema` and
  `VerifyingKey` parse a schema or key once.

#### The CLI

- `xark build` prints the circuit digest (a fingerprint of the R1CS, written to
  `target/xark/<name>/digest`) and the three source lines that cost the most
  constraints.
- `xark profile` ends with a breakdown by kind of constraint, saying what each is
  and how to have fewer, and the costliest functions including what they call
  (`commitment → hash → perm`); `--json` carries both. `--html` writes
  `profile.html`: the same breakdown, the costliest lines opening onto their call
  chains, and the circuit's source with each line shaded by what it costs.
- `--field` (`xark build`, `xark profile`) takes `bn254` or a prime modulus in
  decimal; anything else (a typo, a composite) is an error before building. A build
  over another field suggests `xark profile` next, and `setup`, `prove` and `client`
  rebuild it for BN254 (keys, proofs and clients are BN254's), or refuse one built
  elsewhere (`--out`); `inspect` reads it as built.
- `xark clean` also removes the wasm build caches (`target/xark-wasm`, and
  `target/xark-client` from `xark client`).
- **Builds are reused while current, and never used stale.** `xark check
  --inputs`, `xark test` and `xark profile` skip their build when no source of the
  circuit has changed since (and the field and `xark` are the same). `xark prove`,
  `xark setup`, `xark client` and `xark inspect` build a circuit that's missing, or
  rebuild one older than its source, saying which file changed (so a proof or key is
  never of the old circuit; `prove` then asks for `xark setup` if the circuit
  changed), and `xark export` warns that its keys may be for an older circuit.
- **`--out` is a directory** for `xark setup`, `xark prove` and `xark export`, with
  a warning when it isn't empty (`prove --out` was the proof's path, with
  `public_inputs.bin` put beside it; `export` still never replaces a `Cargo.toml` or
  `src/lib.rs` it didn't write). Their next steps point at what they wrote there:
  `--proving-key <dir>/pk.bin` after `setup`, `--proof` and `--public-inputs` (and
  the key beside a `--proving-key`) after `prove`.
- **A key fits every build of its circuit.** Keys record the circuit digest
  (`metadata.json`'s `digest`) beside `circuit.xbc`'s hash. `prove`, `verify` and
  `export` accept a key from another build with the same digest, such as the same
  circuit compiled by another Rust version (which can store repeats differently,
  as 1.89 does for the Ed25519 and P-256 examples), instead of asking for a new
  `xark setup`. A minimized key's `r1cs.stream` is marked with the digest too, so
  `prove` doesn't rebuild its rows for another build and xark-wasm doesn't refuse
  them. `xark inspect` shows both fingerprints.

### Added

- `xark_verifier::verify_groth16_batch`: several proofs of one circuit in a single
  pairing call. On chain each extra proof costs about 29k CU instead of 77k, so the
  compute limit allows about 46 proofs instead of 18. Needs
  `solana-nostd-alt-bn128` 0.1.3.
- `xark_poseidon2::native`: the Poseidon2 permutation and hashes on the host, from
  the same code as the gadget.
- `xark_prover::Circuit::check_constrained(inputs)`: `check`, plus a search for
  witness variables the inputs leave free (the "forgot to constrain a hint" bug).
- `xark-schema`, `xark-frontend` and `xark-groth16` are published.
- Exhaustive witness search (`xark_ir::witness_search`), and `cargo xtask difftest`
  on every pull request: each example must accept exactly the inputs it should,
  with exactly one witness. It covers every example but the two ECDSA circuits
  (searched block by block), the whole ed25519 verify included.
- Every crate declares `rust-version = "1.89"`, and CI builds the workspace on 1.89.
- The slow CI checks (known-answer vectors, the EC gadget vectors, the example
  sweep, a publish rehearsal) run on every pull request instead of nightly. A
  weekly run keeps what can fail with no code change: the digest check on Rust
  stable and beta, and a long fuzz run. Generated clients and xark-wasm's streaming
  prover are tested in CI. Repository tasks are `cargo xtask` (`digests`,
  `difftest`, `publish`, and `wasm`, which builds xark-wasm's packages).

### Removed

- `xark-rustc` and the pinned nightly.
- snarkjs output: `snarkjs-verification_key.json`, `snarkjs-proof.json`,
  `snarkjs-public.json`, and xark-wasm's `proof_to_snarkjs`. Verify in JavaScript
  with xark-wasm or a generated client.
- The proof bundle `<name>-<hash>.proof.json` (it duplicated `proof.bin` and
  `public_inputs.bin`); `xark prove` prints the proof's SHA-256 fingerprint.
- `--r1cs` / `--circuit` (reading `r1cs.json` / `circuit.json`) from `prove`,
  `setup`, `verify`, `inspect` and `ceremony init`; `prove --stream` (it always
  streams); `setup --cache` and `r1cs.min.wcz`. `xark build --emit-json` still
  writes the JSON as a debugging view.
- `xark export`'s `client_call_example.rs` (its dependencies didn't compile
  together); the generated README says how to send `instruction_data.bin`.
- The `xark-client` npm package.

### Fixed

- A circuit's generated test function (`zkyc_circuit(...)` in `cargo test`) looks
  for the build where `xark build` writes it, under the package's name: a crate
  named `my-circuit` (as `xark init my-circuit` makes it) said "has not been built".
- `xark ceremony contribute`, `verify` and `finalize` on a directory that isn't a
  ceremony (a typo) say so and how to start one, instead of "No such file or
  directory (os error 2)"; a damaged ceremony key names the file.
- Builds of one crate at once (an editor's `xark check` beside `xark build` in a
  terminal) no longer fail with "reading …/<crate>.wasm: No such file or
  directory": each holds the build directory until it has read its `.wasm`.
- `require_eq` accepts an integer or decimal string on either side
  (`require_eq(7u64, x)` compiles).
- The verifier docs no longer suggest `verify_strict` makes proof bytes safe as a
  replay or dedup key: Groth16 proofs are re-randomizable. They now say to put
  replay protection in the public inputs (a nullifier, nonce or signer).
- `xark setup` and `xark ceremony contribute` write their files under temporary
  names and swap them in at the end, so an interruption can't leave a new dev key
  beside metadata marking it production-safe, or keys the ceremony's chain doesn't
  explain. `ceremony contribute` refuses a finalized ceremony, and `ceremony init`
  refuses a directory holding one unless given `--force`.
- `xark export --out` refuses to overwrite files it didn't generate (it could
  replace your own crate's `Cargo.toml` and `src/lib.rs`).
- `xark build`, `test`, `check` and `profile` find the crate from inside it, as cargo
  does, and every command reports a mistyped path (`no such directory: …`) instead
  of building the current directory or passing it to `cargo test` as a filter.
- `xark init` refuses names `cargo new` refuses and suggests one that works, names
  the crate after the last path component, and makes a crate that passes its own
  `xark test`.
- `xark test` passes its arguments to `cargo test` as given (`xark test . -- --list`).
- `xark prove` with a proving key older than the circuit says to run `xark setup`
  again, and a proof that fails its self-check says whether the inputs don't
  satisfy the circuit or the key is for another one (`ProveError::Unsatisfied`).
- A missing input is named (`missing input `result``), an out-of-range `uN` input
  is named before solving, and a whole number written as a JSON float (`1e3`) is
  accepted.
- `xark verify` reports a public-input count mismatch as such, and suggests
  `xark prove` only when `public_inputs.bin` is missing.
- Errors in a circuit crate's tests show in an editor: `xark check
  --message-format=json` (rust-analyzer's command) runs `cargo check --all-targets`
  first.
- `xark doctor` warns when the `xark` that `cargo test` and rust-analyzer run is a
  different version, and says what it's for.
- `xark clean` no longer follows symlinks and skips `node_modules`.
- Solving a circuit multiplied out every `A·B = C` row, so two 500-term sides made
  250,000 terms (a 12k-constraint Grumpkin circuit took 27 GB and 80 s); such rows
  are factored through a helper variable (0.7 GB, about 2 s).
- `xark_test_harness::compile_file` builds debug notes and variable names only when
  it writes the JSON views: `grumpkin_ipa_fold`'s tests went from 34 GB and 106 s
  to 3.6 GB and 7 s.
- A circuit importing `Field` by name (`use xark::{Field, …}`) no longer gets an
  `unused import` warning on host builds.
- Smaller fixes to messages and `--help`: `xark ceremony` documents its flags,
  default artifact paths are given as `target/xark/<name>/…`, the builds that other
  commands run don't print `xark build`'s next-step hint, and `xark setup` says a
  key needs xark's provers only for a mixed-radix QAP domain.
