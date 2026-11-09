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
- `xark-bignum`: `mod_mul`, `mul_divmod` and `sub2` derive their bound `m − 1`
  from `m` (#62), and a typed `Bignum` or `fp!` input range-checks its limbs
  when it's read (#63). The `bignum`, `bignum_ops`, `bignum_wide`, `fp_mul`,
  `sub2` and `is_lt_check` examples change; `bignum_wide`, `fp_mul`, `sub2` and
  `is_lt_check` now range-check the limbs they take as `[Field; N]`. The curve
  gadgets don't change.
- `grumpkin_nova_fold` takes its inputs grouped by instance.
- A `Time`/`Days` input is checked to its range of steps, not just its bit width
  (`Days<2024, 2024>` is 366 days in 9 bits, and 366–511 were accepted): `zkyc`
  changes. `scalar_range` changes only in row order.
- The bit and hash gadgets take fewer rows, each proven sound in Lean over the
  exact rows it emits (`formal/`): XOR and OR with a constant fold to a linear form,
  `to_bits` computes bit 0 linearly, `xor3`/`maj3`/`chi`/`ch` are one row each,
  `reduce` has tight carries, and a Merkle level swaps with one product. Every
  example using SHA-256, Keccak, BLAKE, AES, Merkle or `to_bits` changes (27 of 71).
- ECDSA on secp256k1 and P-256, and EdDSA on Ed25519, are rewritten around proven
  gadgets: non-native multiplication by pseudo-Mersenne certificates over 8×32-bit
  limbs, fused double-and-add over signed digits, and fake GLV (ePrint 2025/933) with
  a fixed-base comb, each gadget proven sound over its rows. Fewer rows
  (`examples/secp256k1_ecdsa` is 227,168 in `xark inspect`); the hinted `R.x` is
  checked canonical (`< p`), and Ed25519 keeps the cofactored check of RFC 8032.
  Keys for the ECDSA and EdDSA examples must be made again.
- Grumpkin scalar multiplication (`scalar_mul`, `wide_scalar_mul`,
  `multi_scalar_mul`) and the Pedersen hash are rewritten as proven gadgets: one
  fused incomplete step per bit over signed digits, and windowed lookups from
  constant tables for Pedersen (3,318 → 772 rows). `scalar_mul` pins its own bits
  boolean. The seven Grumpkin and Pedersen examples change.
- The AES S-box is a select over its constant 256-byte table (687 → 34 rows),
  proven to output `S(x)` for every byte: `aes` is 145,944 → 15,360 rows,
  `aes256_gcm` 931,512 → 209,883. The five AES examples change.

### Highlights

- **Stable Rust only.** Circuits compile with any stable Rust from 1.89, and are
  identical on every supported version. The pinned-nightly `xark-rustc` is gone.
- **Typed inputs.** One `xark::Input` trait, implemented by `#[input]` or by hand,
  and everyday types (`Timestamp`, `Days<FROM, TO>`, `Text`, `Choice<E>`,
  `Bitfield<E>`, `Country`), in
  the circuit, in tests, on the command line and in clients.
- **Typed TypeScript clients.** `xark client` generates a client that proves and
  verifies through xark-wasm, with the circuit's types and its Rust constructors.
- **A streaming Groth16 prover** (`xark-groth16`) that never holds the whole
  constraint system or key in memory, with arkworks' Groth16 removed.
- **Failing checks name their source line**, everywhere inputs are checked.
- **Gadgets proven in Lean over the rows they emit.** 63 gadget templates (bits,
  hashes, AES, ECDSA, EdDSA, Grumpkin, Pedersen) are exported from the compiler and
  proven sound in `formal/`; CI fails when the code stops emitting a proven
  template or a production call isn't covered, and the secp256k1 ECDSA circuit is
  composed in Lean from its calls, its rows hashed against the compiler's. Every
  minimizer run on the keyed path writes a certificate a Lean checker accepts,
  proven to mean the keyed rows have the same solutions and eliminate no input.

### Changed

#### The npm package

- **`@blueshift-gg/xark`.** The JS runtime is published as
  `@blueshift-gg/xark`; imports move from `@blueshift-gg/xark-wasm` (and its
  `/client`, `/pool`, `/stream` subpaths) to the same subpaths of the new name.
  `@blueshift-gg/xark-wasm@0.2.x` stays published.

#### The toolchain and the frontend

- **Stable Rust only.** A circuit crate is compiled to wasm by the ambient stable
  `cargo` (1.89 or later, for the CLI too) and lowered by the new `xark-frontend`.
  The pinned-nightly MIR compiler `xark-rustc` is removed. A circuit's R1CS is the
  same on every supported Rust version (`cargo xtask digests` checks every example
  on 1.89, stable and beta in CI).
- **An integer input's range check is reused.** Its bits serve a later `to_bits`,
  bitwise operation or signed comparison of the input, so comparing two `i64` (or
  `Timestamp`) inputs costs what comparing two `u64`s does (68 constraints, not 202).
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
- **Everyday input types**: `Text`, `Choice<E>` (one variant of an enum) and
  `Bitfield<E>` (a set of them), each one field, with natural forms in tests
  (`"A1938274"`, `[US, GB]`), `--inputs` and clients, and the ISO 3166 `Country`
  enum. Each compares with `require_eq` and `==`, as does an `#[input]` struct.
  Checks are sized to the enum: a set splits into one bit per variant, and
  `Choice::require_in(set)` costs about 510 constraints over `Country`.
  `Text::parse` and the time types' `parse` return a `Result` for input you didn't
  write.
- **Times, sized to their range.** `Timestamp` is any moment as Unix seconds (an
  `i64`, as Solana's `Clock` and a JS `Date` hold it). `Time<UNIT, FROM, TO>` is a
  moment from the start of year `FROM` to the end of `TO` in whole `UNIT`-second
  steps (`SECOND` … `WEEK`), and `Days<FROM, TO>` its days: in the circuit an
  unsigned integer just wide enough for the range (`Days<1900, 2100>` is 17 bits),
  range-checked on entry and compared at that width. A moment inside a step is that
  step (rounded down, as Unix time does), and one outside the range is refused with
  the range named. Both read `"YYYY-MM-DD"`, an ISO 8601 date-time with a zone, or
  Unix seconds, are a JS `Date` in a generated client, and convert on the host
  (`Days::from_timestamp`, `years_before`), on chain too (`const fn`s, `no_std`).
  Leap years count where a date is read or written; every day is 86,400 seconds.
  `examples/zkyc` uses them: a private `Identity` checked against a public
  `Policy` built with `Policy::default().on(today).min_age(18).worth_at_least(500_000)`.
- **`bool` inputs.** A `bool` parameter or field is one field element, checked to
  be 0 or 1, usable as a condition and a value.
- **Struct fields are packed.** An `#[input]` struct's consecutive fields of known
  width (`uN`, `iN`, `bool`, a `Time`/`Days` or `Timestamp`, a `Choice` and a
  `Bitfield`) share one field element, in declaration order, the first in its lowest
  bits, until the next would pass 253 bits. In the circuit the element is split into
  its bits once, which is also every field's range check (so a packed `Choice` or
  `Days` is range-checked on entry), and each field reads its own bits. A `Field`, a
  `Text`, an array, a nested struct or a field marked `#[unpacked]` keeps its own
  leaves and starts a new run, and a field with no packable neighbour stays as it
  is. Fewer leaves means fewer public inputs (fewer multiplications for the
  verifier, less instruction data, a smaller verifying key) and fewer hash rounds
  over `to_fields()`, which returns the packed elements: order a struct's fields
  so that narrow ones sit together. The packed element is named by its fields
  (`policy.{born_by,min_net_worth}`) and `schema.json` records each field's bits,
  so clients, `--inputs` and decoded public inputs keep every field by name. A
  hand-written `Input` impl packs only what it declares with `Member::packed` and
  reads and writes with `Reader::member` / `Writer::member`.
- **Signed integer inputs.** An `i8`…`i128` parameter or field is one field
  element holding its two's complement (`-1i8` is `255`), range-checked to its
  width like a `uN`. Clients and `--inputs` take a negative number (or a `"-…"`
  string), and a generated client types it `I8`…`I128`.
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

- **What it writes:** one file, `<circuit>.ts`, with the circuit's `schema.json`
  inlined, so Node, a bundler and tsc all run it with no project settings, where
  `-o` says: a file, or a directory to write it in. A tuple struct's fields
  (`"0"`) and raw identifiers (`r#type`, named `type`) give a client that compiles. Names
  keep underscores around them (`_reserved`); a field JavaScript can't hold
  (`__proto__`, or `constructor` on a struct with Rust methods) is an error naming it. The
  types read like the circuit's: interfaces for input structs, enums as constants
  and a type (`Country.US` or `"US"`; `"XX"` doesn't compile), named aliases for
  xark's standard types (`Text`, `U8` … `U128`, `I8` … `I128`; a time is a `Date`), and arrays of up to 16
  elements as tuples, so a wrong length doesn't compile.
- **Proving and verifying:** `Zkyc.prover(source)` and `Zkyc.verifier(source)`,
  from a URL serving the build output or its bytes, each with only the methods it
  can run. They load xark-wasm themselves (node, web or workerd; `{ wasm }` passes
  your own). `{ pool }` proves on a worker pool from `@blueshift-gg/xark/pool`. `prove` returns a `Proof`: `toBytes()` is the proof as an exported
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
- The shared code is xark-wasm's `@blueshift-gg/xark/client`, and every value
  is encoded by one Rust codec, `xark-schema`, shared with the CLI, so a client and
  `xark prove --inputs` can't disagree.

#### Proving and verifying

- **Soundness is checked by tests, not by `xark prove`.** `Circuit::check`, which
  every `#[circuit]` validator calls, now also searches for witness variables the
  inputs leave free, so a circuit's tests fail on a "forgot to constrain a hint"
  bug that used to pass them. `check_satisfied` checks satisfaction only.
  `xark prove` only solves, proves and verifies the proof against the key: it no
  longer refuses an under-constrained circuit (`xark check --inputs` still runs the
  search). Proving ed25519 on an M3 Max takes 0.60 → 0.48 s.
- **Faster setup and proving.** Setup multiplies fixed bases with signed windows
  and batched affine additions, and keeps no extra copy of the circuit while it
  picks a key form; proving solves witnesses from the compiled templates, builds
  the row source while the witness solves, and computes `h` while the witness MSMs
  stream. On one 14-core machine: ed25519 setup 6.9 → 3.9 s and prove 8.6 → 6.8 s;
  secp256k1_ecdsa setup 4.9 → 2.9 s; aes256_gcm setup peak 3.1 → 2.8 GB. Keys,
  proofs and the keyed rows are unchanged.
- **A faster witness solve.** Bits skip the field multiply, a non-native inverse
  is a 256-bit safegcd, and the hint program compiles in parallel. Proving on an
  M3 Max: secp256k1_ecdsa 0.38 → 0.28 s, secp256r1_ecdsa 0.54 → 0.38 s, ed25519
  0.48 → 0.41 s. Witnesses, keys and proofs are unchanged.
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
  program's hash changes. The typed `Verifier::verify` does the same as
  `verify_instruction_data` now: it was the dearer of the two (78,538 against
  77,043 CU for one input of 81), and is now the cheaper (76,621).
- xark-wasm: `public_inputs_to_snarkjs` becomes `decode_public_inputs`; `Schema` and
  `VerifyingKey` parse a schema or key once.

#### The CLI

- `xark export` writes the verifier crate to `<crate>/<name>-verifier/` by
  default, named `<name>-verifier`, instead of `target/xark/<name>/verifier`, a
  crate named `verifier` that git ignored and `cargo clean` deleted. It is a nested
  crate with its own `[workspace]`, so the circuit crate neither builds nor
  packages it. `--out` still chooses; a build output outside a crate's `target/`
  keeps `verifier/` inside it.
- `xark export` takes any key and says how it was made, so `--allow-insecure` is
  gone. A key from OS randomness is a single-party trusted setup, sound unless
  whoever ran setup kept the randomness; a `--deterministic-rng` key can be forged
  by anyone with the seed, and export warns about it. The crate's `SETUP` constant
  and README carry it: `seeded`, `single-party`, `ceremony` (two or more
  contributors; a ceremony of one is `single-party`) or `unknown`, for a deploy
  script to check.
- `xark setup` has no `--insecure-dev-mode`: without a `.ptau`, it makes the key
  from the machine's randomness, as it already did by default. `--deterministic-rng`
  and `--domain smooth` work on their own, skip an auto-detected `.ptau`, and are
  refused with `--ptau-file`. The key's `metadata.json` says `"setup_mode":
  "single-party"`.
- `xark build` reuses an unchanged build: when the `xark` binary, the options, the
  `XARK_*` variables, the compiled module and every source file are the same as for
  the outputs in `target/xark/<name>/` (and those are untouched), it says so and
  skips lowering.
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

- `Bignum` up to 32 limbs (2752 bits at 86-bit limbs), enough for RSA-2048 (24
  limbs) and RSA-2560. Above 16 limbs a multiply's carries get one more bit of
  headroom (about 230 constraints per 24-limb multiply); up to 16 limbs the rows are
  unchanged. `xark_sha256::compress` and `h0` are public, for messages padded by the
  caller. The `bignum_wide` example is a 24-limb `mod_mul`.
- `Field::to_bits_canonical()`: the 254 bits of the canonical representative
  (in `[0, r)`), with a comparison against `r − 1`, so a value has one decomposition.
- `xark_merkle::cond_swap(bit, a, b)`: a conditional swap in one product.
- `require_eq` of two different constants (outside a witness branch) is a compile
  error, and `to_bits` of more than 253 bits is refused when it's built.
- `<Fn>Inputs::to_json()`, generated by `#[circuit]`: inputs built in Rust as the
  JSON `xark prove --inputs` takes, named as declared, like `inputs.example.json`.
  `xark prove --help` now says `--inputs` takes both those names and the camelCase
  ones a TypeScript client uses.
- `CircuitProof::to_solana_proof()`, `to_solana_public_inputs()` and
  `to_instruction_data()`: a proof made in Rust as an exported Solana verifier reads
  it, the same bytes as `xark export`'s `proof.solana.bin`,
  `public_inputs.solana.bin` and `instruction_data.bin`. Getting them took
  `xark-groth16`'s `solana` module and decoding the proof by hand.
- Untyped integer literals mix with `Field`: `x * 2`, `2 * x`, `1 - x`, `x += 1`,
  `Field::from(2)`, `0.into()`, `x == 0`. They failed to build, because a literal is
  an `i32` and only `u8`..`u128` had impls; `Field::from(2)` built in `cargo test`
  but not in `xark build`. A negative literal is refused in both builds (write
  `-Field::from(1u8)` for `p - 1`). Ordered comparisons still need a typed literal
  (`x < 5u32`), whose type gives the bit width.

- Tests that the `alt_bn128` syscalls and their Arkworks fallback reject a G1 point
  off the curve or with a coordinate `>= q`, and an off-subgroup G2 point in a
  pairing. The verifier relies on them for those checks, and nothing pinned it.

- `bind(x)`, for a public input that only the verifier supplies (a recipient, a
  nonce): one constraint that any value satisfies, which ties the proof to the
  value it was made for. Leaving such an input unused is refused at build time, and
  the error now points to `bind` instead of `require_eq`. `xark_hash::Hash` gets
  `to_fields()`. `examples/bound_recipient` binds a 32-byte address as two field
  elements, its 16-byte halves, so a program passes the address in unchanged.
- `xark_verifier::verify_groth16_batch`: several proofs of one circuit in a single
  pairing call. On chain each extra proof costs about 29k CU instead of 77k, so the
  compute limit allows about 46 proofs instead of 18. Needs
  `solana-nostd-alt-bn128` 0.1.3.
- `xark_poseidon2::native`: the Poseidon2 permutation and hashes on the host, from
  the same code as the gadget.
- `xark_prover::Circuit::check_satisfied(inputs)`: `check` without its search for
  witness variables the inputs leave free. `check_constrained` is the same as
  `check`.
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
  `difftest`, `publish`, and `wasm`, which builds xark-wasm's packages); `cargo xtask
  ci` runs every check a pull request gets on your machine, side by side (about 7
  minutes on 16 cores).

### Removed

- `xark-aes`'s `gf_mul`, `gf_square` and `gf_inv` (the S-box no longer computes
  `b²⁵⁴`).
- `xark-pedersen`'s `ec_add`, `ec_double` and `scalar_mul` helpers (the hash no
  longer uses them; `xark-grumpkin` has the point operations).
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

- A `Time` or `Days` input past the end of its range (a value its bits hold but no
  day of the type is) was accepted; it's refused as the input is read, packed or not.
- `fp!`'s `assert_nonzero` checked only that the limbs weren't all zero, so `m`
  itself, in range but not canonical, passed. It checks the value canonical first.
  The crate docs now say which results are canonical: only `mod_mul`'s and `sub2`'s.
- A `.ptau` whose τ is a root of unity of its size passed every admissibility check,
  and keys from it let any witness prove; it's refused.
- Ed25519 points decode as RFC 8032 says: `x = 0` with the sign bit set, `y ≥ p`,
  and a `y` with no `x` are refused, so each point has one encoding.
- A ceremony finalized with no contributions kept the δ `init` derives from the seed
  it records in `circuit_meta.json`, so anyone with the directory could forge
  proofs, yet it was marked production-safe and exported as `single-party` (#66).
  `xark ceremony finalize` refuses it; a key finalized before is labelled `seeded`,
  with a warning.
- `blake2s_hash_one_block` and `blake3_hash_one_block` take the length as a const
  generic (`::<LEN>`, at most 64) and require the bytes past it to be zero; a
  `Field` length up to 2³² and any tail were accepted, so one message had many
  digests (#72).
- The `--low-memory` spill file holds witness-derived data: on unix it's created
  readable by its owner only and unlinked at once, so it never outlives the
  process (#69).
- `metadata.phase2_seed_hash` is the SHA-256 of the seed's 32 bytes, not of the
  argument's text (#71).
- A hostile `circuit.xbc` fails to decode instead of aborting the process: counts are
  checked against the bytes left, variables and expansions are capped, a template
  call graph must be acyclic, and the panic hook is wrapped once rather than swapped
  around each decode, so overlapping decodes can't leave it removed (#64, #65, #68).
- Verifying keys, proofs and public inputs over 64 MiB are refused before they're
  read, and a `.ptau` file's header is checked before it's read whole (#73, #70).
- The `ec_incomplete` examples say why they need no on-curve check, and
  `enforce_on_curve` says when it's optional (#67).
- Two soundness holes in `xark-bignum`'s multiplication, each letting a prover make
  a valid proof of a wrong `(a·b) mod m` in a circuit that takes `m` or the limbs
  from the prover. The curve gadgets were not affected.
  - The remainder's bound `m − 1` was a separate argument nothing tied to `m`, so a
    larger one admitted `r + m` (#62). `mod_mul`, `mul_divmod`, `sub2` and
    `Bignum::{mul, sub2}` now take only `m` and derive the bound (`minus_one`).
  - A limb `≥ 2^BITS` turned the column identity into a congruence mod BN254's
    field (#63). A typed `Bignum` or `fp!` input now range-checks its limbs when
    it's read; `fp!(unchecked_input …)` skips that for code that checks its inputs
    itself, as the curve macros do. Limbs a circuit takes as `[Field; N]` still
    need `range_check_limbs`, as the crate docs say.
- Two soundness holes in `witness_begin()`/`witness_end()` regions, each letting a
  prover make a valid proof of a statement the circuit rejects. No shipped circuit
  hit either (every digest is unchanged).
  - A `Field` comparison (`==`, `!=`, `lt`, …) made in a region lost its rows but
    was still trusted as a 0-or-1 `bool`, so a branch or select on it after the
    region could take any value (#59). It now keeps its rows, as native integer
    ops do.
  - An arm of a witness branch that panicked inside a region left the region open,
    and every constraint after the branch was dropped (#58). Each arm now starts in
    the region state the branch was reached in, and a region that would straddle a
    branch is refused.
- Malformed input is an error, not a panic: a row-file window index out of range,
  a malformed or wrongly laid out row stream, a proving key whose lengths overflow,
  and an MSM work item or accelerator result of the wrong size or with points that
  don't decode.
- `xark` found a directory named `*.ptau` as a powers-of-tau file; it now looks at
  files only. A crate whose `name = "…"` line ends in a comment got the comment
  in its build directory's name.
- `xark check --inputs` refused a circuit with witness-only scratch
  variables no constraint references (the `secp256k1_ecdsa` example's GLV
  decomposition) as under-constrained, while `xark check` passed it. Such a variable
  changes no row and no output, so it is ignored, as the test harness already did.
- The generated TypeScript client runs in Node's own ESM loader. It imported its
  schema as `./cube.schema`, with no extension, which only a bundler resolves (Node:
  `ERR_MODULE_NOT_FOUND`). The schema is now inlined: `xark client` writes one file,
  `<circuit>.ts`, and no longer a `<circuit>.schema.ts` (an old one can be deleted).
- Outside a browser, a client's `prover(from)`, `verifier(from)` and `ready(from)`
  given a path or a `file:` URL say to pass the files' bytes, and show the
  `readFileSync` calls that do it. A path was refused as "relative, … pass an
  absolute URL" (even an absolute one), and a `file:` URL failed with "fetch
  failed". The runtime still only fetches, so it has no Node-only code.
- The next steps `xark setup` and `xark client` print can be followed as written:
  - setup always writes `inputs.example.json` and says to replace its placeholders,
    instead of a runnable-looking `--inputs '{"x": "<field>"}'` that failed with
    "is not a decimal or 0x-hex number". A placeholder left in is now named: "still
    the placeholder "<field>" from `inputs.example.json`".
  - client's `prover(…)` hint and the generated client's docs point at the build's
    directory, named after the package, not the circuit (`target/xark/my-cube/`, not
    `target/xark/cube/`).
  - setup says how it made the key and where to find a multi-party ceremony.
- A `#[circuit]` array parameter's length may be a `const`: `Private<[Field; DEPTH]>`
  failed with "array lengths must be integer literals". The circuit is the one the
  literal gives (`examples/merkle` now uses `const DEPTH`, same digest). A generic
  entry (`fn c<const N: usize>`) is refused with a pointer to a `const` or a generic
  helper; its generics used to be dropped silently.
- Two `#[circuit]` functions in one crate fail with "the crate has 2 #[circuit]
  functions (src/lib.rs:2, …); xark builds one circuit per crate", not a clash of the
  internal `__xark_main` / `__XARK_ENTRY` symbols. The rule is now documented.
- The `xark` crate docs said `^` on `Field` is exponentiation. It is boolean XOR, but
  it didn't check that its operands are 0 or 1, so `x ^ Field::from(3u8)` built and
  constrained `3 - 5x`, not `x³`. The example now uses `x.pow(3)` and is compiled as a
  doctest. `^` now checks each operand is a bit: free when the compiler already knows
  it is one (a bit of `to_bits`, a XOR/AND/OR of bits, a constant 0 or 1), one row
  otherwise. A constant other than 0 or 1 is a build error that points to `uN` or
  `to_bits` for bitwise XOR and to `pow` for a power. `^=` and `^` with an integer
  literal work too. `Field::xor` stays unchecked. No example's rows change.
- `xark build` checks that the `circuit.xbc` it writes expands to exactly the
  circuit it lowered, and fails before writing anything if not. The check used to
  run only in xark's own tests, so a compaction bug on a user's circuit would have
  shipped silently. It adds 0–15% to a build (1.8s of 12s on `secp256r1_ecdsa`).
- `Field::to_bits::<N>` of a constant takes the bits of its field element. A constant
  above `p/2` (e.g. `2^253 - 1`) is stored as a negative integer, so it failed to
  build with "does not fit in N bits", and in a witness branch it ruled the branch
  out, so honest witnesses taking it were rejected.
- `xark ceremony verify` and `finalize` check the whole of the shipped keys, not just
  δ. They took any α, β, γ and public-input points, so a coordinator could ship `γ =
  δ` (which lets anyone prove anything) behind an honest contribution chain and have
  it marked `production_safe`. They now recompute the keys `init` made from the
  circuit, the `.ptau` (a new required `--ptau-file`) and the phase-2 seed, which
  `init` records in `circuit_meta.json`, and require the shipped keys to be those
  with only δ changed, by exactly the chain. `baseline_delta_g1.bin` is checked
  against them too. A ceremony begun with an older xark (no recorded seed) can't be
  checked: start it again.
- Native integer arithmetic inside a `witness_begin()`/`witness_end()` region is
  constrained. It used to be free there like `Field` ops, so an integer computed in
  the region was trusted afterwards with no range proof (a `u32` quotient could be
  `3⁻¹ mod p`, proving `1 = 3·q`). And because the optimizer may merge integer code
  across the region's ends, a value recomputed after the region could be the
  region's unconstrained one. No example or gadget circuit changes.
- A circuit with a `u128` input beside a narrower integer input (`struct { x: u8,
  z: u128 }`, or two parameters) no longer crashes the build with "index out of
  bounds".
- `proveStreaming` without `options.r1cs` proves with the rows its key was made
  for, as `prove` does. A `minimized` key (which `xark setup` picks for some
  circuits) used to fail there while plain `prove` worked. A push-driven proof
  (`beginStreamingProof`, `proveFromStream`) still needs `r1cs` for such a key.
- A client function taking or returning a type alias (`type Address = Hash`), or a
  path to a type (`xark_hash::Hash`), reaches the generated client. It used to be
  skipped with a warning, because the client read each type as written; it now reads
  the type's `Input::TYPE`.
- `xark export` no longer needs a proof. Without one, or with one made for another
  key, it writes the verifier crate without its self-test (and says why in the
  second case). A proof named with `--proof` must still verify.
- `xark-verifier` no longer turns on `static-syscalls` by default. An SBPFv3 build
  is byte-identical without it (the v3 target sets it), and an SBPFv0 build now
  works with the default features, where it used to build a `.so` the loader
  rejects.
- `xark ceremony finalize` records what the keys were made from, as `xark setup`
  does: `num_constraints` (was 0), `ptau_source` (was null), `r1cs_form` and
  `qap_domain_size`. A ceremony begun with an older xark still finalizes, without
  the constraint count or the `.ptau` name.
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
