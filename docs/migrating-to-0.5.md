# Migrating from 0.4 to 0.5

0.5 changes the client crate `xark export` writes: a new one is named
`<name>-client`, it carries a circuit's proof and public inputs as one type, and
its `prover` feature proves on a host. A circuit crate can also depend on another
one for its input types. **No circuit changed**: every digest is the same, so keys
made with 0.4 still verify, and a deployed program keeps working.

**Your code doesn't have to change.** Update the versions as below, and a project
from 0.4.0 builds under 0.5: `xark export` over an earlier export keeps that
crate's name, so `<name>-verifier` and the programs depending on it stay as they
are. The one behavior to check is that a prover no longer verifies its proof
before returning it unless you ask ([below](#verify-a-proof-before-its-returned)).
The rest of this guide is what you can take up, and the one name `xark add` now
refuses.

## Update xark

```sh
cargo install xark-cli --version 0.5.0 --locked
```

```toml
# xark.toml, at a project's root: the release it's made with (until it says 0.5,
# every command warns that this xark is another release)
[project]
xark = "0.5"
```

```toml
# The circuit's Cargo.toml (and any gadget crates, at the same release)
xark = "0.5"
xark-poseidon2 = "0.5"
```

```sh
npm install @blueshift-gg/xark@0.5
```

Then run `xark build` at the project's root (or `xark export` beside a circuit
crate) and commit what it writes: the client crate gains the types below.

## Verify a proof before it's returned

In 0.4 every prover checked its proof against the proving key's verifying key
before returning it, so inputs that break a constraint were an error naming the
constraint and its source line. In 0.5 the check is off by default: a proof's
soundness doesn't depend on it, and a verifier checks the proof anyway. Without
it, such inputs give a proof that no verifier accepts, and `xark prove` prints
`✅ Proof produced` as for any other.

Where you relied on that error (a test that bad inputs are refused, or a UI that
shows the failing check), ask for the check. It costs one pairing, under a
millisecond natively:

```sh
xark prove --verify --inputs '{"secret": 3, "result": 10}'
```

```ts
// A generated TypeScript client
prover.prove(inputs, { verify: true }); // throws a CheckFailed naming the statement

// @blueshift-gg/xark directly
prove(xbc, pk, inputs, sources, { verify: true });
proveStreaming(xbc, pk, inputs, { verify: true, sources });
session.prove(inputs, { verify: true });
```

From Rust, `xark_groth16::ProverConfig { self_check: true, .. }`. A Rust client
crate's `prover::Prover` checks the inputs against every constraint before
proving, as before, so it still refuses bad inputs without the check.

## Circuit names

`xark add circuit` refuses a name ending in `-client` or `_client`, since the
circuit's client crate is `<name>-client`. A name ending in `-verifier` is allowed
again. A circuit you already have keeps building whatever its name.

## Rename the client crate (optional)

A new client crate is `<name>-client`; yours keeps `<name>-verifier` until you
rename it. First point the program at the new name, and rename its `use` lines
(`my_circuit_verifier::` to `my_circuit_client::`):

```toml
# programs/my-circuit/Cargo.toml
my-circuit-client = { path = "../../clients/my-circuit/rust" }
```

Then delete the crate and build. The key is in `keys/`, so the crate is written
again from it, embedding the same verifying key:

```sh
rm -r clients/my-circuit/rust
xark build
```

A circuit crate outside a project does the same with `xark export --crate-name
my-circuit-client`, or by deleting `clients/rust/` and exporting again.

## Take the proof as one type (optional)

The client crate has a `<Name>Proof` struct, named after the circuit as the
TypeScript client is (`my_circuit` gives `MyCircuitProof`): the 256-byte proof
and the public inputs by name, `no_std`. It implements `xark_verifier::Verifiable`,
whose `verify()` returns `Result<(), XarkError>`.

When every public input is a byte array (`[u8; N]`: keys, hashes, nullifiers),
`MyCircuitProof::try_from(data)` parses `proof || public inputs` from instruction
data, and refuses data that is too short (`XarkError::Truncated`) or too long
(`XarkError::TrailingBytes`). The instruction parsing `xark add program` wrote
becomes:

```rust
// Before: split, check the length and copy by hand
let (proof, rest) = data.split_first_chunk::<256>().ok_or(ProgramError::InvalidInstructionData)?;
if rest.len() != NUM_PUBLIC_INPUTS * 32 {
    return Err(ProgramError::InvalidInstructionData);
}
let mut inputs = [[0u8; 32]; NUM_PUBLIC_INPUTS];
for (input, bytes) in inputs.iter_mut().zip(rest.chunks_exact(32)) {
    input.copy_from_slice(bytes);
}
if !verify(&Proof::from_le_bytes(proof), inputs) {
    return Err(MyError::InvalidProof.into());
}

// After
use my_circuit_client::{MyCircuitProof, Verifiable};
let proof = MyCircuitProof::try_from(data).map_err(|_| ProgramError::InvalidInstructionData)?;
proof.verify().map_err(|_| MyError::InvalidProof)?;
```

Map an `XarkError` to your program's own error, as above, rather than returning
its code: its codes (`Truncated` 1, `InvalidProof` 2, `TrailingBytes` 3) are
`ProgramError::Custom` codes too, and would read as your program's.

The public inputs parsed from instruction data come from whoever sent it. Check
them against your program's state (a policy, a Merkle root, the signer) before
you act on the proof, as with `PublicInputs`. A circuit whose public inputs aren't
all byte arrays gets `MyCircuitProof` without `try_from`: fill it from your
state. A circuit with a public input named `proof` gets no `MyCircuitProof`, and
`PublicInputs` and `verify` work as before.

## Prove from Rust (optional)

The client crate's `prover` feature adds `prover::Prover`, for a server or a
local Rust app. The default build, the one a program uses, doesn't pull it in.

```toml
my-circuit-client = { path = "clients/my-circuit/rust", features = ["prover"] }
```

```rust
use my_circuit_client::prover::Prover;

// The circuit's build directory. In a project the proving key is found in
// keys/my-circuit/; outside one, beside the build.
let prover = Prover::new("circuits/my-circuit/target/xark/my-circuit");
let proof = prover.prove_fields([("x", "3"), ("y", "9")])?;
let data = proof.to_instruction_data(); // proof || public inputs
```

`prove_fields` takes every input as a `(name, decimal field value)` pair, and
`prove_json` a JSON object of them. Neither encodes a struct or a natural value
(a date, a string) yet: for those, use `xark prove` or the TypeScript client.

## Prove on a GPU (experimental, optional)

An `xark` built with OpenCL proves large circuits with the quotient and the H
MSM on the GPU, beside the CPU's MSMs, with the same keys. It is tested on
Apple Silicon (and in CI on POCL); other GPUs should work but haven't been run.
Every proof it makes is verified before it's written, and one that fails
although your inputs satisfy the circuit is proved again on the CPU, with a
warning:

```sh
cargo install xark-cli --version 0.5.0 --locked --features opencl
xark prove --prover opencl --acknowledge-gpu-side-channel-risk --inputs inputs.json
```

A circuit under a 2^18-point QAP domain (up to about 131k constraints) proves
on the CPU, where the GPU's fixed cost would lose; the command says which proved it. A
GPU MSM is variable-time and its buffers aren't guaranteed to be erased, hence
the flag: use it on trusted, single-tenant hardware only. From Rust, the provers
share `xark_groth16::Prover`: `Cpu` and `Accelerated` with a device.

## Reuse another circuit's types

A circuit crate can depend on another circuit crate and use its `#[input]` types
and methods: only the crate `xark` builds exports its `#[circuit]`. In 0.4 the two
entries clashed at link time (`duplicate symbol: __xark_main`), so a circuit crate
meant as a library had to put its `#[circuit]` behind a feature. That feature can
go: depend on the crate as it is, and its circuit still builds on its own. See [Reusing types from another circuit](inputs.md#reusing-types-from-another-circuit);
`examples/zkyc_nationality` is a circuit over `examples/zkyc`'s `Identity`.

## Smaller changes

- The client crate depends on `xark-verifier = "0.5.0"`, a semver-compatible
  requirement, where 0.4 pinned it exactly (`"=0.4.0"`): it takes the verifier's
  patch releases.
- rust-analyzer no longer greys out a `#[circuit]` function as inactive code.
