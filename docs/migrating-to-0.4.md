# Migrating from 0.3 to 0.4

0.4 adds projects: one directory for a circuit, the Solana program that verifies
it, the clients xark generates and their tests. It also changes the verifier crate
`xark export` writes. **No circuit changed**: every digest is the same, so keys
made with 0.3 still verify, and a deployed program keeps working until you choose
to update it.

You can stay with a standalone circuit crate (what `xark init` made in 0.3) and
make the few changes in [Keep a circuit crate](#keep-a-circuit-crate), or move to
a project as in [Move to a project](#move-to-a-project). Either way, start with
[Update xark](#update-xark) and [Update your program](#update-your-program).

## Update xark

```sh
cargo install xark-cli --version 0.4.0 --locked
```

```toml
# The circuit's Cargo.toml (and any gadget crates, at the same release)
xark = "0.4"
xark-poseidon2 = "0.4"
```

```sh
npm install @blueshift-gg/xark@0.4
```

## Keep a circuit crate

A circuit crate without a `xark.toml` above it works as it did, except where the
generated code goes:

| | 0.3 | 0.4 |
|---|---|---|
| `xark export` | `<crate>/<name>-verifier/` | `<crate>/clients/rust/` |
| `xark client` | `<crate>/target/xark/<name>/<circuit>.ts` | `<crate>/clients/ts/<circuit>.ts` |

The verifier crate keeps its name (`<name>-verifier`, or your `--crate-name`).
Point your program's path dependency at the new directory, or keep the old one
with `--out`:

```toml
# programs/…/Cargo.toml
my-circuit-verifier = { path = "../my-circuit/clients/rust" }
```

Run `xark export` and `xark client` again, and commit what they write. Your keys
stay in `target/xark/<name>/`.

## Move to a project

A project keeps everything in one Cargo workspace, and `xark build` and `xark test`
at its root build and test all of it. See [Projects](projects.md) for the layout.

1. **Make the project** in a new directory, named after your circuit:

   ```sh
   xark init my-circuit && cd my-circuit
   ```

2. **Move the circuit.** Replace `circuits/my-circuit/src/` with your crate's
   `src/`, and copy its dependencies into `circuits/my-circuit/Cargo.toml`. Drop
   any `[workspace]` table: the project's root `Cargo.toml` is the workspace.

3. **Keep your keys.** A deployed program embeds your verifying key, so carry the
   keys over instead of making new ones:

   ```sh
   mkdir -p keys/my-circuit
   cp ../old/target/xark/my-circuit/{pk.bin,vk.bin,metadata.json,circuit.xbc} keys/my-circuit/
   ```

   `circuit.xbc` is the build the key was made from, and a key proves only with that
   build. If yours was rebuilt since `xark setup` (`xark build` says the key was
   made from another build of the circuit), you need a new key and a new verifier.

   A project commits `keys/`. `xark build` makes a key only when there's none, and
   never while a committed verifier embeds one. A proving key over 50 MB belongs
   in Git LFS.

4. **Move the program** into `programs/my-circuit/`. In its `Cargo.toml`, depend on
   the generated crate, and remove `[workspace]` and `[profile.release]` (the root
   has the programs' profile):

   ```toml
   [dependencies]
   my-circuit-verifier = { path = "../../clients/my-circuit/rust" }
   ```

   If you exported with `--crate-name`, the crate is now `my-circuit-verifier`:
   rename its `use` lines. `xark add program my-circuit` writes a new one in the
   canonical Pinocchio layout instead, if you'd rather start from that.

5. **Build** at the root. It writes `clients/my-circuit/{rust,ts}`, then builds
   the program:

   ```sh
   xark build
   ```

6. **Move the TypeScript tests** into `tests/`, and replace your harness with
   `@blueshift-gg/xark/testing` (it needs `litesvm` and `@solana/kit`). Import
   the client from `clients/`:

   ```ts
   // Before
   import { artifacts, funded, send, vm } from "./harness";
   import { MyCircuit } from "./my_circuit";
   const prover = await MyCircuit.prover(artifacts("circuit", "my_circuit"));
   const svm = vm(id, "program/target/deploy/my_circuit_program.so");

   // After
   import { circuit, funded, program, send, vm } from "@blueshift-gg/xark/testing";
   import { MyCircuit } from "../clients/my-circuit/ts/my_circuit";
   const prover = await MyCircuit.prover(circuit("my-circuit"));
   const svm = vm({ [id]: program("my-circuit") });
   ```

7. **Commit** everything `xark build` wrote, `keys/` included, and run CI with
   `xark build --check` (the workflow `xark init` wrote does) and `xark test`.

## Update your program

### `verify` takes its public inputs by name

The generated crate has a `PublicInputs` struct, with your circuit's public
inputs as named fields, packed for you as the circuit's `#[input]` packs them:

```rust
// Before: field elements in proof order, packed by hand
let public_inputs: [[u8; 32]; 5] = policy::public_inputs(&commitment, unix, holder);
if !zkyc_verifier::verify(&proof, &public_inputs) { … }

// After
let inputs = zkyc_verifier::PublicInputs {
    commitment,
    policy: zkyc_verifier::Policy { today, born_by, min_net_worth, allowed },
    holder: *holder.address(),
};
if !zkyc_verifier::verify(&proof, inputs) { … }
```

Pass it by value (it's `Copy`): clippy flags a needless `&inputs`. `verify` takes
anything that converts into `Fields` (`[[u8; 32]; N]`), so code
that already builds the field elements keeps working: pass them by value,
`verify(&proof, fields)`, or `*fields` from a reference. To pack a struct of your
own, implement `From<&YourStruct> for Fields` with `xark_verifier::fields::Packer`.

### `verify_instruction_data` is gone

It was a second way to verify. Split the public inputs off after the proof's 256
bytes, and call `verify`:

```rust
// Before
if !my_circuit_verifier::verify_instruction_data(data) { … }

// After
let (proof, rest) = data.split_first_chunk::<256>().ok_or(ProgramError::InvalidInstructionData)?;
let mut fields: Fields = [[0; 32]; NUM_PUBLIC_INPUTS];
if rest.len() != fields.len() * 32 {
    return Err(ProgramError::InvalidInstructionData);
}
for (f, b) in fields.iter_mut().zip(rest.chunks_exact(32)) {
    f.copy_from_slice(b);
}
if !verify(&Proof::from_le_bytes(proof), fields) { … }
```

`VK_BYTES` is gone with it: the key is in `VERIFIER`.

### TypeScript

A proof's `toInstructionData()` is `toBytes()` followed by `toFields()`, its public
inputs as the program's `Fields`, for a program that takes both.

## Checking the move

- `xark build --check` at the project's root passes with nothing to commit.
- `xark test` runs the circuit's tests, the program's, and the LiteSVM tests.
- The verifying key the program embeds (`clients/<circuit>/rust/verifying_key.solana.bin`)
  is the one deployed: if you kept your keys, it's byte for byte what 0.3 exported
  (`<name>-verifier/verifying_key.solana.bin`).
