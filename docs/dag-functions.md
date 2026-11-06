# DAG functions & the JIT prover

xark stores a circuit as a **DAG-compact bytecode artifact** (`circuit.xbc`): each repeated
piece of the circuit is stored once as a **template**, every other occurrence is a small call
record, and long periodic runs are rolled. Setup and proving **expand it on demand** (the "JIT
prover" model) instead of reading a flat constraint list. This covers how templates are found,
the container, decoding, minimization, and how soundness is checked at each step.

## Why

A signature circuit is millions of constraints built from a handful of routines (a field
multiply, a point add or double) run thousands of times. Storing the flat expansion wastes disk
and load time; storing each routine once does not:

| circuit | constraints | `circuit.xbc` |
|---|---:|---:|
| `ed25519` | 2,399,092 | 43 KB |
| `secp256k1_ecdsa` | 1,634,595 | 441 KB |
| `keccak256` | 156,280 | 562 KB |

## Pipeline

```
Rust circuit crate
  │  rustc (any stable ≥ 1.89) → wasm32, with --cfg xark
  ▼
xark-frontend interpreter (interp.rs, builder.rs)
  │   • runs the module with witness values symbolic, emitting rows and witness ops
  │   • records the rows / witness ops / variables each wasm call produced (a Region)
  ▼
templates::detect                   (templates.rs)
  │   • two calls whose rows are identical up to variable renaming are one template
  ▼
build_function_blob                 (output.rs) → circuit.xbc, container version 2
  ▼   setup / prove
function_decode::expand_function_blob → CircuitProgram   (exactly the flat circuit)
  │   or expand_function_blob_reduced: each template minimized once (what setup keys)
  ▼
Groth16 (xark-groth16, streaming)
```

`circuit.xbc` carries both consumer views, `to_r1cs()` for the Groth16 backend and
`to_primitive()` for the witness solver, so nothing downstream needs to know the circuit was
template-encoded.

## Template detection

Templates are found **after** lowering, purely as an encoding of the finished flat circuit
(`crates/frontend/src/templates.rs`):

- The interpreter records, for every wasm call, the range of rows, witness ops and variables
  it produced, and its enclosing call.
- Two calls are the same template when their rows are identical once the variables the call
  allocated are written as offsets from its first one and variables from outside become
  positional **plugs**. The first such call becomes the template's definition; every match
  becomes a `CALL` record `(template, base var, plug LCs)`.
- Calls smaller than 8 rows stay inline, since a `CALL` record isn't worth it. Templates nest:
  a template's body may itself contain calls.

Because expansion reproduces the flat circuit exactly, templates never change the proven
circuit, only the artifact's size and how fast it expands. A routine can only become a template
if rustc keeps it as a separate wasm call (`#[inline(never)]` guarantees that); code rustc
inlines is stored inline.

## The container

`b"XBC\0"` + a `u16` version (`2`); `is_function_artifact` rejects anything else, including
version-1 files from the removed MIR frontend (rebuild them). After the header (field name and
modulus, variable count, and each signature input's role and name), the body is:

- a **constant pool**, referenced by index from anywhere below;
- the **template definitions**: each a base variable, its plug and output variables, and its
  constraint and witness item streams;
- the **top-level** constraint and witness item streams;
- the variables to keep although nothing references them (rare unreferenced advice).

Items are rows (`a·b = c`) and witness ops, `CALL`s, rolled `CALL` blocks, and rolled runs of
rows or witness ops (`bytecode::roll_and_encode_ops_compact`). Variables are zigzag deltas from
the previous one in a list, and rows can refer back to an earlier row's linear combination. The
byte-level tag table is the header of `crates/ir/src/function_decode.rs`; the encoder
(`output.rs`) and decoder must change together.

## Decode & variable-table reconstruction

`expand_function_blob(bytes) → CircuitProgram`:

1. Parse the header, the pool, the definitions and the top-level streams.
2. Walk the top-level streams; a `CALL` recurses into its template with the substitution
   `v ≥ base_var ↦ call_base + (v − base_var)`, `plug ↦ caller's plug LC`, reproducing the flat
   rows and witness program.
3. **Roles are id-based, not visibility-based.** Ids `0..num_inputs` take the stored role and
   name; every other variable is `Derived`, including hint/advice variables, which the witness
   program computes and are never supplied.
4. Drop every unreferenced non-input variable except the keep-set, and the witness ops whose
   output was dropped, matching the flat lowering exactly.

## R1CS minimization

Independent of the bytecode: a **linear-variable-elimination** pass on the R1CS (Gaussian
elimination over the field). Every internal variable defined by a linear constraint is
substituted away to a fixpoint. The eliminated variable is a function of the survivors, so
satisfiability is preserved exactly in both directions.

By default this runs as a **template minimize + boundary pass**: each template body is minimized
once during the reduced expand (plugs and outputs pinned), then one pass over the flattened
result removes the remaining cross-template plug copies, reaching the same fixpoint as a full
flat minimize without materializing the unreduced circuit. `xark setup` records which form a key
was made for (`--r1cs-form`), and writes a minimized key's rows (`r1cs.stream`) beside it so `xark
prove` skips the minimize.

The Groth16 cost is set by the proving key and FFT domain, which scale with constraints and
variables, so the big win is crossing below a domain-size boundary.

## Soundness, checked at each step

- **Artifact ≡ flat.** `function_decode::verify_blob_matches` decodes the artifact
  independently and checks it equals the flat lowering (rows, witness program, variable roles).
  `crates/frontend/tests/examples.rs` runs it on every example, and so does
  `cargo xtask digests`.
- **The keyed (reduced) circuit is as sound as the full one.** `crates/ir/tests/reduced_soundness.rs`:
  a forged public output is rejected by both, and every public input stays constrained.
- **The minimizer preserves satisfiability** by construction, and end to end by producing
  verifying proofs that reject wrong witnesses. `XARK_VERIFY` (developer builds) also asserts
  it reached a fixpoint.
- **Under-constraint gate.** Independently, lowering rejects any hint/advice or public variable
  left unpinned by a constraint.

## Developer flags

Behind the `debug` feature, or CLI flags:

| flag | effect |
|------|--------|
| *(default)* | template minimize + boundary pass |
| `XARK_FLAT_MINIMIZE` | guarded flat minimize on the full expansion instead |
| `XARK_NO_MINIMIZE` | skip R1CS minimization |
| `XARK_MAX_FILL` | fill-in cap for the guarded flat minimize (default 32) |
| `xark prove --cache` | write the minimized rows (and a decoded key) when missing |
| `XARK_VERIFY` | assert the minimizer reached its fixpoint |
| `XARK_BUILD_TIME` / `PROVE_TIME` | per-phase build / prove timings |
