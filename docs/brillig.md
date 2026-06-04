# Brillig handling in xark

This document is the **design note** for ROADMAP step **WS-C.1**. The matching
implementation is **WS-C.2**. When starting C.2, pick this doc up first and
follow the implementation sketch at the bottom.

## What Brillig is

Brillig is Noir's **unconstrained virtual machine**. It is a stack-based
bytecode that runs *during witness computation* (i.e. during
`nargo execute` / the ACVM solver), but is **not constrained inside the
proving system**.

The Noir compiler emits Brillig for **hint computations**: things that are
easier to compute imperatively but whose results must be re-derived by ACIR
constraints for soundness. Typical examples:

* **Modular inverse hints.** `1/x` is supplied by Brillig; ACIR enforces
  `x * supplied_inverse == 1`.
* **Bit decomposition hints.** Brillig spits out the bits; ACIR enforces each
  bit is boolean and the bit recomposition equals the original witness.
* **Quotient / remainder hints in division.** Brillig computes `q, r` from
  `a, b`; ACIR enforces `a = b*q + r` together with `r < b`.

The shape of the opcode in `acir::circuit::Opcode` (see
`/tmp/noir-probe/acvm-repo/acir/src/circuit/opcodes.rs`):

```rust
Opcode::BrilligCall {
    id: BrilligFunctionId,
    inputs: Vec<BrilligInputs<F>>,
    outputs: Vec<BrilligOutputs>,
    predicate: Expression<F>,
}
```

with

```rust
pub enum BrilligOutputs {
    Simple(Witness),
    Array(Vec<Witness>),
}
```

The full bytecode lives separately on the `Program` (see
`/tmp/noir-probe/acvm-repo/acir/src/circuit/brillig.rs`,
`BrilligBytecode { function_name, bytecode: Vec<BrilligOpcode<F>> }`),
indexed by `id`.

## Why we can choose to ignore Brillig outputs

Noir's **compiler contract** is: every witness produced by a Brillig call is
also constrained by surrounding `Opcode::AssertZero` opcodes. The Brillig
output is the *hint*; the ACIR opcodes that follow are the *check*.

If a Brillig output were **not** constrained by any AssertZero, that would be
a Noir compiler bug (a missing soundness check). But it cannot produce a
**soundness failure in xark** beyond what the bug already creates: xark
evaluates every supplied witness through the lowering layer and checks that
the lowered constraints hold. A Brillig output that's not constrained
becomes a free variable that the prover could populate with anything; the
verifier would still accept, but only because the Noir program never asked
it to check.

### Soundness argument: "ignore Brillig opcodes" is sound

Let `B` be a Brillig opcode emitting outputs `w_1, ..., w_k`.

* **(SI)** *Soundness invariant.* If Noir is correct, every `w_i` appears in
  at least one downstream `AssertZero` opcode that pins its value relative
  to other witnesses.
* xark lowers each such `AssertZero` into a Groth16 R1CS constraint
  (per `docs/acir-lowering.md`).
* The Groth16 verifier checks the R1CS constraints.
* Therefore: **ignoring Brillig opcodes is sound** as long as (SI) holds and
  the surrounding constraints are correctly lowered.

The lowering of `AssertZero` is already covered by `lower::lower_assert_zero`
and its test suite. The remaining surface is `(SI)` itself, which is the
Noir compiler's contract — not ours.

## Failure mode if (SI) is violated

A Noir compiler bug producing an unconstrained Brillig output would let a
malicious prover lie about that witness. **xark cannot detect this** in the
trust-outputs strategy because we never re-execute the Brillig bytecode.

The defence is *out-of-band*:

* Track which Noir compiler versions we've vetted in `NOIR_VERSION.md`
  (introduce this file when C.2 lands).
* Reject artifacts compiled by versions not on the allowlist with a clear
  error.
* When a new Noir release adds a feature that touches Brillig emission,
  re-vet before bumping the allowlist.

## Alternative considered (Plan B): re-execute Brillig

We could embed `acvm`'s Brillig VM and run it during setup-mode witness
solving. Outputs derived this way would be bound to the values the VM
computes; any unconstrained-witness compiler bug would surface as either:

* a mismatch between the prover-supplied witness and the VM-computed one
  (caught by a constraint we'd add: `vm_output == witness`), or
* an `AssignmentMissing` if the VM can't run because some input is unknown.

**Cost** of Plan B:

* Add `acvm`'s VM crate (and its transitive deps) as a runtime dependency.
* Run the VM at proving time on every Brillig call (linear in bytecode
  length × number of Brillig opcodes).
* Maintain compatibility with whichever Brillig opcode set the pinned Noir
  version emits — this is a moving target.

## Decision: Plan A (trust outputs)

**Rationale.**

1. Noir's compiler is what produces the surrounding `AssertZero` opcodes. If
   it has a soundness bug there, no amount of Brillig re-execution rescues
   us: the constraint we'd compare against doesn't exist.
2. Plan A is roughly **five lines of code** — bind the declared output
   witnesses to whatever the witness map already contains, then move on.
3. We can revisit if a future Noir release lands that's known to
   under-constrain Brillig outputs, or if downstream users (Solana,
   on-chain) demand a stricter soundness story.

## Implementation sketch (for C.2)

The dispatch happens in `LoweredAcirCircuit::synthesize` (see
`crates/acir-r1cs/src/lower.rs`). Today the match arm rejects `BrilligCall`
via the `_ => return Err(SynthesisError::Unsatisfiable)` catch-all and the
pre-check in `LoweredAcirCircuit::new` rejects it via
`OpcodeClass::is_supported`. C.2 needs to:

1. Update `OpcodeClass::is_supported` in
   `crates/acir-r1cs/src/opcodes/mod.rs` to return `true` for
   `OpcodeClass::Brillig`.
2. Add a new arm in the synthesize loop. The body looks like:

   ```rust
   Opcode::BrilligCall { outputs, .. } => {
       for out in outputs {
           match out {
               BrilligOutputs::Simple(w) => {
                   let _ = builder.alloc_witness(WitnessIndex::from_witness(*w))?;
               }
               BrilligOutputs::Array(ws) => {
                   for w in ws {
                       let _ = builder.alloc_witness(WitnessIndex::from_witness(*w))?;
                   }
               }
           }
       }
       // No additional constraints. Inputs are not touched: surrounding
       // AssertZero opcodes already reference any input witnesses they
       // care about, and the predicate gates *those* constraints, not
       // ours.
   }
   ```

3. Update `OpcodeClass::help` for `Brillig` to reflect the new behaviour
   (it currently advertises the opcode as unsupported).

### Why `alloc_witness` is enough

`R1csBuilder::alloc_witness` returns the existing `Variable` if the witness
has already been allocated, or allocates a new one and (in proving mode)
binds it to the value from the witness map. There's no separate constraint
emitted; the binding to the map value happens via Arkworks' internal value
function. If a Brillig-only witness shows up here that no AssertZero ever
references, this call is the *only* place it gets bound — and that's fine,
because nothing constrains it either way.

### Predicate handling

`predicate: Expression<F>` controls whether the Brillig VM executes (zero =
skip, nonzero = run). We don't need to do anything with it in xark:

* If `predicate` evaluates to zero, Noir guarantees the surrounding
  `AssertZero` opcodes are also gated on it (typically via
  `predicate * (constraint_residual) = 0` rewrites in the compiler). Those
  gated constraints lower into R1CS exactly like any other AssertZero.
* If `predicate` evaluates to nonzero, the constraints fire normally.

In both cases, the predicate's effect is already encoded in the surrounding
ACIR, not in the BrilligCall opcode itself.

## What to test (C.2's acceptance criteria)

1. **Happy path.** A Noir program using `// Safety: ` Brillig calls — e.g.,
   integer division `a / b` where `1/b` is a Brillig hint and ACIR enforces
   `b * (1/b) == 1` plus `a = b*q + r`, `r < b`. Add as
   `examples/division_basic` and a fixture under `tests/fixtures/`.
2. **Verify true.** Prove and verify the happy path with valid inputs.
3. **Constrained-witness tamper.** Tamper with any *constrained* witness in
   the witness map → verify false.
4. **Brillig-only witness tamper.** If the program has a Brillig output that
   isn't in any AssertZero (this is unusual; check by inspecting the ACIR),
   tampering with it may still verify true. **Document this as a known
   limitation pending Plan B.** Note: this isn't a soundness regression
   vs. dropping the BrilligCall altogether — it's the inherent cost of
   trusting Noir's compiler.

## Open questions to confirm before C.2 starts

* Does `R1csBuilder::alloc_witness` early-return when the witness is already
  allocated, or does it error? (It should early-return based on existing
  call sites in `lower_assert_zero`, but worth confirming.)
* When `predicate` is symbolically zero (compile-time false branch), does
  Noir still emit downstream AssertZero opcodes? If not, our "predicate is
  handled elsewhere" claim needs a footnote.
* Should we record Brillig outputs separately (e.g. in inspect output) so
  users can see which witnesses are *only* bound by trust?

## Links

* **C.2** (implementation): see `ROADMAP.md` § WS-C.2.
* Related lowering doc: `docs/acir-lowering.md`.
* Related ACIR types: `/tmp/noir-probe/acvm-repo/acir/src/circuit/brillig.rs`,
  `/tmp/noir-probe/acvm-repo/acir/src/circuit/opcodes.rs`.
