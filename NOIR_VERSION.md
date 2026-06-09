# Supported nargo / ACIR Version

xark lowers **ACIR** (the intermediate representation `nargo` emits), not Noir
source — it never parses the Noir language. What this pin constrains is the
ACIR *artifact format* and *opcode/black-box set*, which ship from the
noir-lang monorepo and are still pre-1.0 (there is no stable, independently
versioned ACIR interface yet). So the version that matters is the **`nargo`
version that compiled the circuit**, which must match the `acir`/`acvm` crate
version xark links against. Your Noir source may use any language feature that
`nargo` version supports.

```
Supported Noir version:        1.0.0-beta.22
Supported nargo version:       1.0.0-beta.22
Supported ACIR artifact format: bytecode format byte 0x03 (msgpack-compact) inside the standard nargo target/<name>.json envelope
Supported witness format:       WitnessStack serialized via rmp-serde (msgpack-compact) and gzip-compressed (target/<name>.gz)
Date tested:                    2026-06-09
Known incompatible versions:    every Noir release earlier than 1.0.0-beta.22, and every release after 1.0.0-beta.22 until this file is updated
```

xark pins `acir` to the matching nargo tag (`v1.0.0-beta.22`, commit
`c57152f91260ecdb9faad4efc20abb14b6d2ece7`); it re-exports and pulls in
`acir_field` / `acvm` at the same commit. Bumping nargo requires bumping the git
tag in `Cargo.toml` and re-testing every fixture under `crates/tests/fixtures/`.

### Beta.21 → beta.22 migration notes

The bump from beta.21 to beta.22 carried two incompatible ACIR changes that
required corresponding lowering updates:

1. **`MemOp` is no longer generic** over the field. `MemOp<F>` became
   `MemOp` (the `_phantom: PhantomData<F>` field was removed). Field types
   were unchanged; the lowering layer only needed the type signatures
   updated.
2. **`EmbeddedCurveAdd` and `MultiScalarMul` outputs dropped from
   3-tuple to 2-tuple**. The `is_infinity` input/output was removed —
   the opcode contract now assumes neither input is at infinity, and
   the point at infinity is encoded as `(0, 0)` in the witness-level
   convention. `lower_embedded_curve_add` and `lower_multi_scalar_mul`
   now allocate a constant-zero `is_infinity` internally so the
   `curve_point_from_vars` gadget (which still tracks it) can be
   re-used unchanged.
