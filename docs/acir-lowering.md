# ACIR-to-R1CS Lowering

xark only supports `Opcode::AssertZero(Expression)` in this release. Every
other opcode (black-box calls, memory ops, Brillig, multi-circuit `Call`) is
rejected with an `UnsupportedOpcode` error before any constraint is emitted.

## R1CS form

All constraints are emitted as `<A, z> * <B, z> = <C, z>` over
`ark_bn254::Fr`, with the Arkworks-implicit one variable in position 0.

## Variable allocation rules

1. Public input variables are allocated first, in the exact order produced
   by `NoirArtifact::public_inputs` (external `public_parameters` first,
   then `return_values`).
2. Private witness variables are allocated lazily on first reference during
   lowering.
3. Auxiliary `t_i` variables are allocated as needed when an `AssertZero`
   expression has more than one multiplication term.
4. The `WitnessIndex -> Variable` map is owned by the `R1csBuilder` and is
   reused for both setup-mode and proving-mode synthesis so that circuit
   shape stays identical between the two.

## Expression lowering

A Noir `Expression` has three parts: `mul_terms` (degree-2), 
`linear_combinations` (degree-1), and `q_c` (constant). The semantic target
is `expression == 0`.

### Linear-only (`mul_terms` empty)

Enforced as `0 * 0 = -(linear + q_c)`, which is equivalent to
`linear + q_c = 0`.

### One mul term

For `q_M * a * b + linear + q_c = 0`, the constraint is

```
a * (q_M * b) = -(linear + q_c)
```

This compresses into a single R1CS row.

### Multiple mul terms

For `\sum_i q_i * a_i * b_i + linear + q_c = 0`, each `a_i * b_i` is
materialised as an auxiliary `t_i = a_i * b_i`, then the residual

```
\sum_i q_i * t_i + linear + q_c = 0
```

is enforced as one linear constraint. This is `mul_terms.len() + 1` R1CS
rows total.

`estimate_constraints` in `lower.rs` mirrors this counting so that
`inspect`'s reported constraint estimate matches what the prover will
actually emit.

## Closures and setup mode

ark-relations does not invoke value-producing closures when the
`ConstraintSystem` is in `SynthesisMode::Setup`. We rely on this: the
closures we pass to `new_input_variable`, `new_witness_variable`, and
`new_witness_variable` for `t_i` all look up the witness map, which is
`None` during setup. If Arkworks ever changes that behavior, every variable
allocation site here would need a setup-mode branch.

## What's *not* supported yet

Any opcode that isn't `AssertZero` errors out at `LoweredAcirCircuit::new`.
The error includes the opcode index and a remediation hint. This is the
single chokepoint for opcode policy — adding a new gadget means changing
`OpcodeClass::is_supported` and the dispatch in `LoweredAcirCircuit::synthesize`.
