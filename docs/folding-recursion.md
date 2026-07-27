# Folding recursion over the BN254↔Grumpkin cycle

Status of Xark's folding-recursion (Nova/CycleFold-style IVC) building blocks, the
cycle's field roles, and the one capability gap that blocks a *closed* loop.

## Why Grumpkin

BN254 (pairing curve, Groth16) has scalar field `Fr` and base field `Fq`.
**Grumpkin** is `y² = x³ − 17` over `Fr` — its coordinates are Xark's native
`Field`, so Grumpkin group ops are native in a BN254 circuit (a few constraints
each, no non-native limbs). That makes the compute-heavy half of folding cheap:
a full Nova fold step verifies in-circuit in **~9k constraints**
(`examples/grumpkin_nova_fold`), vs millions for non-native EC.

## What is built (all tested: accept + analyzer-clean + tamper-reject + Groth16)

In-circuit **verifier** core:
| Example | Verifies | Constraints |
|---|---|---|
| `grumpkin_ipa` | deferred-MSM accumulator claim | 12,212 |
| `grumpkin_ipa_fold` | full Halo IPA reduction + in-circuit Poseidon2 FS | 40,150 |
| `grumpkin_nova_fold` | one Nova folding step | 8,859 |
| `grumpkin_ivc` | 2-step folding IVC (computation + accumulator chains) | 18,200 |
| `grumpkin_complete_add` | identity-safe complete Grumpkin add (Nova prerequisite) | 24 |

Host-side **prover** core (`examples/grumpkin_nova_prover`): extract a Xark R1CS
`(A,B,C)`, fold committed relaxed instances (cross-term `T`), a multi-step
stepping loop, and a Grumpkin Pedersen commitment — verified that the folded
relaxed instance satisfies `Az∘Bz = u·Cz + E` and the commitment fold is
homomorphic.

## The cycle's field roles (who commits what)

Nova's primary circuit is over `Fr` (so a BN254 Groth16 can be the terminal
proof). A witness in field `K` is committed homomorphically only with a curve
whose **scalar field is `K`**:

- **BN254 G1** (scalar field `Fr`) commits the **primary** (`Fr`) witness — but
  its coordinates are in `Fq`, *non-native* in the `Fr` circuit.
- **Grumpkin** (scalar field `Fq`) commits the **companion** (`Fq`) witness — its
  coordinates are `Fr`, *native* in the `Fr` circuit.

So the `Fr` circuit **natively folds Grumpkin (companion) commitments**
(`grumpkin_nova_fold`), and **defers the one BN254-G1 scalar-mul** (`r·comm_W`
over the primary witness) to a small **companion circuit over `Fq`** — this is
**CycleFold**.

### This is not theory — it's a measured finding

Committing the primary `Fr` witness on Grumpkin and folding it **fails**: with
`r·T` large, `r·T mod r ≠ r·T mod q` (Grumpkin's group order is `Fq ≠ Fr`), so the
`comm_E` fold mismatched (`grumpkin_nova_prover`). Grumpkin Pedersen is
homomorphic over **`Fq`**, confirming the role split above.

## The capability gap (what blocks a closed loop)

The CycleFold companion is a circuit over **`Fq`** (BN254's *base* field). **Xark
is `Fr`-native** — it compiles to a BN254-`Fr` R1CS for Groth16 and has no
over-`Fq` target. So the companion circuit is **not buildable in Xark today**.

Remaining for a closed IVC:
1. **CycleFold companion** — an `Fq`-field circuit / proof system (the capability gap).
2. **Self-referential augmented step circuit** `F'` — computation + fold-verify +
   Poseidon2 IO compression, whose own committed instance is folded next step.
   Buildable on the `Fr` side (`examples/grumpkin_augmented_step` is the shape).
3. **Decider** — a terminal SNARK opening the final folded commitment.

The verifier core and the prover's accumulation are done; #1 is a genuine new
capability, #2–#3 are systems assembly with every field-matching pitfall mapped.
