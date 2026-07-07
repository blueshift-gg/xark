/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Mathlib

-- The `style.header` linter hard-codes mathlib's Apache license string; this is
-- an MIT project, so disable that house-style check (it is not a correctness lint).
set_option linter.style.header false

/-!
# xark — the BN254 scalar field `Fr`

The shared BN254 scalar field definition, used by the Poseidon2 gadget
soundness proof (`Formal.Poseidon2Bn254T3` — the `t = 3` permutation matching
the in-circuit gadget `crates/xark-poseidon2/src/lib.rs`). This is the field the
Rust gadgets compute in: `ZMod bn254FrModulus`.
-/

namespace Xark

/-- BN254 scalar field modulus (Fr). Same value as `ark_bn254::Fr`. -/
def bn254FrModulus : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- BN254 scalar field `Fr` as `ZMod` (the same field the Rust gadget computes
in). -/
abbrev Bn254Fr : Type := ZMod bn254FrModulus

end Xark
