/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Rsa2048.Chain
import Formal.Circuits.Rsa2048.Bits

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# `rsa2048`'s chain from the circuit alone

`chain_congruence` asked for the packed `sig`, `n` and `em` limbs' bounds. They are
the byte packing's: `nBound`/`sigBound`/`emBound` read the exported linear
combinations, and `hbit` turns the 544 `to_bits` contracts into "each bit is 0 or 1".
This file discharges the hypotheses, so the chain congruence holds for every
satisfying assignment.
-/

namespace Xark.Circuits.Rsa2048

open Xark.Circuit Xark.R1cs Xark.Template
open Xark.Rsa.GroupedColumns (val W)

/-- **The chain congruence from `circuit`'s rows alone.** If `σ` satisfies every row,
`em ≡ sig^(2^16+1) (mod n)`, where the three integers are the limb vectors the chain
calls carry. -/
theorem chain_congruence_sat (σ : ℕ → F) (h : Sat circuit σ) :
    chainEm σ ≡ (val (limb sq0 σ 0)) ^ (2 ^ 16 + 1) [ZMOD chainN σ] := by
  have hb := hbit σ h
  refine chain_congruence σ h (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
  · interval_cases i
    · exact sigBound0 σ hb
    · exact sigBound1 σ hb
    · exact sigBound2 σ hb
    · exact sigBound3 σ hb
    · exact sigBound4 σ hb
    · exact sigBound5 σ hb
    · exact sigBound6 σ hb
    · exact sigBound7 σ hb
    · exact sigBound8 σ hb
    · exact sigBound9 σ hb
    · exact sigBound10 σ hb
    · exact sigBound11 σ hb
    · exact sigBound12 σ hb
    · exact sigBound13 σ hb
    · exact sigBound14 σ hb
    · exact sigBound15 σ hb
    · exact sigBound16 σ hb
    · exact sigBound17 σ hb
    · exact sigBound18 σ hb
    · exact sigBound19 σ hb
    · exact sigBound20 σ hb
    · exact sigBound21 σ hb
    · exact sigBound22 σ hb
    · exact sigBound23 σ hb
    · exact sigBound24 σ hb
  · interval_cases i
    · exact nBound0 σ hb
    · exact nBound1 σ hb
    · exact nBound2 σ hb
    · exact nBound3 σ hb
    · exact nBound4 σ hb
    · exact nBound5 σ hb
    · exact nBound6 σ hb
    · exact nBound7 σ hb
    · exact nBound8 σ hb
    · exact nBound9 σ hb
    · exact nBound10 σ hb
    · exact nBound11 σ hb
    · exact nBound12 σ hb
    · exact nBound13 σ hb
    · exact nBound14 σ hb
    · exact nBound15 σ hb
    · exact nBound16 σ hb
    · exact nBound17 σ hb
    · exact nBound18 σ hb
    · exact nBound19 σ hb
    · exact nBound20 σ hb
    · exact nBound21 σ hb
    · exact nBound22 σ hb
    · exact nBound23 σ hb
    · exact nBound24 σ hb

  · interval_cases i
    · exact emBound0 σ hb
    · exact emBound1 σ hb
    · exact emBound2 σ hb
    · exact emBound3 σ hb
    · exact emBound4 σ
    · exact emBound5 σ
    · exact emBound6 σ
    · exact emBound7 σ
    · exact emBound8 σ
    · exact emBound9 σ
    · exact emBound10 σ
    · exact emBound11 σ
    · exact emBound12 σ
    · exact emBound13 σ
    · exact emBound14 σ
    · exact emBound15 σ
    · exact emBound16 σ
    · exact emBound17 σ
    · exact emBound18 σ
    · exact emBound19 σ
    · exact emBound20 σ
    · exact emBound21 σ
    · exact emBound22 σ
    · exact emBound23 σ
    · exact emBound24 σ

end Xark.Circuits.Rsa2048
