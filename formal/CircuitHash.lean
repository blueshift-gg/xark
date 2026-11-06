/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Secp256k1Ecdsa

/-!
Run by CI (`lean.yml`, after the build) as `lake env lean CircuitHash.lean`: for each
exported circuit, each segment of its Lean composition (`Xark.Circuit.Seg.rows`) must hash
to the hash the exporter took of the compiler's rows for that segment (`expectedSegs`, in
order), so a theorem about `circuit` is about the production circuit. The segments are
hashed side by side. Fails, naming the circuit and the first differing segment, otherwise.
-/

#eval Xark.Circuit.check "Secp256k1Ecdsa" Xark.Circuits.Secp256k1Ecdsa.circuit
  Xark.Circuits.Secp256k1Ecdsa.expected Xark.Circuits.Secp256k1Ecdsa.expectedSegs
