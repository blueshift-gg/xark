/-
Copyright (c) 2026 Blueshift Labs Limited. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: Blueshift Labs Limited
-/
import Formal.Circuits.Secp256k1Ecdsa

/-!
Run by CI (`lean.yml`, after the build) as `lake env lean CircuitHash.lean`: for each
exported circuit, the rows of its Lean composition (`Xark.Circuit.rows`) must hash to the
hash the exporter took of the compiler's rows (`expected`), so a theorem about `circuit`
is about the production circuit. Fails, naming the circuit and both hashes, otherwise.
-/

#eval Xark.Circuit.check "Secp256k1Ecdsa" Xark.Circuits.Secp256k1Ecdsa.circuit
  Xark.Circuits.Secp256k1Ecdsa.expected Xark.Circuits.Secp256k1Ecdsa.expectedSegs
