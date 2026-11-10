// The generated `scalar_range` client (`xark client`) through xark-wasm. The circuit
// has no public inputs, so verifying needs no `{}`.
import { artifacts } from "../artifacts";
import { ScalarRange, ScalarRangeProver, ScalarRangeVerifier } from "./scalar_range";

let prover: ScalarRangeProver;
let verifier: ScalarRangeVerifier;
beforeAll(async () => {
  prover = await ScalarRange.prover(artifacts("scalar_range"));
  verifier = await ScalarRange.verifier(artifacts("scalar_range").verifyingKey);
});

test("proves and verifies without public inputs", () => {
  const proof = prover.prove({ s0: 1, s1: 0, s2: 0 });
  expect(proof.publicInputs).toEqual({});
  expect(verifier.verify(proof)).toBe(true);
  expect(verifier.verify(proof.toBytes())).toBe(true);
  expect(verifier.verify(proof.toBytesCompressed())).toBe(true);
  // @ts-expect-error: a circuit with no public inputs takes none (tsc checks this line)
  if (false) verifier.verify(proof, {});

  const garbled = proof.toBytes();
  garbled[10] ^= 0xff;
  expect(verifier.verify(garbled)).toBe(false);
});
