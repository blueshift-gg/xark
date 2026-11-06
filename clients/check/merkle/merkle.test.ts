// The generated `merkle` client (`xark client`) through xark-wasm. `npm test` runs it,
// after setup.ts builds the example and its keys.
import { artifacts } from "../artifacts";
import { Field, Merkle, MerkleInputs, MerkleProver, MerkleVerifier } from "./merkle";

const root = new Field(19217897426496189115890594488318047711322540293288184119629031241572428947159n);
// `[Field; 4]` is a 4-tuple: a wrong length doesn't compile.
const inputs: MerkleInputs = { leaf: 7, siblings: [11, 22, 33, 44], indexBits: [1, 0, 1, 0], root };
// @ts-expect-error: three siblings, not four (tsc checks this line)
const short: MerkleInputs = { ...inputs, siblings: [11, 22, 33] };

let prover: MerkleProver;
let verifier: MerkleVerifier;
beforeAll(async () => {
  prover = await Merkle.prover(artifacts("merkle"));
  verifier = await Merkle.verifier(artifacts("merkle"));
});

test("proves membership", () => {
  const proof = prover.prove(inputs);
  expect(proof.publicInputs).toEqual({ root });
  expect(verifier.verify(proof.toBytes(), { root })).toBe(true);
  expect(verifier.verify(proof, { root: 12345 })).toBe(false);
});

test("refuses a non-member", () => {
  expect(() => prover.prove({ ...inputs, leaf: 8 })).toThrow();
  expect(() => prover.prove(short)).toThrow(/siblings/);
});
