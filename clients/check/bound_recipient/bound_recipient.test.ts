// The generated `bound_recipient` client (`xark client`) through xark-wasm: an
// `Address` input is @solana/kit's `Address` (or its bytes) going in, and an `Address`
// coming back. `npm test` runs it, after setup.ts builds the example and its keys.
import { address, generateKeyPairSigner, getAddressEncoder, type Address } from "@solana/kit";
import { artifacts } from "../artifacts";
import { BoundRecipient, BoundRecipientProver, BoundRecipientVerifier, toHex } from "./bound_recipient";

// f1e2d3c4b5a69788796a5b4c3d2e1f00 00112233445566778899aabbccddeeff: above p, so
// neither half may be reduced on the way in.
const alice = address("HHDs1nrQ4yPMCTW79vBSPt7V9hXyhsJMTG5bkv9BjBxr");
const hex = "0xf1e2d3c4b5a69788796a5b4c3d2e1f0000112233445566778899aabbccddeeff";

let prover: BoundRecipientProver;
let verifier: BoundRecipientVerifier;
beforeAll(async () => {
  prover = await BoundRecipient.prover(artifacts("bound_recipient"));
  verifier = await BoundRecipient.verifier(artifacts("bound_recipient"));
});

test("an address goes in as an Address or its bytes, and comes back an Address", async () => {
  const proof = prover.prove({ x: 3, y: 9, recipient: alice });
  const back: Address = proof.publicInputs.recipient;
  expect(back).toBe(alice);
  expect(verifier.verify(proof, { y: 9, recipient: alice })).toBe(true);
  // Its 32 bytes, as kit encodes them, are the same address.
  const bytes = new Uint8Array(getAddressEncoder().encode(alice));
  expect(toHex(bytes)).toBe(hex);
  expect(verifier.verify(proof.toBytes(), { y: 9, recipient: bytes })).toBe(true);
  // Bound: another address doesn't verify. A signer's (as the testing module's
  // `funded` gives one) passes as it is.
  const other = await generateKeyPairSigner();
  expect(verifier.verify(proof, { y: 9, recipient: other.address })).toBe(false);
  expect(prover.prove({ x: 3, y: 9, recipient: other.address }).publicInputs.recipient).toBe(other.address);
});

test("the proof's last two field elements are the address's halves", () => {
  const fields = prover.prove({ x: 3, y: 9, recipient: alice }).toFields();
  expect(fields.length).toBe(3 * 32);
  // Each half big-endian, as a little-endian element: its 16 bytes reversed, then zeros.
  const half = (h: string) => [...Buffer.from(h, "hex").reverse(), ...new Uint8Array(16)];
  expect([...fields.slice(32)]).toEqual([...half(hex.slice(2, 34)), ...half(hex.slice(34))]);
});

test("refuses what isn't an address", () => {
  // @ts-expect-error: a plain string isn't an `Address` (tsc checks this line)
  const loose: Parameters<BoundRecipientProver["prove"]>[0] = { x: 3, y: 9, recipient: "0OIl" };
  expect(() => prover.prove(loose)).toThrow(/recipient.*base58/);
  expect(() => prover.prove({ x: 3, y: 9, recipient: new Uint8Array(31) })).toThrow(/recipient.*32 bytes/);
});
