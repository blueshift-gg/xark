// The generated `sha256` client (`xark client`) through xark-wasm. `npm test` runs it,
// after setup.ts builds the example and its keys.
import { artifacts } from "../artifacts";
import { Sha256, Sha256Prover, Sha256Verifier, fromHex, toHex } from "./sha256";

// sha256("abc"): a `Hash` is its 32 bytes (given as hex here, through `fromHex`).
const digest = fromHex("0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
const msg = new TextEncoder().encode("abc");

let prover: Sha256Prover;
let verifier: Sha256Verifier;
beforeAll(async () => {
  prover = await Sha256.prover(artifacts("sha256"));
  verifier = await Sha256.verifier(artifacts("sha256"));
});

test("proves a preimage", () => {
  const proof = prover.prove({ msg, digest });
  expect(proof.publicInputs.digest).toBeInstanceOf(Uint8Array);
  expect(proof.publicInputs.digest).toHaveLength(32);
  expect(verifier.verify(proof)).toBe(true);
  expect(verifier.verify(proof, { digest })).toBe(true);
  const other = digest.slice();
  other[31] ^= 1;
  expect(verifier.verify(proof, { digest: other })).toBe(false);
  expect(toHex(proof.publicInputs.digest)).toBe(toHex(digest));
  // Bytes are a `Uint8Array`: hex goes through `fromHex`, and anything else doesn't compile.
  // @ts-expect-error: a hex string isn't bytes (tsc checks this line)
  const asHex: Parameters<Sha256Prover["prove"]>[0] = { msg: "0x616263", digest };
  expect(asHex.msg).toBe("0x616263");
  expect(() => fromHex("0x6g")).toThrow(/not hex bytes/);
  // Only bytes go to hex, and only a string comes from it (plain JS gets a clear error).
  expect(() => toHex("ab" as unknown as Uint8Array)).toThrow(/expected a Uint8Array/);
  expect(() => toHex([300] as unknown as Uint8Array)).toThrow(/expected a Uint8Array/);
  expect(() => fromHex(123 as unknown as string)).toThrow(/expected a string, got number/);
  expect(fromHex("616263")).toEqual(msg);
});

test("refuses bad inputs", () => {
  expect(() => prover.prove({ msg, digest: new Uint8Array(1) })).toThrow(/digest/); // a short hash
  expect(() => prover.prove({ msg: new TextEncoder().encode("abd"), digest })).toThrow(); // the wrong message
  expect(() => prover.prove({ msg: new TextEncoder().encode("ab"), digest })).toThrow(/msg/); // a short message
});
