// The generated `cube` client (`xark client`) through xark-wasm. `npm test` runs it,
// after setup.ts builds the example and its keys.
import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { artifacts, outDir, serve } from "../artifacts";
import { Circuit, Proof } from "@blueshift-gg/xark-wasm/client";
import { Cube, CubeProver, CubeVerifier, Field } from "./cube";
import cubeSchema from "./cube.schema.js";
import { Field as KycField } from "../zkyc/zkyc";

// The BN254 scalar field modulus: p + 3 would prove as 3 if it wrapped.
const p = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;
// A field input takes a `Field` or a plain integer; decoded values are `Field`s.
const inputs = { secret: 3, result: 27 };

let prover: CubeProver;
let verifier: CubeVerifier;
beforeAll(async () => {
  prover = await Cube.prover(artifacts("cube"));
  verifier = await Cube.verifier(artifacts("cube").verifyingKey);
});

test("proves and verifies", () => {
  const proof = prover.prove(inputs);
  expect(proof.publicInputs).toEqual({ result: new Field(27) });
  expect(proof.publicInputs.result.equals(27)).toBe(true);
  expect(verifier.verify(proof)).toBe(true);
  // Against the public inputs a verifier requires.
  expect(verifier.verify(proof, { result: new Field(27) })).toBe(true);
  expect(verifier.verify(proof, { result: 28 })).toBe(false);
});

test("a proof travels as its bytes, on-chain or compressed", () => {
  const proof = prover.prove(inputs);
  const [onChain, compressed] = [proof.toBytes(), proof.toBytesCompressed()];
  expect([onChain.length, compressed.length]).toEqual([256, 128]);
  // A verifier reads either, against the public inputs it requires.
  for (const bytes of [onChain, compressed]) {
    expect(verifier.verify(bytes, { result: 27 })).toBe(true);
    expect(verifier.verify(bytes, { result: new Field(28) })).toBe(false);
    expect(verifier.verify(bytes.slice(0, 10), { result: 27 })).toBe(false);
    const garbled = bytes.slice();
    garbled[10] ^= 0xff; // inside the proof: malformed, or another proof
    expect(verifier.verify(garbled, { result: 27 })).toBe(false);
  }
  // The bytes don't carry the public inputs: asking without them is a mistake.
  // @ts-expect-error: proof bytes need their public inputs (tsc checks this line)
  expect(() => verifier.verify(onChain)).toThrow(/don't carry its public inputs/);
});

test("a broken verifying key fails when the verifier is made", async () => {
  const vk = artifacts("cube").verifyingKey.slice(0, 40);
  await expect(Cube.verifier(vk)).rejects.toThrow(/verifying key/);
});

test("refuses bad inputs", () => {
  expect(() => prover.prove({ ...inputs, result: 28 })).toThrow();
  // Checked as a `Field` would be, naming the input: never wrapped or rounded.
  expect(() => prover.prove({ ...inputs, secret: p + 3n })).toThrow(/secret/);
  expect(() => prover.prove({ ...inputs, secret: -1 })).toThrow(/secret/);
  expect(() => prover.prove({ ...inputs, secret: 2 ** 53 + 2 })).toThrow(/`secret`: .* is not a safe integer/);
  expect(() => prover.prove({ ...inputs, secret: 1.5 })).toThrow(/`secret`: 1.5 is not an integer/);
  expect(() => prover.prove({ ...inputs, secret: "three" })).toThrow(/secret/);
  expect(prover.prove({ secret: new Field(3), result: 27n }).publicInputs.result.equals(27)).toBe(true);
});

test("a Field is checked when it's made", () => {
  // Every form is the same element.
  const three = new Field(3);
  for (const x of [3n, "3", " 3 ", "0x03", "0X03", new Uint8Array([3]), new Uint8Array(32).fill(3, 0, 1), three]) {
    expect(new Field(x).value).toBe(3n);
  }
  // A string reads as the prover reads it: decimal or 0x/0X hex, nothing else.
  expect(prover.prove({ ...inputs, secret: "0X03" }).publicInputs.result.equals(27)).toBe(true);
  for (const x of ["1_000", "+3", "0x", "3.0"]) {
    expect(() => new Field(x)).toThrow(/not a decimal or 0x-hex integer/);
    expect(() => prover.prove({ ...inputs, secret: x })).toThrow(/not a decimal or 0x-hex number/);
  }
  // Bytes are little-endian, as proofs and Rust's `Field::from_le_bytes` have them.
  expect(new Field(new Uint8Array([1, 2])).value).toBe(0x0201n);
  expect(Field.fromBeBytes(new Uint8Array([1, 2])).value).toBe(0x0102n);
  const big = new Field(p - 1n).toBytes();
  expect(big).toEqual(Uint8Array.from(Buffer.from((p - 1n).toString(16).padStart(64, "0"), "hex")).reverse());
  expect(new Field(big).value).toBe(p - 1n);
  expect(JSON.stringify({ x: three })).toBe('{"x":"3"}');
  // Every client re-exports the one `Field`.
  expect(KycField).toBe(Field);
  // Not below p, negative, inexact or malformed: refused, rather than wrapped.
  expect(() => new Field(p + 3n)).toThrow(/not below the field's modulus/);
  expect(() => new Field(new Uint8Array(32).fill(0xff))).toThrow(/not below the field's modulus/);
  expect(() => new Field(-1)).toThrow(/negative/);
  expect(() => new Field(2 ** 53)).toThrow(/not a safe integer/);
  expect(() => new Field(1.5)).toThrow(/1.5 is not an integer/);
  for (const s of ["", "-1", "1e3", "0x", "12abc"]) expect(() => new Field(s)).toThrow(/not a decimal or 0x-hex/);
  expect(() => new Field(new Uint8Array(33))).toThrow(/at most 32/);
  // @ts-expect-error: not a field element's form (tsc checks this line)
  expect(() => new Field(null)).toThrow(/can't make a field element/);
});

test("loads its build output from a URL", async () => {
  const server = await serve("cube");
  try {
    const proof = (await Cube.prover(server.url)).prove(inputs);
    // A verifier fetches only the verifying key, and can't prove.
    const fetched = await Cube.verifier(new URL(server.url));
    expect(fetched.verify(proof)).toBe(true);
    // @ts-expect-error: a verifier has no `prove` (tsc checks this line)
    expect(fetched.prove).toBeUndefined();
    await expect(Cube.prover(server.url + "missing/")).rejects.toThrow(/404/);
    await expect(Cube.verifier("/circuits/cube/")).rejects.toThrow(/pass an absolute URL/);
    // @ts-expect-error: proving needs the circuit and proving key (tsc checks this line)
    await expect(Cube.prover({ verifyingKey: artifacts("cube").verifyingKey })).rejects.toThrow(/needs `circuit`/);
  } finally {
    await server.close();
  }
});

test("a client from another xark release says so", () => {
  const schema = { version: 2, xark: "0.4.0", circuit: "c", inputs: [], types: {}, public_inputs: [] };
  const circuit = (xark?: string) => new Circuit({ name: "c", schema: { ...schema, xark }, decodePublic: () => ({}), client: false });
  expect(() => circuit("0.4.0")).toThrow(/generated by xark 0\.4\.0.*install @blueshift-gg\/xark-wasm@0\.4/);
  expect(() => circuit("0.3.7")).not.toThrow(); // the same release
  expect(() => circuit(undefined)).not.toThrow(); // before 0.3, schemas didn't say
  expect(cubeSchema.xark).toMatch(/^0\.3\./);
});

test("toBytes() is the proof an exported Solana verifier reads", () => {
  const proof = prover.prove(inputs);
  // Byte for byte what `xark export` makes of the same proof (its proof.solana.bin).
  const dir = mkdtempSync(join(tmpdir(), "xark-solana-"));
  writeFileSync(join(dir, "proof.bin"), proof.toBytesCompressed());
  writeFileSync(join(dir, "public_inputs.bin"), proof.publicInputBytes);
  const root = join(__dirname, "..", "..", "..");
  const xark = join(process.env.CARGO_TARGET_DIR ?? join(root, "target"), "release", "xark");
  execFileSync(xark, [
    "export", outDir("cube"), "--allow-insecure",
    "--proof", join(dir, "proof.bin"), "--public-inputs", join(dir, "public_inputs.bin"),
    "--out", join(dir, "verifier"),
  ], { stdio: "pipe" });
  expect(proof.toBytes()).toEqual(new Uint8Array(readFileSync(join(dir, "verifier", "proof.solana.bin"))));
  // Its public input, as the program would supply it: the `Field`'s 32 LE bytes.
  const onChainInputs = new Uint8Array(readFileSync(join(dir, "verifier", "public_inputs.solana.bin")));
  expect(proof.publicInputs.result.toBytes()).toEqual(onChainInputs);
  // A Proof made by hand has no xark-wasm to convert it; its compressed bytes are as given.
  const byHand = new Proof(proof.proofBytes, proof.publicInputs, proof.publicInputBytes);
  expect(() => byHand.toBytes()).toThrow(/make it with one/);
  expect(byHand.toBytesCompressed()).toEqual(proof.toBytesCompressed());
});
