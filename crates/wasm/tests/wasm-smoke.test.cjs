// xark-wasm smoke test: `prove()` + `verify()` (+ preloading + public-input decoding)
// against the pre-built `cube` example (secret^3 == result). Run from anywhere
// after:
//   wasm-pack build crates/wasm --target nodejs --dev --out-dir crates/wasm/dist/node
//   node --test crates/wasm/tests/wasm-smoke.test.cjs
//
// Uses Node's built-in test runner (`node:test`) — no JS dependencies. Reads
// the self-contained binary `circuit.xbc` (the default `xark build` artifact),
// so no JSON circuit files are needed. Requires the cube example rebuilt with a
// current `xark` (one that writes `circuit.xbc`).
//
// Set CIRCUIT_ARTIFACTS_DIR to override the artifact directory (useful in CI,
// when artifacts live under a different path, e.g. `target/test-out/cube`).
const test = require("node:test");
const assert = require("node:assert/strict");
const { join } = require("node:path");
const { readFileSync } = require("node:fs");

const {
  prove, verify, preload, prove_preloaded,
  decode_public_inputs,
} = require("../dist/node/xark_wasm.js");

const D = process.env.CIRCUIT_ARTIFACTS_DIR
  || join(__dirname, "..", "..", "..", "examples", "cube", "target", "xark", "cube");
const xbc = new Uint8Array(readFileSync(join(D, "circuit.xbc")));
const pk = new Uint8Array(readFileSync(join(D, "pk.bin")));
const vk = new Uint8Array(readFileSync(join(D, "vk.bin"))); // host-written verifying key
const hostPublic = readFileSync(join(D, "public_inputs.bin"));

// Prove two satisfiable instances once and reuse them across cases.
const p27 = prove(xbc, pk, { secret: "3", result: "27" });
const p8 = prove(xbc, pk, { secret: "2", result: "8" });

test("prove(3->27) yields a non-empty proof with exactly 1 public input", () => {
  assert.ok(p27.proof.length > 0, "proof must be non-empty");
  assert.strictEqual(p27.numPublicInputs, 1, "cube has 1 public input");
});

test("wasm publicInputs are byte-identical to the host public_inputs.bin", () => {
  assert.deepStrictEqual(Buffer.from(p27.publicInputs), Buffer.from(hostPublic));
});

test("decode_public_inputs reads the host public_inputs.bin", () => {
  assert.deepStrictEqual(decode_public_inputs(hostPublic), ["27"]);
});

test("prove(2->8) public inputs are ['8']", () => {
  assert.deepStrictEqual(decode_public_inputs(p8.publicInputs), ["8"]);
});

test("verify round-trips under the host vk.bin (both 27 and 8)", () => {
  assert.strictEqual(verify(vk, p27.proof, p27.publicInputs), true, "verify(27) round-trip");
  assert.strictEqual(verify(vk, p8.proof, p8.publicInputs), true, "verify(8) round-trip");
});

test("preload + prove_preloaded produce a proof that verifies under the same vk", () => {
  preload(xbc, pk);
  const pf = prove_preloaded({ secret: "3", result: "27" });
  assert.deepStrictEqual(
    Buffer.from(pf.publicInputs), Buffer.from(p27.publicInputs),
    "prove_preloaded public inputs match one-shot prove",
  );
  assert.strictEqual(verify(vk, pf.proof, pf.publicInputs), true, "prove_preloaded proof verifies");
});

test("verify returns false on proof/public-input mismatch", () => {
  assert.strictEqual(verify(vk, p8.proof, p27.publicInputs), false, "proof(8) vs public(27) must fail");
  assert.strictEqual(verify(vk, p27.proof, p8.publicInputs), false, "proof(27) vs public(8) must fail");
});

test("verify throws on a malformed proof (does not silently return false)", () => {
  assert.throws(() => verify(vk, new Uint8Array([0, 1, 2, 3]), p27.publicInputs));
});

test("prove throws on an unsatisfiable witness", () => {
  // Named as the inputs' fault, not the key's, with the failing constraint.
  assert.throws(
    () => prove(xbc, pk, { secret: "3", result: "26" }),
    /inputs don't satisfy the circuit: constraint #\d+ fails/,
  );
});

test("prove names the failing source line given sources.json", () => {
  const sources = readFileSync(join(D, "sources.json"), "utf8");
  assert.throws(
    () => prove(xbc, pk, { secret: "3", result: "26" }, sources),
    /the inputs fail the check at src\/lib\.rs:\d+:\d+: `.+`/,
  );
  assert.throws(() => prove(xbc, pk, { secret: "3", result: "26" }, "{"), /parsing sources\.json/);
});

test("byte args accept a raw ArrayBuffer (browser response.arrayBuffer() flow)", () => {
  const ab = (u8) => new Uint8Array(u8).buffer;
  const { proof, publicInputs } = prove(ab(xbc), ab(pk), { secret: "3", result: "27" });
  assert.ok(proof.length > 0, "ArrayBuffer circuit/pk must still prove");
  assert.strictEqual(
    verify(ab(vk), ab(proof), ab(publicInputs)), true,
    "verify must accept ArrayBuffer vk/proof/publicInputs",
  );
});

test("byte args reject a non-bytes value with a clear message", () => {
  assert.throws(
    () => prove("not-bytes", pk, { secret: "3", result: "27" }),
    /Uint8Array or ArrayBuffer/,
  );
  assert.throws(
    () => verify({}, p27.proof, p27.publicInputs),
    /Uint8Array or ArrayBuffer/,
  );
});

test("inputs take numbers, bigints, and 0x-hex", () => {
  for (const inputs of [
    { secret: 3, result: 27 },
    { secret: 3n, result: 27n },
    { secret: "0x03", result: "0x1b" },
  ]) {
    const out = prove(xbc, pk, inputs);
    assert.deepStrictEqual(decode_public_inputs(out.publicInputs), ["27"]);
  }
});

test("numbers outside the safe-integer range are rejected, not rounded", () => {
  assert.throws(() => prove(xbc, pk, { secret: 3, result: 2 ** 60 }), /safe integer/);
});

test("an unknown input names the circuit's real inputs", () => {
  assert.throws(() => prove(xbc, pk, { secrett: 3, result: 27 }), /unknown input `secrett`.*secret/);
});
