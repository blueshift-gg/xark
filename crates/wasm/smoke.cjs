// Smoke test for xark-wasm `prove()` + `verify()` against the pre-built `cube`
// example (secret^3 == result). Run from the repo root after:
//   wasm-pack build crates/wasm --target nodejs --dev --out-dir crates/wasm/pkg-node
//   node crates/wasm/smoke.cjs
const { join } = require("path");
const { readFileSync } = require("fs");
const assert = require("assert");

const { prove, verify, circuit_inputs, version } = require("./pkg-node/xark_wasm.js");

const D = join(__dirname, "..", "..", "examples", "cube", "target", "xark", "cube");
const r1cs = readFileSync(join(D, "r1cs.json"), "utf8");
const circuit = readFileSync(join(D, "circuit.json"), "utf8");
const pk = new Uint8Array(readFileSync(join(D, "pk.bin")));
const vk = new Uint8Array(readFileSync(join(D, "vk.bin"))); // host-written verifying key
const hostPublic = readFileSync(join(D, "public_inputs.bin"));
const hostSnarkPublic = readFileSync(join(D, "snarkjs-public.json"), "utf8").trim();

console.log("version       :", version());
console.log("circuit_inputs:", circuit_inputs(circuit));

// --- prove: 3^3 = 27 ---
const p27 = prove(r1cs, circuit, pk, JSON.stringify({ secret: "3", result: "27" }));
console.log(
  "prove(3->27)  :", p27.proof.length, "B proof;", p27.publicInputs.length, "B public;",
  p27.numPublicInputs, "public input(s)",
);
assert.ok(p27.proof.length > 0, "proof non-empty");
assert.strictEqual(p27.numPublicInputs, 1, "cube has 1 public input");
assert.deepStrictEqual(
  Buffer.from(p27.publicInputs), Buffer.from(hostPublic),
  "wasm publicInputs must match host public_inputs.bin",
);
assert.deepStrictEqual(
  JSON.parse(p27.snarkjsPublic), JSON.parse(hostSnarkPublic),
  "wasm snarkjsPublic must match host snarkjs-public.json",
);
const sj = JSON.parse(p27.snarkjsProof);
assert.strictEqual(sj.protocol, "groth16");
assert.strictEqual(sj.curve, "bn128");
assert.ok(Array.isArray(sj.pi_a) && sj.pi_a.length === 3, "pi_a is a G1 point");

// --- prove: 2^3 = 8 (a second, satisfiable instance) ---
const p8 = prove(r1cs, circuit, pk, JSON.stringify({ secret: "2", result: "8" }));
assert.deepStrictEqual(JSON.parse(p8.snarkjsPublic), ["8"], "p8 public = [8]");

// --- verify: round-trip with the HOST vk.bin (full wasm-proof / host-key interop) ---
assert.strictEqual(verify(vk, p27.proof, p27.publicInputs), true, "verify(27) round-trip");
assert.strictEqual(verify(vk, p8.proof, p8.publicInputs), true, "verify(8) round-trip");

// --- verify: negative — proof/public-input mismatch must return false ---
assert.strictEqual(verify(vk, p8.proof, p27.publicInputs), false, "proof(8) vs public(27) must fail");
assert.strictEqual(verify(vk, p27.proof, p8.publicInputs), false, "proof(27) vs public(8) must fail");

// --- verify: malformed proof must throw (not return false) ---
let threw = false;
try { verify(vk, new Uint8Array([0, 1, 2, 3]), p27.publicInputs); }
catch (e) { threw = true; console.log("garbage proof    : rejected ->", String(e).slice(0, 60)); }
assert.ok(threw, "a malformed proof must throw");

// --- prove: unsatisfiable witness must throw ---
threw = false;
try { prove(r1cs, circuit, pk, JSON.stringify({ secret: "3", result: "26" })); }
catch (e) { threw = true; console.log("invalid witness  : rejected ->", String(e).slice(0, 60)); }
assert.ok(threw, "an unsatisfiable witness must throw");

console.log("\nALL CHECKS PASSED ✅  (prove + verify, true & false cases)");
