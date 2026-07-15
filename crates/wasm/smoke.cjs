// Smoke test for xark-wasm `prove()` + `verify()` against the pre-built `cube`
// example (secret^3 == result). Run from the repo root after:
//   wasm-pack build crates/wasm --target nodejs --dev --out-dir crates/wasm/pkg-node
//   node crates/wasm/smoke.cjs
//
// Reads the self-contained binary `circuit.xbc` (the default `xark build`
// artifact) — no JSON circuit files needed. Requires the cube example rebuilt
// with a current `xark` (one that writes `circuit.xbc`).
//
// Set CIRCUIT_ARTIFACTS_DIR to override the artifact directory (useful in CI
// when artifacts live under a different path, e.g. `target/test-out/cube`).
const { join } = require("path");
const { readFileSync } = require("fs");
const assert = require("assert");

const { prove, verify, circuit_inputs, version, preload, prove_preloaded, proof_to_snarkjs_json, public_inputs_to_snarkjs_json } = require("./pkg-node/xark_wasm.js");

const D = process.env.CIRCUIT_ARTIFACTS_DIR
  || join(__dirname, "..", "..", "examples", "cube", "target", "xark", "cube");
const xbc = new Uint8Array(readFileSync(join(D, "circuit.xbc")));
const pk = new Uint8Array(readFileSync(join(D, "pk.bin")));
const vk = new Uint8Array(readFileSync(join(D, "vk.bin"))); // host-written verifying key
const hostPublic = readFileSync(join(D, "public_inputs.bin"));
const hostSnarkPublic = readFileSync(join(D, "snarkjs-public.json"), "utf8").trim();

console.log("version       :", version());
console.log("circuit_inputs:", circuit_inputs(xbc));

// circuit_inputs() uses the lightweight header-only parser; assert it returns
// the declared inputs in declaration order with correct roles.
assert.deepStrictEqual(
  JSON.parse(circuit_inputs(xbc)),
  [{ name: "secret", role: "private" }, { name: "result", role: "public" }],
  "circuit_inputs must list declared inputs in order with roles",
);

// --- prove: 3^3 = 27 ---
const p27 = prove(xbc, pk, JSON.stringify({ secret: "3", result: "27" }));
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
  JSON.parse(public_inputs_to_snarkjs_json(p27.publicInputs)), JSON.parse(hostSnarkPublic),
  "wasm snarkjs public must match host snarkjs-public.json",
);
const sj = JSON.parse(proof_to_snarkjs_json(p27.proof));
assert.strictEqual(sj.protocol, "groth16");
assert.strictEqual(sj.curve, "bn128");
assert.ok(Array.isArray(sj.pi_a) && sj.pi_a.length === 3, "pi_a is a G1 point");

// --- prove: 2^3 = 8 (a second, satisfiable instance) ---
const p8 = prove(xbc, pk, JSON.stringify({ secret: "2", result: "8" }));
assert.deepStrictEqual(JSON.parse(public_inputs_to_snarkjs_json(p8.publicInputs)), ["8"], "p8 public = [8]");

// --- verify: round-trip with the HOST vk.bin (full wasm-proof / host-key interop) ---
assert.strictEqual(verify(vk, p27.proof, p27.publicInputs), true, "verify(27) round-trip");
assert.strictEqual(verify(vk, p8.proof, p8.publicInputs), true, "verify(8) round-trip");

// --- preload + prove_preloaded: must produce a proof that verifies under the same vk ---
preload(xbc, pk);
const pf = prove_preloaded(JSON.stringify({ secret: "3", result: "27" }));
assert.deepStrictEqual(
  Buffer.from(pf.publicInputs), Buffer.from(p27.publicInputs),
  "prove_preloaded public inputs match one-shot prove",
);
assert.strictEqual(verify(vk, pf.proof, pf.publicInputs), true, "prove_preloaded proof verifies");
console.log("prove_preloaded : ok (", pf.proof.length, "B proof )");

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
try { prove(xbc, pk, JSON.stringify({ secret: "3", result: "26" })); }
catch (e) { threw = true; console.log("invalid witness  : rejected ->", String(e).slice(0, 60)); }
assert.ok(threw, "an unsatisfiable witness must throw");

console.log("\nALL CHECKS PASSED ✅  (prove + verify, true & false cases)");
