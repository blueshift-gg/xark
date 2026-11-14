// The Poseidon2 exports a client computes commitments and nullifiers with,
// against `gadgets/xark-poseidon2/poseidon2_ref.py`'s vectors (the same ones
// `gadgets/xark-poseidon2/tests/modes.rs` checks the circuit with).
// Needs no circuit: run after `wasm-pack build crates/wasm --target nodejs --dev
// --out-dir crates/wasm/dist/node`.
const test = require("node:test");
const assert = require("node:assert/strict");

const { poseidon2, poseidon2Commit, poseidon2Nullifier } = require("../dist/node/xark_wasm.js");

const COMMIT_123 = "17634564540255296520186148110660714497980376341407394513010947673015055999934";
const NULLIFIER_123 = "1583281705540343901485297543298824336757279061095191133038142125609155856497";
const HASH_123 = "8643882004926979398976878054694415684746477902129629285229035462626682758314";

test("commit, nullifier and hash are the reference's, and differ", () => {
  assert.equal(poseidon2Commit(["1", "2", "3"]), COMMIT_123);
  assert.equal(poseidon2Nullifier(["1", "2", "0x3"]), NULLIFIER_123);
  assert.equal(poseidon2(["1", "2", "3"]), HASH_123);
  assert.throws(() => poseidon2Commit([]), /at least one/);
});
