// The Poseidon2 exports a client computes commitments, nullifiers and encrypted
// notes with, against `gadgets/xark-poseidon2/poseidon2_ref.py`'s vectors (the
// same ones `gadgets/xark-poseidon2/tests/modes.rs` checks the circuit with).
// Needs no circuit: run after `wasm-pack build crates/wasm --target nodejs --dev
// --out-dir crates/wasm/dist/node`.
const test = require("node:test");
const assert = require("node:assert/strict");

const {
  poseidon2, poseidon2Commit, poseidon2Nullifier, poseidon2Encrypt, poseidon2Decrypt,
} = require("../dist/node/xark_wasm.js");

const COMMIT_123 = "17634564540255296520186148110660714497980376341407394513010947673015055999934";
const NULLIFIER_123 = "1583281705540343901485297543298824336757279061095191133038142125609155856497";
const HASH_123 = "8643882004926979398976878054694415684746477902129629285229035462626682758314";
// encrypt(key = 123456789, nonce = 42, [10, 11, 12]): the ciphertext, then the tag.
const ENC_3 = [
  "542663946192589838133460107101816892738666137983613942915370787155408987833",
  "4154875339721954462662900302236641642615963054759252672359497994734470297905",
  "14618528529411687673436746933590505467544694387242946331906959716917406637884",
  "14505114595764655204677295775782525172158035260596553999717939141079569455416",
];

test("commit, nullifier and hash are the reference's, and differ", () => {
  assert.equal(poseidon2Commit(["1", "2", "3"]), COMMIT_123);
  assert.equal(poseidon2Nullifier(["1", "2", "0x3"]), NULLIFIER_123);
  assert.equal(poseidon2(["1", "2", "3"]), HASH_123);
  assert.throws(() => poseidon2Commit([]), /at least one/);
});

test("encrypt gives the reference ciphertext and tag, and decrypt inverts it", () => {
  const out = poseidon2Encrypt("123456789", "42", ["10", "11", "12"]);
  assert.deepEqual(out, ENC_3);
  const tag = out.pop();
  assert.deepEqual(poseidon2Decrypt("123456789", "42", out, tag), ["10", "11", "12"]);
});

test("decrypt refuses a wrong key or nonce, or a changed ciphertext or tag", () => {
  const ct = ENC_3.slice(0, 3);
  const tag = ENC_3[3];
  const bump = (s) => (BigInt(s) + 1n).toString();
  assert.throws(() => poseidon2Decrypt("123456788", "42", ct, tag), /tag/);
  assert.throws(() => poseidon2Decrypt("123456789", "43", ct, tag), /tag/);
  assert.throws(() => poseidon2Decrypt("123456789", "42", [ct[0], bump(ct[1]), ct[2]], tag), /tag/);
  assert.throws(() => poseidon2Decrypt("123456789", "42", ct, bump(tag)), /tag/);
});
