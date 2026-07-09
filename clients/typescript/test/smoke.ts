// Smoke test: verify a real cube proof through the library and confirm a
// tampered proof is rejected.
//
//   npm install && npm test
//
// Fixtures (`cube.vk.json`, `cube.proof.json`) are produced by the xark CLI:
//   xark setup examples/cube && xark prove examples/cube --input secret=3 --input result=27

import { XarkClient, type ProofBundle } from "../src/index";
import vk from "./cube.vk.json";
import bundle from "./cube.proof.json";

async function main() {
  const client = new XarkClient(vk);

  const ok = await client.verify(bundle as ProofBundle);
  console.log(`verify(valid) = ${ok}`);

  const tampered = { ...bundle, public_signals: ["999"] } as ProofBundle;
  const bad = await client.verify(tampered);
  console.log(`verify(tampered) = ${bad}`);

  if (!ok || bad) {
    console.error("❌ SMOKE FAILED");
    process.exit(1);
  }
  console.log("✅ xark-client smoke passed");
  // snarkjs keeps worker threads alive; exit explicitly so the process ends.
  process.exit(0);
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
