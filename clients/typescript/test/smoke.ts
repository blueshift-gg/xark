// Smoke test: verify a real cube proof through the library, confirm a tampered
// proof is rejected, and exercise the typed public-signals inference.
//
//   npm install && npm test
//
// Fixtures (`cube.idl.ts`, `cube.proof.json`) are produced by the xark CLI:
//   xark prove examples/cube --input secret=3 --input result=27

import { XarkClient, type ProofBundle } from "../src/index";
import { cubeIdl } from "./cube.idl";
import bundle from "./cube.proof.json";

async function main() {
  const client = new XarkClient(cubeIdl);
  console.log(`circuit: ${client.name}, public signals: ${client.publicSignalOrder.join(", ")}`);

  const ok = await client.verify(bundle as ProofBundle);
  const signals = client.publicSignals(bundle as ProofBundle);
  // Compile-time proof of typing: `.result` is known from the IDL, not `any`.
  const result: string = signals.result;
  console.log(`verify(valid) = ${ok}, result = ${result}`);

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
