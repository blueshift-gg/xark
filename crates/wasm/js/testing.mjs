// Testing a project's circuits and programs in Node: a circuit's build output, and a
// LiteSVM to send transactions to. An app would fetch the build output from a URL
// (`Circuit.prover("/circuits/<name>/")`) and send to an RPC instead; the clients and
// instructions are the same.
//
//   import { circuit, funded, program, send, vm } from "@blueshift-gg/xark/testing";
//   const prover = await Claim.prover(circuit("claim"));
//   const svm = vm({ [id]: program("claim") });
//   await send(svm, await funded(svm), { programAddress: id, data });
//
// Needs `litesvm` and `@solana/kit` beside this package.

import {
  appendTransactionMessageInstructions,
  createTransactionMessage,
  generateKeyPairSigner,
  lamports,
  pipe,
  setTransactionMessageFeePayerSigner,
  setTransactionMessageLifetimeUsingBlockhash,
  signTransactionMessageWithSigners,
} from "@solana/kit";
import { FailedTransactionMetadata, LiteSVM } from "litesvm";
import { artifacts, circuit, program, projectRoot } from "./testing/paths.mjs";

export { artifacts, circuit, program, projectRoot };

/** A fresh LiteSVM with each program (a `.so` path) at its address. */
export function vm(programs) {
  const svm = new LiteSVM();
  for (const [id, path] of Object.entries(programs)) svm.addProgramFromFile(id, path);
  return svm;
}

/** A new keypair holding `sol` SOL. */
export async function funded(svm, sol = 10n) {
  const signer = await generateKeyPairSigner();
  svm.airdrop(signer.address, lamports(sol * 1_000_000_000n));
  return signer;
}

/**
 * Sign `instructions` with `payer` (and any signers they name) and send them. Throws
 * with the program's logs if the transaction fails, so a test can match the error.
 */
export async function send(svm, payer, ...instructions) {
  const tx = await pipe(
    createTransactionMessage({ version: 0 }),
    (m) => setTransactionMessageFeePayerSigner(payer, m),
    (m) => setTransactionMessageLifetimeUsingBlockhash({ blockhash: svm.latestBlockhash(), lastValidBlockHeight: 0n }, m),
    (m) => appendTransactionMessageInstructions(instructions, m),
    (m) => signTransactionMessageWithSigners(m),
  );
  const result = svm.sendTransaction(tx);
  // A new blockhash, so sending the same instructions again is a new transaction.
  svm.expireBlockhash();
  if (result instanceof FailedTransactionMetadata) {
    throw new Error(`transaction failed: ${result.err()}\n${result.meta().logs().join("\n")}`);
  }
  return result;
}
