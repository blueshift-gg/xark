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
import { existsSync, readFileSync } from "node:fs";
import { dirname, join } from "node:path";

/** The project `from` is in: the nearest directory with a `xark.toml`. */
export function projectRoot(from = process.cwd()) {
  for (let dir = from; ; dir = dirname(dir)) {
    if (existsSync(join(dir, "xark.toml"))) return dir;
    if (dirname(dir) === dir) throw new Error(`no xark.toml in ${from} or above it: not in a xark project`);
  }
}

/**
 * A build output directory (`target/xark/<name>/`), as a prover takes it, with
 * the keys in `keys` (by default the same directory).
 */
export function artifacts(dir, keys = dir) {
  const read = (d, f) => new Uint8Array(readFileSync(join(d, f)));
  if (!existsSync(join(keys, "pk.bin"))) throw new Error(`no proving key in ${keys}: run \`xark build\``);
  return {
    circuit: read(dir, "circuit.xbc"),
    provingKey: read(keys, "pk.bin"),
    verifyingKey: read(keys, "vk.bin"),
    sources: readFileSync(join(dir, "sources.json"), "utf8"),
    client: existsSync(join(dir, "client.wasm")) ? read(dir, "client.wasm") : undefined,
  };
}

/**
 * Circuit `name`'s build output (`circuits/<name>/target/xark/<name>/`) and keys
 * (`keys/<name>/`) in the project.
 */
export function circuit(name, root = projectRoot()) {
  return artifacts(join(root, "circuits", name, "target", "xark", name), join(root, "keys", name));
}

/** Program `name`'s build: `target/deploy/<name>_program.so` in the project. */
export function program(name, root = projectRoot()) {
  return join(root, "target", "deploy", `${name.replaceAll("-", "_")}_program.so`);
}

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
