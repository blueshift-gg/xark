// Prove `{{circuit}}` with its generated client, then verify the proof onchain with
// the `{{name}}` program in LiteSVM. `xark build` makes what this reads.
import { generateKeyPairSigner, type Address } from "@solana/kit";
import { circuit, funded, program, send, vm } from "@blueshift-gg/xark/testing";
import { {{Pascal}}, type {{Pascal}}Inputs, type {{Pascal}}Prover } from "../clients/{{circuit}}/ts/{{circuit_file}}";

{{inputs_doc}}const INPUTS: {{Pascal}}Inputs = {{inputs}};

let id: Address;
let prover: {{Pascal}}Prover;
beforeAll(async () => {
  id = (await generateKeyPairSigner()).address; // the program takes any address
  // Pinned to the circuit this client was generated from.
  prover = await {{Pascal}}.prover(circuit("{{circuit}}"), { digest: {{Pascal}}.digest });
});

/** `Verify`: its discriminator (0), then the proof and its public inputs. */
const verify = (data: Uint8Array) => ({ programAddress: id, data: new Uint8Array([0, ...data]) });

test("a proof verifies onchain", async () => {
  const proof = prover.prove(INPUTS);
  const svm = vm({ [id]: program("{{name}}") });
  const payer = await funded(svm);

  await send(svm, payer, verify(proof.toInstructionData()));

  const tampered = proof.toInstructionData();
  tampered[0] ^= 1;
  await expect(send(svm, payer, verify(tampered))).rejects.toThrow(/InvalidProof/);
});
