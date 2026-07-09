// xark-client — verify xark zero-knowledge proofs and build on-chain calldata.
//
// Construct a client from a circuit's snarkjs verifying key (written by
// `xark setup` as `snarkjs-verification_key.json`), then verify the proof
// bundles `xark prove` produces:
//
//   import { XarkClient } from "xark-client";
//   import vk from "./verification_key.json";
//
//   const client = new XarkClient(vk);
//   await client.verify(bundle);          // snarkjs verify
//   const data = client.calldata(bundle); // packed proof ‖ public bytes
//
// Proving happens in the `xark` CLI (`xark prove …`): snarkjs can verify an
// xark proof but cannot generate one, so there is no `prove` here by design.

import * as snarkjs from "snarkjs";

/** A snarkjs Groth16 proof. */
export interface SnarkjsProof {
  pi_a: string[];
  pi_b: string[][];
  pi_c: string[];
  protocol: string;
  curve: string;
}

/** A proof bundle as written by `xark prove` (`<name>-<hash>.proof.json`). */
export interface ProofBundle {
  circuit: string;
  circuit_hash: string;
  proof_sha256: string;
  public_signals: string[];
  proof: SnarkjsProof;
  calldata: {
    endianness: string;
    hex: string;
    proof_hex: string;
    public_inputs_hex: string;
  };
}

/** Decode a `0x…`/bare hex string into bytes (browser- and Node-safe). */
export function hexToBytes(hex: string): Uint8Array {
  const h = hex.startsWith("0x") ? hex.slice(2) : hex;
  if (h.length % 2 !== 0) throw new Error("hexToBytes: odd-length hex string");
  // Reject non-hex up front — otherwise a bad pair parses to NaN, which
  // Uint8Array silently coerces to 0 (wrong bytes, no error).
  if (!/^[0-9a-fA-F]*$/.test(h)) throw new Error("hexToBytes: invalid hex string");
  const out = new Uint8Array(h.length / 2);
  for (let i = 0; i < out.length; i++) {
    out[i] = parseInt(h.slice(i * 2, i * 2 + 2), 16);
  }
  return out;
}

/**
 * A verifier for one circuit, built from its snarkjs verifying key (the
 * `snarkjs-verification_key.json` `xark setup` writes).
 */
export class XarkClient {
  constructor(readonly verifyingKey: unknown) {}

  /** Verify a proof bundle (as written by `xark prove`) with snarkjs. */
  verify(bundle: ProofBundle): Promise<boolean> {
    return this.verifyRaw(bundle.proof, bundle.public_signals);
  }

  /** Verify a raw snarkjs proof against ordered public signals. */
  verifyRaw(proof: SnarkjsProof, publicSignals: string[]): Promise<boolean> {
    return snarkjs.groth16.verify(this.verifyingKey, publicSignals, proof);
  }

  /**
   * The packed verifier calldata: `proof (256 B) || public_inputs (N * 32 B)`,
   * little-endian — what a verifier built with `xark export` consumes. Your
   * program owns the accounts and any instruction discriminator; drop these
   * bytes where your verifier expects the proof.
   */
  calldata(bundle: ProofBundle): Uint8Array {
    return hexToBytes(bundle.calldata.hex);
  }
}
