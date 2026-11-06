import type { ProofBundle } from "../dist/web/xark_wasm.js";

export interface StreamProveOptions {
  /** `r1cs.stream` bytes, for a key `xark setup` generated in the `minimized` form. */
  r1cs?: Uint8Array | ArrayBuffer;
  /** Worker pool from `@blueshift-gg/xark-wasm/pool` (needs SharedArrayBuffer). */
  pool?: unknown;
  /** Proving-key points folded per MSM chunk (default 2^18). */
  msmChunk?: number;
  /**
   * QAP domain size of the key (`qap_domain_size` in `metadata.json`). Optional:
   * the key's header states it, and `h` is computed when the header arrives; with
   * this, `h` is computed up front instead (before any key bytes).
   */
  domainSize?: number;
  /** Testing only: deterministic prover randomness. */
  seed?: number;
  /** Called after each chunk with the key bytes consumed so far. */
  onProgress?: (bytesReceived: number) => void;
}

/** Prove while `pk.bin` downloads, never holding the key in memory. */
export function proveFromStream(
  xark: {
    beginStreamingProof(xbc: Uint8Array | ArrayBuffer, inputs: object, options?: object): {
      push(chunk: Uint8Array): void;
      readonly received: number;
      finish(): ProofBundle;
      free(): void;
    };
  },
  circuitXbc: Uint8Array | ArrayBuffer,
  key: ReadableStream<Uint8Array> | Response | Promise<Response>,
  inputs: object,
  options?: StreamProveOptions,
): Promise<ProofBundle>;

/** Re-encode `pk.bin` with uncompressed points as a stream (store it, prove from it later). */
export function transcodeKey(
  xark: { beginKeyTranscode(options?: object): { push(chunk: Uint8Array): Uint8Array; readonly complete: boolean; free(): void } },
  key: ReadableStream<Uint8Array> | Response | Promise<Response>,
  options?: { pool?: unknown },
): ReadableStream<Uint8Array>;
