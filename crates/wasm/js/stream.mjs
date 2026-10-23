// Prove while the proving key downloads: feed a ReadableStream (e.g. a fetch
// Response body) into the push-driven prover. The key is never held in memory —
// each chunk of points is folded into its MSM and dropped — and the witness and
// quotient polynomial are computed before the first key byte is needed.
//
//   import * as xark from "@blueshift-gg/xark-wasm";
//   import { proveFromStream } from "@blueshift-gg/xark-wasm/stream";
//   const out = await proveFromStream(xark, xbc, fetch("/circuit/pk.bin"), inputs);
//
// No SharedArrayBuffer or cross-origin isolation needed. Pass `options.pool` to
// add worker threads (that part does need them, and a non-main thread).

/**
 * @param {typeof import("../dist/web/xark_wasm.js")} xark  the initialized module
 * @param {Uint8Array | ArrayBuffer} circuitXbc
 * @param {ReadableStream<Uint8Array> | Response | Promise<Response>} key  pk.bin
 * @param {object} inputs
 * @param {object} [options]  as proveStreaming, plus `onProgress(bytesReceived)`
 */
export async function proveFromStream(xark, circuitXbc, key, inputs, options = {}) {
  const proof = xark.beginStreamingProof(circuitXbc, inputs, options);
  try {
    let src = await key;
    if (src && typeof src === "object" && "body" in src && !(src instanceof ReadableStream)) {
      if (src.ok === false) throw new Error(`fetching proving key: HTTP ${src.status}`);
      src = src.body;
    }
    const reader = src.getReader();
    for (;;) {
      const { done, value } = await reader.read();
      if (done) break;
      proof.push(value);
      options.onProgress?.(proof.received);
    }
    return proof.finish();
  } finally {
    proof.free();
  }
}

/**
 * Re-encode a proving key with uncompressed points, as a stream: pipe it to
 * storage (OPFS, IndexedDB, the Cache API) once, then prove from the stored
 * copy — later proofs skip every point's square root (the dominant cost of a
 * WASM proof), at twice the key's size.
 *
 *   const decoded = transcodeKey(xark, fetch("/circuit/pk.bin"), { pool });
 *   await decoded.pipeTo(opfsFile.createWritable());
 *
 * @returns {ReadableStream<Uint8Array>}
 */
export function transcodeKey(xark, key, options = {}) {
  const t = xark.beginKeyTranscode(options);
  let reader;
  return new ReadableStream({
    async pull(controller) {
      try {
        if (!reader) {
          let src = await key;
          if (src && typeof src === "object" && "body" in src && !(src instanceof ReadableStream)) {
            if (src.ok === false) throw new Error(`fetching proving key: HTTP ${src.status}`);
            src = src.body;
          }
          reader = src.getReader();
        }
        for (;;) {
          const { done, value } = await reader.read();
          if (done) {
            if (!t.complete) throw new Error("proving key ended early");
            t.free();
            controller.close();
            return;
          }
          const out = t.push(value);
          if (out.length) {
            controller.enqueue(out);
            return;
          }
        }
      } catch (e) {
        t.free();
        controller.error(e);
      }
    },
  });
}
