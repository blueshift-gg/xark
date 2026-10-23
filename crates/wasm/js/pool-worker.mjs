// A pool worker (Node worker_threads or a browser module Worker): one wasm
// instance running the prover's kernels on slices of SharedArrayBuffers, then
// signalling the shared completion counter (see pool.mjs).

const IS_NODE = typeof process !== "undefined" && !!process.versions?.node;

let wasm;

function cols(job) {
  // Gather an N1 × b tile (one contiguous run per row), transform, scatter back.
  const { n1, n2, c0: start, c1, tile, op } = job;
  const data = new Uint8Array(job.data);
  const block = new Uint8Array(n1 * tile * 32);
  for (let c0 = start; c0 < c1; c0 += tile) {
    const run = Math.min(tile, c1 - c0) * 32;
    const blk = block.subarray(0, n1 * run);
    for (let r = 0; r < n1; r++) {
      const off = (r * n2 + c0) * 32;
      blk.set(data.subarray(off, off + run), r * run);
    }
    wasm.kernel_cols(blk, n1, n2, c0, op);
    for (let r = 0; r < n1; r++) data.set(blk.subarray(r * run, (r + 1) * run), (r * n2 + c0) * 32);
  }
}

function rows(job) {
  const { n1, n2 } = job;
  const view = new Uint8Array(job.data, job.r0 * n2 * 32, (job.r1 - job.r0) * n2 * 32);
  wasm.kernel_rows(view, n1, n2, job.r0, job.toCoset);
}

function msm(job) {
  const pts = new Uint8Array(job.pts, job.ptsOff, job.ptsLen);
  const sc = new Uint8Array(job.sc, job.scOff, job.scLen);
  const sum = wasm.kernel_msm(job.g2, pts, job.compressed, sc);
  new Uint8Array(job.out, job.outOff, sum.length).set(sum);
}

function decompress(job) {
  const out = wasm.kernel_decompress(job.g2, new Uint8Array(job.src, job.srcOff, job.len));
  new Uint8Array(job.dst, job.dstOff, out.length).set(out);
}

const KERNELS = { cols, rows, msm, decompress };

function handle(job) {
  const ctl = new Int32Array(job.ctl);
  try {
    KERNELS[job.kind](job);
  } catch (e) {
    console.error("xark pool worker:", e);
    Atomics.store(ctl, 1, 1);
  }
  Atomics.add(ctl, 0, 1);
  Atomics.notify(ctl, 0);
}

if (IS_NODE) {
  const { parentPort, workerData } = await import("node:worker_threads");
  const { createRequire } = await import("node:module");
  const require = createRequire(import.meta.url);
  wasm = require(workerData?.wasm || "../dist/node/xark_wasm.js");
  parentPort.on("message", handle);
  parentPort.postMessage("ready");
} else {
  self.onmessage = async (e) => {
    if (e.data?.init) {
      const mod = await import(e.data.wasm || new URL("../dist/web/xark_wasm.js", import.meta.url).href);
      await mod.default();
      wasm = mod;
      self.onmessage = (ev) => handle(ev.data);
      self.postMessage("ready");
    }
  };
}
