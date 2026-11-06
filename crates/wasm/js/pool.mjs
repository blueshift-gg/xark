// Parallel proving for xark-wasm: a worker pool that runs the streaming prover's
// FFT sweeps and MSM chunks across threads — in browsers (Web Workers) and Node
// (worker_threads), from one implementation.
//
//   import { createPool, parallelSupported } from "@blueshift-gg/xark-wasm/pool";
//   const pool = parallelSupported() ? await createPool({ threads: 8 }) : undefined;
//   const out = proveStreaming(xbc, pk, inputs, { pool });   // pool is optional
//   await pool?.terminate();
//
// How it works. The prover stays one synchronous wasm call. At each data-parallel
// step it calls back into the pool (toCoset / fromCosetToT / msm) with a view of
// its own memory; the pool copies the data into a SharedArrayBuffer, posts one job
// per worker, and blocks on Atomics.wait until every worker has bumped the shared
// completion counter (a barrier). The four-step FFT is exactly three barriers:
// column tiles → (fused) row blocks → column tiles. Each worker owns a separate
// wasm instance and runs the same Rust kernels the native prover uses.
//
// Requirements — the single switch that unlocks threading:
//   * SharedArrayBuffer: in browsers only on a cross-origin-isolated page, i.e.
//     served with `Cross-Origin-Opener-Policy: same-origin` and
//     `Cross-Origin-Embedder-Policy: require-corp` (same posture as snarkjs).
//   * Atomics.wait on the proving thread: fine in Node and in Web Workers, not on
//     a browser's main thread — so call proveStreaming from a worker.
// Without them parallelSupported() is false: prove without a pool. The
// single-threaded streaming prover keeps the full memory win.

const IS_NODE = typeof process !== "undefined" && !!process.versions?.node;

/** Whether worker-parallel proving can run here (see header). */
export function parallelSupported() {
  if (typeof SharedArrayBuffer !== "function" || typeof Atomics !== "object") return false;
  // Browsers: false means the page isn't cross-origin isolated (no COOP/COEP).
  if (globalThis.crossOriginIsolated === false) return false;
  return true;
}

const COUNT = 0; // completed jobs
const FAILED = 1; // any job failed

export class WorkerPool {
  constructor(workers, opts = {}) {
    this.workers = workers;
    this.tile = opts.tile || 4;
    this.ctl = new Int32Array(new SharedArrayBuffer(8));
    this.bufs = {};
    this.stats = { fftCalls: 0, msmCalls: 0, fftMs: 0, msmMs: 0 };
  }

  get threads() {
    return this.workers.length;
  }

  /** A shared scratch buffer of at least `bytes`, reused across calls. */
  _sab(name, bytes) {
    const cur = this.bufs[name];
    if (!cur || cur.byteLength < bytes) this.bufs[name] = new SharedArrayBuffer(bytes);
    return this.bufs[name];
  }

  /** Post the jobs and block until all have finished (barrier). */
  _run(jobs) {
    const ctl = this.ctl;
    Atomics.store(ctl, COUNT, 0);
    Atomics.store(ctl, FAILED, 0);
    jobs.forEach((job, i) => this.workers[i % this.workers.length].postMessage({ ...job, ctl: ctl.buffer }));
    for (;;) {
      const done = Atomics.load(ctl, COUNT);
      if (done >= jobs.length) break;
      Atomics.wait(ctl, COUNT, done);
    }
    if (Atomics.load(ctl, FAILED)) throw new Error("xark worker kernel failed (see worker console)");
  }

  /** Split [0, n) into ≤ `threads` contiguous ranges, each a multiple of `align`. */
  _ranges(n, align) {
    const units = Math.ceil(n / align);
    const per = Math.ceil(units / this.workers.length);
    const out = [];
    for (let u = 0; u < units; u += per) out.push([u * align, Math.min(n, (u + per) * align)]);
    return out;
  }

  // The buffer is an n1 × n2 matrix (the coordinator's four-step split).
  _cols(sab, n1, n2, op) {
    this._run(this._ranges(n2, this.tile).map(([c0, c1]) => ({
      kind: "cols", data: sab, n1, n2, c0, c1, tile: this.tile, op,
    })));
  }

  _rows(sab, n1, n2, toCoset) {
    this._run(this._ranges(n1, 1).map(([r0, r1]) => ({ kind: "rows", data: sab, n1, n2, r0, r1, toCoset })));
  }

  _fft(buf, passes) {
    const t = Date.now();
    const sab = this._sab("fft", buf.length);
    const shared = new Uint8Array(sab, 0, buf.length);
    shared.set(buf);
    for (const p of passes) p(sab);
    buf.set(shared);
    this.stats.fftCalls++;
    this.stats.fftMs += Date.now() - t;
    return true;
  }

  /** evaluations → coset evaluations, in place (called from wasm). */
  toCoset(n1, n2, buf) {
    return this._fft(buf, [
      (s) => this._cols(s, n1, n2, 0),
      (s) => this._rows(s, n1, n2, true),
      (s) => this._cols(s, n1, n2, 1),
    ]);
  }

  /** coset evaluations → T-layout coefficients, in place (called from wasm). */
  fromCosetToT(n1, n2, buf) {
    return this._fft(buf, [(s) => this._cols(s, n1, n2, 0), (s) => this._rows(s, n1, n2, false)]);
  }

  /** Re-encode compressed points uncompressed, split across workers (called from wasm). */
  decompress(g2, points) {
    const csz = g2 ? 64 : 32;
    const usz = 2 * csz;
    const n = points.length / csz;
    const src = this._sab("dsrc", points.length);
    new Uint8Array(src, 0, points.length).set(points);
    const dst = this._sab("ddst", n * usz);
    this._run(this._ranges(n, 1).map(([i0, i1]) => ({
      kind: "decompress", g2, src, dst, srcOff: i0 * csz, len: (i1 - i0) * csz, dstOff: i0 * usz,
    })));
    return new Uint8Array(dst, 0, n * usz).slice();
  }

  /** Σ sᵢ·Pᵢ over serialized points; returns the workers' partial sums concatenated. */
  msm(g2, points, compressed, scalars) {
    const t = Date.now();
    const n = scalars.length / 32;
    const psz = points.length / n;
    const pts = this._sab("pts", points.length);
    new Uint8Array(pts, 0, points.length).set(points);
    const sc = this._sab("sc", scalars.length);
    new Uint8Array(sc, 0, scalars.length).set(scalars);
    const outSz = g2 ? 128 : 64; // uncompressed affine
    const ranges = this._ranges(n, 1);
    const out = this._sab("out", ranges.length * outSz);
    this._run(ranges.map(([i0, i1], k) => ({
      kind: "msm", g2, compressed, pts, sc, out,
      ptsOff: i0 * psz, ptsLen: (i1 - i0) * psz,
      scOff: i0 * 32, scLen: (i1 - i0) * 32,
      outOff: k * outSz,
    })));
    this.stats.msmCalls++;
    this.stats.msmMs += Date.now() - t;
    return new Uint8Array(out, 0, ranges.length * outSz).slice();
  }

  async terminate() {
    await Promise.all(this.workers.map((w) => w.terminate()));
  }
}

function defaultThreads() {
  if (globalThis.navigator?.hardwareConcurrency) return navigator.hardwareConcurrency;
  return 4;
}

/**
 * Start `threads` workers (default: hardware concurrency), each instantiating its
 * own copy of the wasm module, and resolve once all are ready. Options: `threads`,
 * `tile` (FFT column-block width), `wasm` (Node: path to the nodejs-target glue;
 * browser: URL of the web-target glue module).
 */
export async function createPool(opts = {}) {
  if (!parallelSupported()) throw new Error("SharedArrayBuffer/Atomics unavailable: prove without a pool");
  const workerUrl = new URL("./pool-worker.mjs", import.meta.url);
  let spawn;
  let threads = opts.threads;
  if (IS_NODE) {
    const { Worker } = await import("node:worker_threads");
    const os = await import("node:os");
    threads ||= os.availableParallelism ? os.availableParallelism() : os.cpus().length;
    spawn = () => {
      const w = new Worker(workerUrl, { workerData: { wasm: opts.wasm } });
      return new Promise((resolve, reject) => {
        w.once("message", (m) => (m === "ready" ? resolve(w) : reject(new Error(String(m)))));
        w.once("error", reject);
      });
    };
  } else {
    threads ||= defaultThreads();
    spawn = () => {
      const w = new Worker(workerUrl, { type: "module" });
      return new Promise((resolve, reject) => {
        w.onmessage = (e) => {
          w.onmessage = null;
          e.data === "ready" ? resolve(w) : reject(new Error(String(e.data)));
        };
        w.onerror = (e) => reject(new Error(e.message));
        w.postMessage({ init: true, wasm: opts.wasm });
      });
    };
  }
  const workers = await Promise.all(Array.from({ length: threads }, spawn));
  return new WorkerPool(workers, opts);
}
