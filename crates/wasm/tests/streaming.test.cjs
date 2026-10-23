// xark-wasm streaming prover: `proveStreaming` single-threaded and with the
// worker pool (both paths), the no-SharedArrayBuffer fallback, and the
// wrong-key guard — against the sha256("abc") example (a 2^16 domain, so the
// blocked FFT and its worker passes run). Prerequisites:
//
//   xark build examples/sha256
//   xark setup examples/sha256 --insecure-dev-mode --deterministic-rng 7
//        # auto picks `minimized` for sha256 (−4.9%) and writes r1cs.stream
//   xark setup examples/sha256 --insecure-dev-mode --deterministic-rng 7 \
//        --r1cs-form reduced --out examples/sha256/target/xark/sha256-streamable
//   xark setup examples/sha256 --insecure-dev-mode --deterministic-rng 7 \
//        --out examples/sha256/target/xark/sha256-smooth   # default: smooth domain
//   wasm-pack build crates/wasm --target nodejs --release --out-dir dist/node
//   node --test crates/wasm/tests/streaming.test.cjs
//
// STREAM_CIRCUIT_DIR / STREAM_KEY_DIR override the artifact locations.
const test = require("node:test");
const assert = require("node:assert/strict");
const { join } = require("node:path");
const { readFileSync } = require("node:fs");
const { execFileSync } = require("node:child_process");

const xark = require("../dist/node/xark_wasm.js");
const poolMod = import("../js/pool.mjs");

const ROOT = join(__dirname, "..", "..", "..");
const C = process.env.STREAM_CIRCUIT_DIR || join(ROOT, "examples", "sha256", "target", "xark", "sha256");
const K = process.env.STREAM_KEY_DIR || join(ROOT, "examples", "sha256", "target", "xark", "sha256-streamable");
const xbc = new Uint8Array(readFileSync(join(C, "circuit.xbc")));
const pk = new Uint8Array(readFileSync(join(K, "pk.bin")));
const vk = new Uint8Array(readFileSync(join(K, "vk.bin")));
const INPUTS = {
  "msg[0]": "97", "msg[1]": "98", "msg[2]": "99",
  "digest.hi": "247859944228867399418143717509236138531",
  "digest.lo": "233961684503093977937504818427099878829",
};
const hex = (u8) => Buffer.from(u8).toString("hex");

const single = xark.proveStreaming(xbc, pk, INPUTS, { seed: 5 });

test("single-threaded proveStreaming verifies", () => {
  assert.equal(single.numPublicInputs, 2);
  assert.ok(xark.verify(vk, single.proof, single.publicInputs));
  assert.deepEqual(xark.decode_public_inputs(single.publicInputs), [INPUTS["digest.hi"], INPUTS["digest.lo"]]);
});

test("a tampered public input is rejected", () => {
  const bad = new Uint8Array(single.publicInputs);
  bad[8] ^= 1;
  assert.equal(xark.verify(vk, single.proof, bad), false);
});

test("worker pool: byte-identical proof, FFT + MSM offloaded", async () => {
  const { createPool, parallelSupported } = await poolMod;
  assert.ok(parallelSupported(), "Node has SharedArrayBuffer + Atomics");
  const pool = await createPool({ threads: 4 });
  try {
    const par = xark.proveStreaming(xbc, pk, INPUTS, { seed: 5, pool });
    assert.equal(hex(par.proof), hex(single.proof));
    assert.ok(pool.stats.fftCalls >= 4, `fft offloaded (${pool.stats.fftCalls})`);
    assert.ok(pool.stats.msmCalls >= 5, `msm offloaded (${pool.stats.msmCalls})`);
    // Different tile → same bytes (tiling is a schedule, not a semantics).
    const pool2 = await createPool({ threads: 3, tile: 5 });
    try {
      assert.equal(hex(xark.proveStreaming(xbc, pk, INPUTS, { seed: 5, pool: pool2 }).proof), hex(single.proof));
    } finally {
      await pool2.terminate();
    }
  } finally {
    await pool.terminate();
  }
});

test("without SharedArrayBuffer: parallel is unavailable and the fallback proves the same", () => {
  // A fresh process where SAB is absent (as on a non-cross-origin-isolated page).
  const script = `
    delete globalThis.SharedArrayBuffer;
    const xark = require(${JSON.stringify(join(__dirname, "..", "dist", "node", "xark_wasm.js"))});
    const fs = require("fs");
    const out = {};
    import(${JSON.stringify(join(__dirname, "..", "js", "pool.mjs"))}).then(({ createPool, parallelSupported }) => {
      out.supported = parallelSupported();
      return createPool();
    }).then(() => { out.created = true; }, () => { out.created = false; }).then(() => {
      const r = xark.proveStreaming(fs.readFileSync(${JSON.stringify(join(C, "circuit.xbc"))}),
        fs.readFileSync(${JSON.stringify(join(K, "pk.bin"))}), ${JSON.stringify(INPUTS)}, { seed: 5 });
      out.proof = Buffer.from(r.proof).toString("hex");
      console.log(JSON.stringify(out));
    });`;
  const out = JSON.parse(execFileSync(process.execPath, ["-e", script], { encoding: "utf8" }));
  assert.equal(out.supported, false);
  assert.equal(out.created, false);
  assert.equal(out.proof, hex(single.proof));
});

test("a minimized key proves with its r1cs.stream, and is refused without it", () => {
  const minimizedKey = new Uint8Array(readFileSync(join(C, "pk.bin")));
  const minimizedVk = new Uint8Array(readFileSync(join(C, "vk.bin")));
  const r1cs = new Uint8Array(readFileSync(join(C, "r1cs.stream")));
  assert.throws(() => xark.proveStreaming(xbc, minimizedKey, INPUTS, { seed: 5 }), /r1cs\.stream/);
  const out = xark.proveStreaming(xbc, minimizedKey, INPUTS, { seed: 5, r1cs });
  assert.ok(xark.verify(minimizedVk, out.proof, out.publicInputs));
  // A row file for another circuit is rejected by fingerprint.
  const other = new Uint8Array(r1cs);
  other[10] ^= 1;
  assert.throws(() => xark.proveStreaming(xbc, minimizedKey, INPUTS, { r1cs: other }));
});

test("proveFromStream: key fed through a ReadableStream, byte-identical", async () => {
  const { proveFromStream } = await import("../js/stream.mjs");
  // Odd, small chunks to exercise every buffering boundary.
  const stream = new ReadableStream({
    start(c) {
      for (let i = 0; i < pk.length; i += 4093) c.enqueue(pk.subarray(i, i + 4093));
      c.close();
    },
  });
  let progress = 0;
  const out = await proveFromStream(xark, xbc, stream, INPUTS, { seed: 5, onProgress: (n) => (progress = n) });
  assert.equal(hex(out.proof), hex(single.proof));
  assert.equal(progress, pk.length);
  // A Response works too (what fetch returns), and a truncated key is an error.
  const viaResponse = await proveFromStream(xark, xbc, new Response(pk), INPUTS, { seed: 5 });
  assert.equal(hex(viaResponse.proof), hex(single.proof));
  await assert.rejects(proveFromStream(xark, xbc, new Response(pk.subarray(0, pk.length - 9)), INPUTS), /ended early/);
});

test("preloadStreaming (streamed and resident key) proves the same bytes", () => {
  xark.preloadStreaming(xbc, pk, {});
  assert.equal(hex(xark.proveStreamingPreloaded(INPUTS, { seed: 5 }).proof), hex(single.proof));
  xark.preloadStreaming(xbc, pk, { residentKey: true });
  assert.equal(hex(xark.proveStreamingPreloaded(INPUTS, { seed: 5 }).proof), hex(single.proof));
});

test("spill: quotient vector parked in JS memory, same proof", () => {
  assert.equal(hex(xark.proveStreaming(xbc, pk, INPUTS, { seed: 5, spill: true }).proof), hex(single.proof));
});

test("transcodeKey: decoded key (with and without workers) proves the same bytes", async () => {
  const { transcodeKey } = await import("../js/stream.mjs");
  const { createPool } = await poolMod;
  const collect = async (s) => {
    const parts = [];
    for (const r = s.getReader(); ;) {
      const { done, value } = await r.read();
      if (done) break;
      parts.push(value);
    }
    return new Uint8Array(Buffer.concat(parts.map((p) => Buffer.from(p))));
  };
  const chunked = () => new ReadableStream({
    start(c) {
      for (let i = 0; i < pk.length; i += 7777) c.enqueue(pk.subarray(i, i + 7777));
      c.close();
    },
  });
  const local = await collect(transcodeKey(xark, chunked()));
  const pool = await createPool({ threads: 3 });
  let viaPool;
  try {
    viaPool = await collect(transcodeKey(xark, chunked(), { pool }));
  } finally {
    await pool.terminate();
  }
  assert.equal(Buffer.compare(Buffer.from(local), Buffer.from(viaPool)), 0);
  assert.ok(local.length > pk.length * 1.8, "uncompressed is ~2x");
  assert.equal(local[5], 1, "XKPK header marks it uncompressed");
  assert.equal(hex(xark.proveStreaming(xbc, local, INPUTS, { seed: 5 }).proof), hex(single.proof));
  await assert.rejects(collect(transcodeKey(xark, new Response(pk.subarray(0, pk.length - 3)))), /ended early/);
});

// A default (`--domain auto` → smooth) key: the domain is 9·2^12, not 2^16.
const S = process.env.SMOOTH_KEY_DIR || join(ROOT, "examples", "sha256", "target", "xark", "sha256-smooth");
const smooth = (() => {
  try {
    return {
      pk: new Uint8Array(readFileSync(join(S, "pk.bin"))),
      vk: new Uint8Array(readFileSync(join(S, "vk.bin"))),
      r1cs: new Uint8Array(readFileSync(join(S, "r1cs.stream"))),
    };
  } catch {
    return null;
  }
})();

test("smooth-domain key: legacy prove / preload and proveStreaming all verify", { skip: !smooth }, () => {
  const meta = JSON.parse(readFileSync(join(S, "metadata.json"), "utf8"));
  assert.equal(meta.qap_domain_size, 9 << 12);
  const legacy = xark.prove(xbc, smooth.pk, INPUTS);
  assert.ok(xark.verify(smooth.vk, legacy.proof, legacy.publicInputs));
  xark.preload(xbc, smooth.pk);
  const pre = xark.prove_preloaded(INPUTS);
  assert.ok(xark.verify(smooth.vk, pre.proof, pre.publicInputs));
  const st = xark.proveStreaming(xbc, smooth.pk, INPUTS, { r1cs: smooth.r1cs, seed: 5 });
  assert.ok(xark.verify(smooth.vk, st.proof, st.publicInputs));
  // Not valid under another key's vk.
  assert.equal(xark.verify(vk, st.proof, st.publicInputs), false);
});

test("legacy prove accepts a reduced-form key", () => {
  const legacy = xark.prove(xbc, pk, INPUTS);
  assert.ok(xark.verify(vk, legacy.proof, legacy.publicInputs));
});
