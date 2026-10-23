# xark-wasm

Generate and verify **Groth16 (BN254) zero knowledge proofs** in the browser
or other JavaScript environments with [xark](https://github.com/blueshift-gg/xark).

```js
import init, { prove, verify } from "@blueshift-gg/xark-wasm";

await init();

const [circuit, pk, vk] = await Promise.all([
  fetch("/circuit/circuit.xbc").then((r) => r.arrayBuffer()),
  fetch("/circuit/pk.bin").then((r) => r.arrayBuffer()),
  fetch("/circuit/vk.bin").then((r) => r.arrayBuffer()),
]);

const { proof, publicInputs } = prove(circuit, pk, { secret: "3", result: "27" });
verify(vk, proof, publicInputs); // true
```

Runs anywhere with Web Crypto: **browsers**, **Node 20+**, **Cloudflare Workers**,
**Vercel Edge**, **Deno**. The circuit, proving/verifying keys, proof, and public
inputs are all **binary** — only the witness inputs (a tiny `name → value` map)
cross the boundary as a plain object. Every binary argument accepts a
`Uint8Array` **or** an `ArrayBuffer`, so the result of `response.arrayBuffer()`
(or a Node `Buffer`) can be passed straight in — no `new Uint8Array(...)` wrap.

## Producing circuit artifacts

Before proving, you need the circuit bytecode and proving/verifying keys.
Produce them with the `xark` CLI:

```sh
xark build    # → target/xark/<name>/circuit.xbc   (binary, self-contained)
xark setup    # → target/xark/<name>/{pk.bin, vk.bin}
```

`circuit.xbc` is the single self-contained build artifact: it encodes both the
solver view (witness generation) and the backend view (the minimized R1CS the
proving key is keyed to)

## Usage

### Browser

```js
import init, { prove, verify } from "@blueshift-gg/xark-wasm";

await init();

const [circuit, pk, vk] = await Promise.all([
  fetch("/circuit/circuit.xbc").then((r) => r.arrayBuffer()),
  fetch("/circuit/pk.bin").then((r) => r.arrayBuffer()),
  fetch("/circuit/vk.bin").then((r) => r.arrayBuffer()),
]);

const { proof, publicInputs } = prove(circuit, pk, { secret: "3", result: "27" });

console.log(verify(vk, proof, publicInputs)); // true
```

### Node.js

The Node build does not require a separate `init()` step.

```js
import { readFileSync } from "node:fs";
import { prove, verify } from "@blueshift-gg/xark-wasm";

// `readFileSync` returns a Buffer, which is a Uint8Array — pass it straight in.
const xbc = readFileSync("examples/cube/target/xark/cube/circuit.xbc");
const pk  = readFileSync("examples/cube/target/xark/cube/pk.bin");
const vk  = readFileSync("examples/cube/target/xark/cube/vk.bin");

const { proof, publicInputs } = prove(xbc, pk, { secret: "3", result: "27" });

console.log(verify(vk, proof, publicInputs)); // true
```

### Performance optimization (preloading)

`prove` re-expands the `.xbc` and re-minimizes the R1CS on every call. For
repeated proofs against the same circuit + key, parse them once with `preload`
and call `prove_preloaded`:

```js
preload(circuit, pk);
const a = prove_preloaded({ secret: "3", result: "27" });
const b = prove_preloaded({ secret: "2", result: "8" });
```

### Large circuits: the streaming prover

Every API proves with the streaming prover: rows are evaluated window by window,
the witness is solved by streaming the hint program, and the proving key is read
one chunk of points at a time, so neither the constraint system nor the decoded
key is ever held whole (Ed25519 verification proves in about 0.5–0.9 GB). Its
proofs are byte-identical to the host prover's for the same randomness. `prove`
needs the whole key as bytes; the APIs below add streaming the key itself as it
downloads, worker threads, and resident keys.

**Which key.** `xark setup` records the key's R1CS form in `metadata.json`
(`r1cs_form`):

* `reduced` — rows stream from `circuit.xbc` alone. Pass nothing extra.
* `minimized` — setup also wrote `r1cs.stream`; pass it as `options.r1cs`.

By default setup picks `reduced` for large circuits (≥ 2²⁰ constraints) and
`minimized` only where the global minimize pass actually helps (sha256: −4.9%);
`--r1cs-form` overrides. A key/circuit mismatch is an error, never a bad proof.

**Stream the key while it downloads** — no SharedArrayBuffer needed, works on the
main thread, and the key is never buffered anywhere:

```js
import * as xark from "@blueshift-gg/xark-wasm";
import { proveFromStream } from "@blueshift-gg/xark-wasm/stream";

const { proof, publicInputs } = await proveFromStream(
  xark, circuit, fetch("/circuit/pk.bin"), inputs,
  { r1cs, onProgress: (bytes) => bar.update(bytes) },   // r1cs only for a `minimized` key
);
```

The witness and quotient polynomial are computed before the first key byte is
needed, so proving overlaps the download. (`beginStreamingProof` → `push(chunk)` →
`finish()` is the underlying API.)

**Decode the key once per device.** A compressed key (the default) costs a field
square root per point every time it is read — ~95% of the witness MSMs in WASM.
`transcodeKey` re-encodes it with uncompressed points (2× the size); store the
result and prove from it on later visits (Ed25519 with 16 workers: 3.5× faster):

```js
import { transcodeKey } from "@blueshift-gg/xark-wasm/stream";

const root = await navigator.storage.getDirectory();
const file = await root.getFileHandle("pk.decoded.bin", { create: true });
await transcodeKey(xark, fetch("/circuit/pk.bin"), { pool }).pipeTo(await file.createWritable());
// later:
const out = await proveFromStream(xark, circuit, (await file.getFile()).stream(), inputs, { pool });
```

**Key already in memory:**

```js
proveStreaming(circuit, pk, inputs, { r1cs });            // one-off

preloadStreaming(circuit, pk, { r1cs, residentKey: true }); // many proofs
proveStreamingPreloaded(inputs);
```

`residentKey` decodes the key once (≈2.2× its compressed size in wasm memory) so
repeat proofs skip point decompression — zkyc proves in the same time as
`prove_preloaded`; sha256 3.6× faster than streamed. Leave it off with a worker
pool, whose workers decompress their chunks in parallel.

**Threads (optional).**

```js
const { createPool, parallelSupported } = await import("@blueshift-gg/xark-wasm/pool");
const pool = parallelSupported() ? await createPool({ threads: 8 }) : undefined;
proveStreaming(circuit, pk, inputs, { pool });   // also accepted by proveFromStream
await pool?.terminate();
```

The blocked FFT's sweeps and every MSM chunk run across workers (each its own wasm
instance) via a `SharedArrayBuffer`. That needs a cross-origin-isolated page
(`Cross-Origin-Opener-Policy: same-origin`, `Cross-Origin-Embedder-Policy:
require-corp`), and the proving call must run in a Web Worker (it blocks with
`Atomics.wait`). Without isolation `parallelSupported()` is false and the same
prover runs single-threaded with the same memory profile.

**Smooth-domain keys** (`xark setup`'s default for dev keys: a QAP domain up to
44% smaller) prove through every API. The key's header states its domain, so `proveFromStream` computes
`h` as soon as the first bytes arrive, overlapping the rest of the download.

**Near the 4 GB limit:** `{ spill: true }` keeps one quotient vector in wasm memory
and parks the other in a JS buffer.

## API

### `prove(circuitXbc, pkBytes, inputs, sources?)`

Generates a Groth16 proof, streaming the constraint rows and reading the key a
chunk at a time. For a `minimized` key it rebuilds that circuit from `circuitXbc`
itself, so no `r1cs.stream` is needed.

| argument     | type                          | description                                           |
|--------------|-------------------------------|-------------------------------------------------------|
| `circuitXbc` | `Uint8Array` \| `ArrayBuffer` | `circuit.xbc` (binary, self-contained build artifact) |
| `pkBytes`    | `Uint8Array` \| `ArrayBuffer` | Proving key (`pk.bin`, binary)                        |
| `inputs`     | `object`                      | Witness values; see [Inputs](#inputs)                 |
| `sources`    | `string` (optional)           | `sources.json` (text) from the same build             |

Returns a `ProofBundle`:

| field             | type         |
|-------------------|--------------|
| `proof`           | `Uint8Array` |
| `publicInputs`    | `Uint8Array` |
| `numPublicInputs` | `number`     |

Throws on a malformed `.xbc`, unknown input, unsatisfiable witness, or malformed key.
Inputs that fail a check are reported as the statement that fails when `sources`
is given (`xark build` writes `sources.json` beside `circuit.xbc`):

```text
the inputs fail the check at src/lib.rs:77:20: `id.nationality.require_one_of(allowed);`
```

and as the failing constraint's number otherwise. `preload(circuitXbc, pkBytes,
sources?)` and the streaming API's `options.sources` take it the same way.

#### Inputs

`inputs` gives every input leaf a field element: keys are the circuit's input names,
and values nest to mirror the input's shape:

```js
prove(xbc, pk, {
  id: { dob: 19940312, net_worth: 2400000n, tag: new Uint8Array([1, 2]) }, // field names as in Rust
  path: ["12", "0x0d"],                // an array: element i → path[i]
  ok: true,                            // booleans are 1 / 0
});
```

For values in their natural forms (a date, a country, a hash's 32 bytes, a key),
encode them first with the circuit's `schema.json`, exactly as `xark prove --inputs`
reads them: `prove(xbc, pk, encodeInputs(schema, JSON.stringify(inputs)))`. A
generated client (`xark client`) does this for you.

Scalars may be decimal strings, `0x`-hex strings, safe-integer numbers, or bigints.
A field value must already be a field element (`0 <= x < p`): a negative or larger
value is rejected rather than reduced, since it would prove a different number. A
number outside JavaScript's safe-integer range is rejected rather than rounded; pass
it as a bigint or a string. Flat leaf names (`"id.dob"`, `"path[0]"`)
still work and can be mixed with nested values.

`proof` and `publicInputs` are the canonical compressed bytes (identical to the
host's `proof.bin` / `public_inputs.bin`) — pass them straight to `verify`. To
read the public inputs, see `decode_public_inputs` below.

> `prove` checks the proof against the key's verifying key before returning it;
> an unsatisfiable witness is reported as an error, never returned as a proof.

### `preload(circuitXbc, pkBytes)`

Parse + cache the `.xbc` and proving key once (replaces prior cached state). The key
is decoded into wasm memory (about 2.2× its compressed size) so repeat proofs skip
point decompression; for the largest circuits use `preloadStreaming`.

### `prove_preloaded(inputs)`

Like `prove` but reuses the artifacts cached by `preload`. Throws if `preload`
hasn't been called.

### `new ProvingSession(circuitXbc, pkBytes, sources?)`

What `preload` caches, as an object of its own: `session.prove(inputs)` proves as
`prove` does, without parsing the circuit or decoding the key again. Each holds its
own circuit, so several can be loaded at once. A typed client's `prover.preload()`
makes one.

### `verify(vkBytes, proofBytes, publicInputsBytes)`

| argument            | type                          |
|---------------------|-------------------------------|
| `vkBytes`           | `Uint8Array` \| `ArrayBuffer` |
| `proofBytes`        | `Uint8Array` \| `ArrayBuffer` |
| `publicInputsBytes` | `Uint8Array` \| `ArrayBuffer` |

`proofBytes` is either form: compressed (128 bytes, as `prove` returns it) or
on-chain (256 bytes, as an exported Solana verifier reads it; `solanaProof(proof)`
converts). Returns `true` if valid, `false` if well-formed but not verifying.
Throws on deserialization errors.

### `decode_public_inputs(publicInputsBytes)` → `string[]`

Decodes the `publicInputs` bytes from `prove()` (or a `public_inputs.bin`) into
decimal strings, in proof order.

```js
const { publicInputs } = prove(xbc, pk, { secret: "3", result: "27" });
decode_public_inputs(publicInputs); // ["27"]
```

### `solanaProof(proofBytes)` → `Uint8Array`

A proof in either form as an exported Solana verifier (`xark export`) reads it:
256 bytes, little-endian, `-A || B || C`. What a client's `proof.toBytes()` returns.

### `sha256Hex(bytes)` → `string`

Lowercase hex SHA-256: a `vk.bin`'s is what `xark setup` prints, and what a client
pins a verifier to with `verifier(from, { keyHash })`. Works where WebCrypto
doesn't (a page served over plain HTTP).

### `circuitDigest(circuitXbc)` → `string`

The circuit digest of a `circuit.xbc`, as `xark build` prints it: the same for every
build of the circuit, whichever Rust compiled it. A client pins a prover to it with
`prover(from, { digest })`.

### Typed clients (`@blueshift-gg/xark-wasm/client`)

What every client `xark client` generates shares, as plain JavaScript with types:
`Field` (a field element, checked when it's made), `Proof` (a proof and its public
inputs; `toBytes()` is the proof as an exported Solana verifier reads it,
`toBytesCompressed()` half the size), and `Circuit`, which a generated file
instantiates with its circuit's schema to make a `Prover` or a `Verifier` from a
URL serving the build output or from its bytes. It loads this package's main
module for the platform itself (running `init()` for the web build) the first time
one is made; `{ wasm }` in the options passes your own. A circuit fetches
`client.wasm` once, however many provers and verifiers are made from its URL, and
`prover.preload()` keeps the proving key decoded so each proof skips decoding it
(faster repeat proofs, for about 2.2× `pk.bin` in memory).

```js
import { Zkyc } from "./zkyc"; // generated; imports this module
const prover = await Zkyc.prover("/circuits/zkyc/");
const proof = prover.prove(inputs);
const verifier = await Zkyc.verifier(vkBytes);
verifier.verify(proof.toBytes(), requiredPublicInputs); // true
prover.poseidon2(prover.fields("Identity", id)); // hash a value as the circuit does
```

### Typed values (`schema.json`)

These take the circuit's `schema.json` text, so values go in and come out in
their natural forms (dates, strings, variant names, bytes). Each also exists as a
method of `new Schema(text)`, which parses the schema once; a generated client
(`xark client`) holds one. Likewise `new VerifyingKey(vkBytes)` decodes `vk.bin`
once (throwing if it's malformed), and its `verify(proof, publicInputs)` decodes
only the proof.

- `encodeInputs(schema, inputs)`: every input (JSON text) → the `leaf → decimal`
  object `prove` takes.
- `encodePublicInputs(schema, publicInputs)`: the public ones → the bytes `verify`
  takes.
- `decodePublicValues(schema, bytes)`: those bytes → JSON text of the natural
  values.
- `valueFields(schema, typeName, value)`: a value of one of the circuit's input
  types → its field elements (decimal strings) in input order, what `to_fields()`
  gives in Rust.

### `poseidon2(inputs)` → `string`

`xark_poseidon2::hash` of field elements (decimal or `0x`-hex strings), as a
decimal string. With `valueFields`, a client computes a commitment the way the
circuit does:

```js
const fields = valueFields(schema, "Identity", JSON.stringify(id));
poseidon2(fields); // == the circuit's `xark_poseidon2::hash(id.to_fields())`
```

## Security

Prover randomness comes from the platform CSPRNG (`crypto.getRandomValues`).

## Build

From the repository root:

```sh
cargo install wasm-pack
rustup target add wasm32-unknown-unknown
cargo xtask wasm           # default target: bundler (webpack, vite, …)
cargo xtask wasm web       # or: nodejs | bundler | module | all; --dev for a debug build
```

The `module` target (Cloudflare Workers / `workerd`) is built with
`wasm-bindgen` directly, since wasm-pack can't emit `--target module`; the
`wasm-bindgen` CLI is installed at the version `Cargo.lock` pins. A
release build of the `module` target will **also rebuild `dist/bundler/`**
and copies its optimized wasm (the raw wasm is byte-identical across targets —
only the JS glue differs).
