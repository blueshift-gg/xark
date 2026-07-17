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
import init, { prove, verify, circuit_inputs } from "@blueshift-gg/xark-wasm";

await init();

const [circuit, pk, vk] = await Promise.all([
  fetch("/circuit/circuit.xbc").then((r) => r.arrayBuffer()),
  fetch("/circuit/pk.bin").then((r) => r.arrayBuffer()),
  fetch("/circuit/vk.bin").then((r) => r.arrayBuffer()),
]);

console.log(circuit_inputs(circuit));
// → [{ name: "secret", role: "private" }, { name: "result", role: "public" }]

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

## API

### `prove(circuitXbc, pkBytes, inputs)`

Generates a Groth16 proof entirely in memory.

| argument     | type                          | description                                           |
|--------------|-------------------------------|-------------------------------------------------------|
| `circuitXbc` | `Uint8Array` \| `ArrayBuffer` | `circuit.xbc` (binary, self-contained build artifact) |
| `pkBytes`    | `Uint8Array` \| `ArrayBuffer` | Proving key (`pk.bin`, binary)                        |
| `inputs`     | `object`                      | Witness values as `{ name: "value" }`                 |

Returns a `ProveResult`:

| field             | type         |
|-------------------|--------------|
| `proof`           | `Uint8Array` |
| `publicInputs`    | `Uint8Array` |
| `numPublicInputs` | `number`     |

Input values are **decimal strings** (`"3"`, `"-7"`), keyed by the circuit's
declared input names. Throws on a malformed `.xbc`, unknown input, unsatisfiable
witness, or malformed key.

`proof` and `publicInputs` are the canonical compressed bytes (identical to the
host's `proof.bin` / `public_inputs.bin`) — pass them straight to `verify`. For
snarkjs interop, convert them on demand (see `proof_to_snarkjs` below).

> `prove` does **not** self-verify. Call `verify` on the result if you want
> that check.

### `preload(circuitXbc, pkBytes)`

Parse + cache the `.xbc` and proving key once (replaces prior cached state).

### `prove_preloaded(inputs)`

Like `prove` but reuses the artifacts cached by `preload`. Throws if `preload`
hasn't been called.

### `verify(vkBytes, proofBytes, publicInputsBytes)`

| argument            | type                          |
|---------------------|-------------------------------|
| `vkBytes`           | `Uint8Array` \| `ArrayBuffer` |
| `proofBytes`        | `Uint8Array` \| `ArrayBuffer` |
| `publicInputsBytes` | `Uint8Array` \| `ArrayBuffer` |

Returns `true` if valid, `false` if well-formed but not verifying. Throws on
deserialization errors.

### `proof_to_snarkjs(proofBytes)` → `object`

Converts the `proof` `Uint8Array` from `prove()` into the snarkjs proof object.

### `public_inputs_to_snarkjs(publicInputsBytes)` → `string[]`

Converts the `publicInputs` `Uint8Array` from `prove()` into the snarkjs
`public.json` array of decimal strings.

```js
const { proof, publicInputs } = prove(xbc, pk, { secret: "3", result: "27" });
const snarkjsProof  = proof_to_snarkjs(proof);
const snarkjsPublic = public_inputs_to_snarkjs(publicInputs);
```

### `circuit_inputs(circuitXbc)` → `object[]`

Returns `[{ name: "…", role: "public" | "private" }, …]` in declaration order.

### `version()` → `string`

Package version.

## Security

Prover randomness comes from the platform CSPRNG (`crypto.getRandomValues`).

## Build

```sh
cargo install wasm-pack
rustup target add wasm32-unknown-unknown
./build.sh                 # default target: bundler (webpack, vite, …)
./build.sh web             # or: nodejs | bundler | module
```

The `module` target (Cloudflare Workers / `workerd`) is built with
`wasm-bindgen` directly, since wasm-pack can't emit `--target module`. A
`release` build of the `module` target will **also rebuilds `dist/bundler/`**
and copies its optimized wasm (the raw wasm is byte-identical across targets —
only the JS glue differs).
