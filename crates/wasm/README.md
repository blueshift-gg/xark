# xark-wasm

Generate and verify **Groth16 (BN254) proofs in the browser or Node.js**.

```js
import init, { prove, verify } from "@blueshift-gg/xark-wasm";
await init();

const xbc = new Uint8Array(await (await fetch("/circuit/circuit.xbc")).arrayBuffer());
const pk  = new Uint8Array(await (await fetch("/circuit/pk.bin")).arrayBuffer());

const { proof, publicInputs } = prove(xbc, pk, JSON.stringify({ secret: "3", result: "27" }));
verify(vkBytes, proof, publicInputs); // true
```

Runs anywhere with Web Crypto: **browsers**, **Node 20+**, **Cloudflare Workers**,
**Vercel Edge**, **Deno**. The circuit, proving/verifying keys, proof, and public
inputs are all **binary** — only the witness inputs (a tiny `name → value` map)
are JSON.

## Producing circuit artifacts

Before proving, you need the circuit bytecode and proving/verifying keys. Produce
them once with the `xark` CLI and ship to your client:

```sh
xark build  my_circuit    # → my_circuit/target/xark/<name>/circuit.xbc   (binary, self-contained)
xark setup  my_circuit    # → my_circuit/target/xark/<name>/{pk.bin, vk.bin}
```

`circuit.xbc` is the single self-contained build artifact: it encodes both the
solver view (witness generation) and the backend view (the minimized R1CS the
proving key is keyed to). No JSON circuit files are required. (`xark build
--emit-json` still writes `circuit.json`/`r1cs.json` for debugging, but the wasm
bindings consume the binary.)

## Usage

### Browser

```js
import init, { prove, verify, circuit_inputs } from "@blueshift-gg/xark-wasm";
await init();

const [xbc, pk, vk] = await Promise.all([
  fetch("/circuit/circuit.xbc").then(r => r.arrayBuffer()).then(b => new Uint8Array(b)),
  fetch("/circuit/pk.bin").then(r => r.arrayBuffer()).then(b => new Uint8Array(b)),
  fetch("/circuit/vk.bin").then(r => r.arrayBuffer()).then(b => new Uint8Array(b)),
]);

console.log(circuit_inputs(xbc));
// → [{"name":"secret","role":"private"}, {"name":"result","role":"public"}]

const { proof, publicInputs } = prove(
  xbc, pk,
  JSON.stringify({ secret: "3", result: "27" })
);

console.log(verify(vk, proof, publicInputs)); // true
```

### Proving many times (preload)

`prove` re-expands the `.xbc` and re-minimizes the R1CS on every call. For
repeated proofs against the same circuit + key, parse them once with `preload`
and call `prove_preloaded`:

```js
preload(xbc, pk);                                        // once
const a = prove_preloaded(JSON.stringify({ secret: "3", result: "27" }));
const b = prove_preloaded(JSON.stringify({ secret: "2", result: "8" }));
```

### Node.js

```js
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import init, { prove, verify } from "@blueshift-gg/xark-wasm";

// Node.js: pass the wasm bytes explicitly (fetch can't read file:// URLs).
const wasmPath = fileURLToPath(new URL("../node_modules/@blueshift-gg/xark-wasm/xark_wasm_bg.wasm", import.meta.url));
const wasmBytes = readFileSync(wasmPath);
await init({ module_or_path: wasmBytes });

const xbc = new Uint8Array(readFileSync("../../examples/cube/target/xark/cube/circuit.xbc"));
const pk  = new Uint8Array(readFileSync("../../examples/cube/target/xark/cube/pk.bin"));
const vk  = new Uint8Array(readFileSync("../../examples/cube/target/xark/cube/vk.bin"));

const { proof, publicInputs } = prove(xbc, pk,
  JSON.stringify({ secret: "3", result: "27" }));

console.log(verify(vk, proof, publicInputs)); // true
```

On Edge runtimes (Workers, Deno), import the `.wasm` via a `CompiledWasm` rule
or pass a `WebAssembly.Module` to `init({ module_or_path })`.

## API

### `prove(circuitXbc, pkBytes, inputsJson)`

Generates a Groth16 proof entirely in memory.

| argument      | type         | description                                       |
|---------------|--------------|---------------------------------------------------|
| `circuitXbc`  | `Uint8Array` | `circuit.xbc` (binary, self-contained build artifact) |
| `pkBytes`     | `Uint8Array` | Proving key (`pk.bin`, binary)                    |
| `inputsJson`  | `string`     | Witness values as `{"name":"value"}`              |

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
snarkjs interop, convert them on demand (see `proof_to_snarkjs_json` below).

> `prove` does **not** self-verify (matching snarkjs / arkworks / gnark, where
> proving and verifying are separate steps). Call `verify` on the result if you
> want that check.

### `preload(circuitXbc, pkBytes)`

Parse + cache the `.xbc` and proving key once (replaces prior cached state).

### `prove_preloaded(inputsJson)`

Like `prove` but reuses the artifacts cached by `preload`. Throws if `preload`
hasn't been called.

### `verify(vkBytes, proofBytes, publicInputsBytes)`

| argument            | type         |
|---------------------|--------------|
| `vkBytes`           | `Uint8Array` |
| `proofBytes`        | `Uint8Array` |
| `publicInputsBytes` | `Uint8Array` |

Returns `true` if valid, `false` if well-formed but not verifying. Throws on
deserialization errors.

### `proof_to_snarkjs_json(proofBytes)` → `string`

Converts the `proof` `Uint8Array` from `prove` into snarkjs-compatible JSON (the
same shape as the host's `snarkjs-proof.json`). Opt-in: `prove` returns only the
canonical bytes, so you derive the snarkjs view only when you need it.

### `public_inputs_to_snarkjs_json(publicInputsBytes)` → `string`

Converts the `publicInputs` `Uint8Array` from `prove` into the snarkjs `public.json`
array of decimal strings.

```js
const { proof, publicInputs } = prove(xbc, pk, inputsJson);
const snarkjsProof  = JSON.parse(proof_to_snarkjs_json(proof));
const snarkjsPublic = JSON.parse(public_inputs_to_snarkjs_json(publicInputs));
```

### `circuit_inputs(circuitXbc)` → `string`

Returns `[{"name":"…","role":"public"|"private"}, …]` in declaration order.

### `version()` → `string`

Package version.

## How the circuit is consumed

A single `circuit.xbc` is sufficient because it encodes both views the prover
needs — mirroring `xark prove`:

* **`expand_function_blob_reduced`** → the **minimized R1CS** the proving key was
  generated against (`xark setup` keys the pk to exactly this circuit). Using any
  other R1CS would make the proof fail to verify.
* **`expand_function_blob`** (full) → the circuit **with its witness-generation
  program**, used to solve the witness. (The reduced variant deliberately leaves
  witness generation empty.)

## Security

Prover randomness comes from the platform CSPRNG (`crypto.getRandomValues`).
No deterministic-RNG option: reproducible prover randomness breaks
zero-knowledge.

## Build

```sh
cargo install wasm-pack
rustup target add wasm32-unknown-unknown
./build.sh                 # default target: bundler (webpack, vite, …)
./build.sh web             # or: nodejs | bundler | module
```

The `module` target (Cloudflare Workers / `workerd`) is built with
`wasm-bindgen` directly, since wasm-pack can't emit `--target module`. To reuse
wasm-pack's `wasm-opt` pass without a separate `wasm-opt` install, a release
`module` build **also rebuilds `dist/bundler/`** and copies its optimized wasm
(the raw wasm is byte-identical across targets — only the JS glue differs). So
don't be surprised if `./build.sh module` refreshes `dist/bundler/` too.
