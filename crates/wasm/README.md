# xark-wasm

Generate and verify **Groth16 (BN254) proofs in the browser or Node.js**.

```js
import init, { prove, verify } from "@blueshift-gg/xark-wasm";
await init();

const { proof, publicInputs } = prove(r1csJson, circuitJson, pkBytes, inputsJson);
verify(vkBytes, proof, publicInputs); // true
```

Runs anywhere with Web Crypto: **browsers**, **Node 20+**, **Cloudflare Workers**,
**Vercel Edge**, **Deno**.

## Producing circuit artifacts

Before proving, you need R1CS, circuit definition, and proving/verifying keys.
Produce them once with the `xark` CLI and ship to your client:

```sh
xark build  my_circuit    # → my_circuit/target/xark/{circuit}/{r1cs,circuit}.json
xark setup  my_circuit    # → my_circuit/target/xark/{circuit}/pk.bin, vk.bin
```

## Usage

### Browser

```js
import init, { prove, verify, circuit_inputs } from "@blueshift-gg/xark-wasm";
await init();

const [r1cs, circuit, pk, vk] = await Promise.all([
  fetch("/circuit/r1cs.json").then(r => r.text()),
  fetch("/circuit/circuit.json").then(r => r.text()),
  fetch("/circuit/pk.bin").then(r => r.arrayBuffer()).then(b => new Uint8Array(b)),
  fetch("/circuit/vk.bin").then(r => r.arrayBuffer()).then(b => new Uint8Array(b)),
]);

console.log(circuit_inputs(circuit));
// → [{"name":"secret","role":"private"}, {"name":"result","role":"public"}]

const { proof, publicInputs } = prove(
  r1cs, circuit, pk,
  JSON.stringify({ secret: "3", result: "27" })
);

console.log(verify(vk, proof, publicInputs)); // true
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

const r1cs    = readFileSync("../../examples/cube/target/xark/cube/r1cs.json", "utf8");
const circuit = readFileSync("../../examples/cube/target/xark/cube/circuit.json", "utf8");
const pk      = new Uint8Array(readFileSync("../../examples/cube/target/xark/cube/pk.bin"));
const vk      = new Uint8Array(readFileSync("../../examples/cube/target/xark/cube/vk.bin"));

const { proof, publicInputs } = prove(r1cs, circuit, pk,
  JSON.stringify({ secret: "3", result: "27" }));

console.log(verify(vk, proof, publicInputs)); // true
```

On Edge runtimes (Workers, Deno), import the `.wasm` via a `CompiledWasm` rule
or pass a `WebAssembly.Module` to `init({ module_or_path })`.

## API

### `prove(r1csJson, circuitJson, pkBytes, inputsJson)`

Generates a Groth16 proof entirely in memory, self-verified before returning.

| argument      | type         | description                          |
|---------------|--------------|--------------------------------------|
| `r1csJson`    | `string`     | R1CS constraints (JSON)              |
| `circuitJson` | `string`     | Circuit definition (JSON)            |
| `pkBytes`     | `Uint8Array` | Proving key (binary)                 |
| `inputsJson`  | `string`     | Witness values as `{"name":"value"}` |

Returns:

| field             | type         |
|-------------------|--------------|
| `proof`           | `Uint8Array` |
| `publicInputs`    | `Uint8Array` |
| `snarkjsProof`    | `string`     |
| `snarkjsPublic`   | `string`     |
| `numPublicInputs` | `number`     |

Input values are **decimal strings** (`"3"`, `"-7"`), keyed by the circuit's
declared input names. Throws on bad JSON, unknown input, unsatisfiable witness,
malformed key, or failed self-verification.

### `verify(vkBytes, proofBytes, publicInputsBytes)`

| argument            | type         |
|---------------------|--------------|
| `vkBytes`           | `Uint8Array` |
| `proofBytes`        | `Uint8Array` |
| `publicInputsBytes` | `Uint8Array` |

Returns `true` if valid, `false` if well-formed but not verifying. Throws on
deserialization errors.

### `circuit_inputs(circuitJson)` → `string`

Returns `[{"name":"…","role":"public"|"private"}, …]` in declaration order.

### `version()` → `string`

Package version.

## Security

Prover randomness comes from the platform CSPRNG (`crypto.getRandomValues`).
No deterministic-RNG option: reproducible prover randomness breaks
zero-knowledge.

## Build

```sh
cargo install wasm-pack
rustup target add wasm32-unknown-unknown
./build.sh
```
