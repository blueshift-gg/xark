# TypeScript clients

`xark client` generates a typed TypeScript client from a circuit's inputs: prove
and verify in Node, the browser or a Worker, with the circuit's own types and
helper functions.

```sh
xark client                                  # writes target/xark/<circuit>/<circuit>.ts
npm install @blueshift-gg/xark@0.3           # the runtime it imports
```

`xark build` also writes `schema.json`: every input's name, visibility and
`Input::TYPE`, plus the public inputs in proof order. `xark client` resolves it
into the standard types and writes one `.ts` file: constants and a type per enum,
an interface per struct, the inputs, the public inputs as given and as decoded, and
the circuit, which makes its provers and verifiers. What every client shares
(`Field`, `Proof`, loading xark-wasm and the build output) is xark-wasm's
`@blueshift-gg/xark/client`, so the file holds only the circuit, and an app
imports only the file. The circuit's `schema.json` is inlined in it, so the file
has no relative import and needs no project settings (Node runs it as is).
Each type is the one you'd write by hand:

```ts
export const Country = { AD: "AD", AE: "AE", /* … */ US: "US", ZW: "ZW" } as const;
export type Country = (typeof Country)[keyof typeof Country]; // "AD" | "AE" | …

export interface Identity {
  document: Text;              // a string, at most 31 bytes
  born: Date;                  // a day, 1900-01-01 to 2100-12-31 (UTC)
  nationality: Country;        // Country.US, or "US"; "XX" won't compile
  netWorth: U64;               // bigint | number, in the attestor's unit
  expires: Date;
  salt: FieldInput;            // a Field, or an integer
}
```

A field input takes a plain integer (a `bigint`, a safe integer, a decimal or
`0x`-hex string) or a `Field`; either way it must be below the field's modulus, so a
value that would wrap or round never reaches the prover, and a mistake names the
input. `new Field(x)` checks it where you make it, and also takes little-endian
bytes (as proofs and Rust's `Field::from_le_bytes` have them; `Field.fromBeBytes`
for the other order). Decoded public inputs and Rust functions return `Field`s.

A prover and a verifier are separate, each made from a URL serving a copy of
`target/xark/<circuit>/` or from the bytes, so each has only the methods it can
run. A proof travels as its bytes, `proof.toBytes()`; the verifier brings the public
inputs it requires:

```ts
import { Country, Field, Identity, Policy, Zkyc } from "./zkyc";

// In the app: fetches circuit.xbc, pk.bin, sources.json and client.wasm, and loads
// xark-wasm (node, web or workerd). Outside a browser, pass the files' bytes instead:
// Zkyc.prover({ circuit: readFileSync("…/circuit.xbc"), provingKey: …, client: … }).
const prover = await Zkyc.prover("/circuits/zkyc/");
const id = { document: "A1938274", born: new Date("1990-01-01"), nationality: Country.US, netWorth: 1_000_000, expires: new Date("2030-01-01"), salt: new Field(saltBytes) };
const commitment = Identity.commitment(id); // the circuit's own Rust (below)
const policy = Policy.default().on(new Date()).minAge(18).nationalities([Country.US, Country.GB, "FR", "DE"]);
const proof = prover.prove({ id, commitment, policy });
proof.publicInputs.policy.allowed; // ["DE", "FR", "GB", "US"]: decoded, a Date stays a Date
send(proof.toBytes(), commitment);

// On the server: check it proves the policy you require, not just any.
const verifier = await Zkyc.verifier(vkBytes); // or a URL, or { verifyingKey, client }
verifier.verify(bytes, { commitment, policy: required }); // true
```

`proof.toBytes()` is the proof as the Solana verifier `xark export` generates reads
it (256 bytes; `Proof::from_le_bytes` on chain), so a program checks it against
public inputs it supplies itself, such as its policy or a root in its state.
`proof.toBytesCompressed()` is half the size, for anywhere else; a verifier reads
either.

To be sure the prover runs the circuit the client was generated from, and not
whatever a deployment serves, pin it: `Zkyc.prover(url, { digest: Zkyc.digest })`
refuses any other circuit (`Zkyc.digest` is the digest `xark build` printed). The
check is one pass over the circuit when the prover is made (about 2 s for Ed25519 in
node), not per proof. A verifier pins its key the same way: `Zkyc.verifier(vk, {
keyHash })` refuses any other `vk.bin` (`xark setup` prints its sha256).

To prove on several threads, give the prover a worker pool:
`Zkyc.prover(url, { pool: await createPool() })`, with `createPool` from
`@blueshift-gg/xark/pool` (about 4× faster with 8 threads). A browser needs a
cross-origin isolated page for it, and proves in a Web Worker.

`Policy.default().on(…).minAge(18)` and `Identity.commitment(id)` are the crate's Rust,
not a TypeScript copy of it: the same `#[input]`, on an `impl` block, makes its
methods client functions, typed from their signatures and documented with their doc
comments.

```rust
#[input]
impl Default for Policy {
    /// A policy every holder passes: no expiry, age, net worth or nationality check.
    fn default() -> Policy { … }
}

#[input]
impl Policy {
    /// Checked on `today`: the holder's document mustn't have expired by then.
    pub fn on(self, today: impl Into<Days<1900, 2100>>) -> Policy { … }
    /// At least `years` old on `today` (set it with `on` first).
    pub fn min_age(self, years: u16) -> Policy { … }
}
```

A trait's `impl` works the same way: `impl Default` gives `Policy.default()`.

`xark client` builds the crate's host code once more as `client.wasm` (beside
`circuit.xbc`; a prover or verifier made from a URL fetches it, or
`await Zkyc.ready(url)` loads it alone), with no JS glue, and
each call runs it: values cross in their natural forms, a Rust panic arrives as an
exception with its message. Parameters and results are any `Input` type. It
works from any crate: a gadget that puts `#[input]` on its types and their `impl`s
brings those functions to the client of every circuit that takes them, with
nothing added to xark. A method that takes `self` is also a method on the values
these functions return and on decoded public inputs, so a chain reads as in Rust:
`Policy.default().on(today).minAge(18).worthAtLeast(500_000)`. A method named like a field
can't be both in TypeScript: it stays `Policy.method(value, …)`, and `xark client`
warns, so you can rename it.

The client holds no encoding logic of its own: xark-wasm encodes values against
the schema with the same Rust code as `xark prove --inputs`, so the two can't
drift, and a mistake names its input (`id.document: "…" is longer than 31 bytes`).
Errors are typed for a UI to act on: an `InputError` carries the input's `path`
(`"id.document"`), and a `CheckFailed` the failing statement's `site` (`file`,
`line`, `col`, `text`, the functions it called into).
`clients/check/{zkyc,cube,sha256,merkle}/` hold those examples' generated clients
and their vitest tests. `npm test` there (run in CI) builds xark, xark-wasm and each
example, fails if a committed client is stale (`npm run update` rewrites it),
typechecks, and runs the tests in Node; a folder with a `<name>.test.ts` is all a new
example needs.

## Without a generated client

Prove and verify anywhere JavaScript runs with
[`@blueshift-gg/xark`](../crates/wasm/README.md) directly
(`prove(circuit, pk, inputs, sources?)`, `verify(vk, proof, publicInputs)`).
`xark prove` writes the same bytes `verify` takes: `proof.bin` and
`public_inputs.bin`.
