# xark-schema

A xark circuit's inputs as `schema.json` describes them (`xark build` writes it
from the `#[circuit]` fn's parameter types), and the one codec for their values:
natural JSON forms (dates, strings, enum names, bytes, numbers) to the circuit's
field elements, and public inputs back.

The CLI's `xark prove --inputs`, `@blueshift-gg/xark-wasm` (and so every client
`xark client` generates), and a circuit crate's `client.wasm` all encode through
it, so they can't disagree. It depends on the BN254 scalar field and `serde_json`
only, not the prover: a binding for another language needs just this crate.
