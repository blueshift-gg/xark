# Serialization

xark's artifacts are binary. Verifying keys, proofs and public inputs use Arkworks'
`CanonicalSerialize` / `CanonicalDeserialize` with `Compress::Yes`, and `Validate::Yes` on read,
so the layout is exactly what `ark-groth16` 0.6 produces for `VerifyingKey<Bn254>` and
`Proof<Bn254>`. A proving key is `ark-groth16`'s `ProvingKey<Bn254>` behind a short header
(`KeyFormat` v2: `XKPK`, version `2`, a point mode — compressed, or uncompressed with
`xark setup --uncompressed` — and the QAP domain size as a little-endian `u64`; 14 bytes).
Dev keys default to the smallest domain of `2^k`, `3·2^k` or `9·2^k` points, and a smooth
(`3·2^k`, `9·2^k`) key can be proved against only by xark's prover and arkworks with a
mixed-radix reduction; see
[`crates/groth16/README.md`](../crates/groth16/README.md).

| File | Written by | Contents |
|---|---|---|
| `circuit.xbc` | `xark build` | the circuit, as DAG-compact bytecode ([dag-functions.md](dag-functions.md)) |
| `schema.json` | `xark build` | the circuit's inputs: names, types, public or private |
| `sources.json` | `xark build` | which source statement each constraint came from |
| `digest` | `xark build` | the R1CS digest `xark build` prints |
| `pk.bin` / `vk.bin` | `xark setup` | the `KeyFormat` header + `ProvingKey<Bn254>` / `VerifyingKey<Bn254>` |
| `metadata.json` | `xark setup`, `xark ceremony finalize` | setup mode, `production_safe`, `circuit_hash`, `digest`, R1CS form, domain size, … |
| `r1cs.stream` | `xark setup` (a `minimized` key) | the keyed rows, so `xark prove` skips the minimize |
| `pk.decoded.bin` | `xark prove --cache` | the proving key with uncompressed points |
| `proving_key.bin` / `verifying_key.bin` | `xark ceremony` | the same as `pk.bin` / `vk.bin`, from the MPC |
| `proof.bin` | `xark prove`, xark-wasm `prove` | `Proof<Bn254>` |
| `public_inputs.bin` | `xark prove`, xark-wasm `prove` | `Vec<Fr>`: an 8-byte little-endian length, then each value as 32 bytes little-endian |

`xark build --emit-json` also writes `circuit.json` and `r1cs.json`, for reading; nothing reads
them back.

xark-wasm's `verify(vk, proof, publicInputs)` and `xark verify` take exactly these bytes, and
xark-wasm's `decode_public_inputs` turns `public_inputs.bin` into decimal strings.

The on-chain Solana verifier takes its own layout: every field element 32 bytes little-endian,
points uncompressed, G2 as `(c0, c1)`, and a proof as `-A || B || C` (256 bytes, `A` negated).
`xark export` writes it (`*.solana.bin`), and a client's `proof.toBytes()` is a proof in it
(`xark_groth16::solana`). A proof in this form is read too: xark-wasm's `verify`, a client
verifier and `xark verify --proof` take either, by its length (128 bytes compressed, 256
on-chain), and check every point of an on-chain one.

Public inputs are in exactly the same order as the circuit's `Public<Field>` parameters
(public-input declaration order). The verifier consumes this order verbatim.
