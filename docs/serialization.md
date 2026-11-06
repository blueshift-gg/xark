# Serialization

xark's artifacts are binary. They use Arkworks' `CanonicalSerialize` / `CanonicalDeserialize` with
`Compress::Yes`, and `Validate::Yes` on read, so the layout is exactly what `ark-groth16` 0.6
produces for `ProvingKey<Bn254>`, `VerifyingKey<Bn254>` and `Proof<Bn254>`.

| File | Written by | Contents |
|---|---|---|
| `pk.bin` / `vk.bin` | `xark setup` | `ProvingKey<Bn254>` / `VerifyingKey<Bn254>` |
| `proving_key.bin` / `verifying_key.bin` | `xark ceremony` | the same types, from the MPC |
| `proof.bin` | `xark prove`, xark-wasm `prove` | `Proof<Bn254>` |
| `public_inputs.bin` | `xark prove`, xark-wasm `prove` | `Vec<Fr>`: an 8-byte little-endian length, then each value as 32 bytes little-endian |

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
