# Serialization

Xark writes authoritative native binaries plus interoperable JSON where it is useful. The default
build artifact is the compact `circuit.xbc`; pass `xark build --emit-json` only when inspecting the
expanded circuit/R1CS as text.

## Binary

Uses Arkworks' `CanonicalSerialize`/`CanonicalDeserialize` with `Compress::Yes` and `Validate::Yes`
on read. The on-disk layout is exactly what `ark-groth16` 0.6 produces for `ProvingKey<Bn254>`,
`VerifyingKey<Bn254>`, `Proof<Bn254>`.

* `pk.bin` — `ark_groth16::ProvingKey<Bn254>`.
* `vk.bin` — `ark_groth16::VerifyingKey<Bn254>`.
* `proof.bin` — `ark_groth16::Proof<Bn254>`.
* `public_inputs.bin` — canonical `Vec<Fr>` used by `xark verify`.
* `proof.solana.bin` — the 256-byte little-endian proof wire format.
* `public_inputs.solana.bin` — public `Fr` values as consecutive 32-byte little-endian scalars.
* `instruction_data.bin` — `proof.solana.bin || public_inputs.solana.bin`, ready for the generated
  on-chain verifier.

`xark export` copies those wire files into the generated verifier crate as its
self-test vector and pins `xark-verifier` to the CLI's exact release or clean
Git revision. A dirty source build uses a path to the same local checkout, so
unreleased verifier changes can be tested without naming a stale remote revision.

## JSON

`xark setup` writes `snarkjs-verification_key.json`. `xark prove` writes
`snarkjs-proof.json` and `snarkjs-public.json`; the latter is an array of decimal-string public
signals in declaration/flatten order. These files can be passed directly to `snarkjs groth16 verify`.

### `snarkjs-proof.json`

```json
{
 "pi_a": ["<x>", "<y>", "1"],
 "pi_b": [["<x0>", "<x1>"], ["<y0>", "<y1>"], ["1", "0"]],
 "pi_c": ["<x>", "<y>", "1"],
 "protocol": "groth16",
 "curve": "bn128"
}
```

G2 coordinates use the `Fq2 = c0 + c1*u` convention.

### `snarkjs-verification_key.json`

```json
{
 "protocol": "groth16",
 "curve": "bn128",
 "nPublic": 1,
 "vk_alpha_1": ["...", "...", "1"],
 "vk_beta_2": [["...", "..."], ["...", "..."], ["1", "0"]],
 "vk_gamma_2": [["...", "..."], ["...", "..."], ["1", "0"]],
 "vk_delta_2": [["...", "..."], ["...", "..."], ["1", "0"]],
 "IC": [["...", "...", "1"], ["...", "...", "1"]]
}
```

### Proof bundle

`xark prove` also writes `<entry>-<proof-hash>.proof.json`, a self-contained bundle containing the
snarkjs proof/public signals, circuit hash, proof fingerprint, and on-chain calldata hex. Full hex
is retained in files while terminal output stays compact unless `--verbose` is requested.
