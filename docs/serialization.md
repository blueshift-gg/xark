# Serialization

xark writes both binary and JSON forms of every artifact. Binary is
authoritative (it's what verify reads); JSON is for tooling and
inspection.

## Binary

Uses Arkworks' `CanonicalSerialize`/`CanonicalDeserialize` with
`Compress::Yes` and `Validate::Yes` on read. The on-disk layout is
exactly what `ark-groth16` 0.6 produces for `ProvingKey<Bn254>`,
`VerifyingKey<Bn254>`, and `Proof<Bn254>`.

Files:

* `proving_key.bin` — `ark_groth16::ProvingKey<Bn254>`.
* `verifying_key.bin` — `ark_groth16::VerifyingKey<Bn254>`.
* `proof.bin` — `ark_groth16::Proof<Bn254>`.

## JSON

Coordinates are always emitted as decimal strings (Fr/Fq big-integer
representation). The `encoding` field on `public_inputs.json` records the
choice so future hex support can opt in.

### `proof.json`

```json
{
 "curve": "bn254",
 "protocol": "groth16",
 "a": { "x": "<dec>", "y": "<dec>" },
 "b": { "x": ["<c0>", "<c1>"], "y": ["<c0>", "<c1>"] },
 "c": { "x": "<dec>", "y": "<dec>" }
}
```

G2 coordinates use the `Fq2 = c0 + c1*u` convention. The `x` array stores
`[c0, c1]` for the x coordinate.

### `verifying_key.json`

```json
{
 "curve": "bn254",
 "protocol": "groth16",
 "alpha_g1": { "x": "...", "y": "..." },
 "beta_g2": { "x": ["...","..."], "y": ["...","..."] },
 "gamma_g2": { "x": ["...","..."], "y": ["...","..."] },
 "delta_g2": { "x": ["...","..."], "y": ["...","..."] },
 "gamma_abc_g1": [ { "x": "...", "y": "..." },... ]
}
```

### `public_inputs.json`

```json
{
 "curve": "bn254",
 "field": "fr",
 "encoding": "decimal-string",
 "inputs": ["..."]
}
```

The `inputs` array is in exactly the same order as the circuit's
`Public<Field>` parameters (public-input declaration order). The verifier
consumes this order verbatim.
