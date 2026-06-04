# Trusted Setup Policy

Groth16 requires per-circuit trusted setup. xark deliberately makes this
impossible to miss.

## What the CLI does

`xark setup` refuses to run unless `--insecure-dev-mode` is passed.

Without the flag:

```text
Groth16 setup requires trusted randomness.

For local testing, pass --insecure-dev-mode.
Do not use insecure dev parameters in production.
```

With the flag, `xark setup` seeds a `ChaCha20Rng` deterministically and runs
`Groth16::circuit_specific_setup`. The resulting keys are written along
with `metadata.json`, which always records `setup_mode: "insecure-dev-mode"`
and `production_safe: false`.

## What this is not

This is **not** an MPC ceremony, a powers-of-tau import, or any other
production-grade setup. There is currently no path to import externally
generated proving/verifying keys; that work is tracked in Milestone 7+.

## Hardening checklist (future)

* Powers of Tau import with transcript verification.
* MPC ceremony driver that yields the same `ProvingKey<Bn254>` layout.
* `setup_mode = "imported"` in metadata, with a hash of the source
  transcript.
* CLI-level check that `setup_mode != "insecure-dev-mode"` for any keys
  used by a "production" verify path.
