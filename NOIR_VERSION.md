# Supported nargo / ACIR Version

xark lowers **ACIR** (the intermediate representation `nargo` emits), not Noir
source — it never parses the Noir language. What this pin constrains is the
ACIR *artifact format* and *opcode/black-box set*, which ship from the
noir-lang monorepo and are still pre-1.0 (there is no stable, independently
versioned ACIR interface yet). So the version that matters is the **`nargo`
version that compiled the circuit**, which must match the `acir`/`acvm` crate
version xark links against. Your Noir source may use any language feature that
`nargo` version supports.

```
Supported Noir version:        1.0.0-beta.21
Supported nargo version:       1.0.0-beta.21
Supported ACIR artifact format: bytecode format byte 0x03 (msgpack-compact) inside the standard nargo target/<name>.json envelope
Supported witness format:       WitnessStack serialized via rmp-serde (msgpack-compact) and gzip-compressed (target/<name>.gz)
Date tested:                    2026-06-03
Known incompatible versions:    every Noir release earlier than 1.0.0-beta.21, and every release after 1.0.0-beta.21 until this file is updated
```

xark pins `acir` to the matching nargo tag (`v1.0.0-beta.21`, commit
`89a0f0faf3a5f1273c8ac4843b7877882437e277`); it re-exports and pulls in
`acir_field` / `acvm` at the same commit. Bumping nargo requires bumping the git
tag in `Cargo.toml` and re-testing every fixture under `crates/tests/fixtures/`.
