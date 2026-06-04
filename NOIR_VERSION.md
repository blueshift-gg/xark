# Supported Noir Version

```
Supported Noir version:        1.0.0-beta.21
Supported nargo version:       1.0.0-beta.21
Supported ACIR artifact format: bytecode format byte 0x03 (msgpack-compact) inside the standard nargo target/<name>.json envelope
Supported witness format:       WitnessStack serialized via rmp-serde (msgpack-compact) and gzip-compressed (target/<name>.gz)
Date tested:                    2026-06-03
Known incompatible versions:    every Noir release earlier than 1.0.0-beta.21, and every release after 1.0.0-beta.21 until this file is updated
```

xark pins `acir`, `acir_field`, and `acvm` to the matching Noir tag (`v1.0.0-beta.21`,
commit `89a0f0faf3a5f1273c8ac4843b7877882437e277`). Bumping Noir requires bumping
the git tags in `Cargo.toml` and re-testing every fixture under `tests/fixtures/`.
