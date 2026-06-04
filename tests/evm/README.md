# EVM verifier smoke test (WS-E.1)

This directory contains a Foundry-based smoke test for the Solidity
verifier that `xark export evm` produces. It is **not** part of the normal
`cargo test --workspace` run — running it requires [Foundry](https://book.getfoundry.sh/).
The Rust-side test at `crates/groth16-backend/tests/evm_export.rs` is what
gates this in CI.

## Files

* `Verifier.t.sol` — Solidity test that hardcodes the proof + public input
  for `tests/fixtures/groth16/arithmetic_square/` and asserts that
  `Verifier.verifyProof(...)` returns `true`. Also asserts that flipping the
  public input makes the verifier return `false`.
* `foundry.toml` — minimal Foundry config: `solc 0.8.20`, `src = "."`.
* `regenerate.sh` — script that regenerates `Verifier.sol` from the
  committed verifying-key fixture using `xark export evm`. The regenerated
  contract is **not** checked in; the test imports it from a relative path
  so you must regenerate it locally before running `forge test`.

## Running

```bash
# 1. Regenerate Verifier.sol from the committed fixture VK.
./tests/evm/regenerate.sh

# 2. Run the smoke test.
cd tests/evm && forge test -vv
```

Expected output:

```
[PASS] testVerifyProof_accepts_valid()
[PASS] testVerifyProof_rejects_tampered_input()
```

## Regenerating the proof fixture

If the committed `proof.bin` / `public_inputs.json` ever changes (e.g.
because the prover RNG seed or a constraint emission changes), the
hardcoded constants in `Verifier.t.sol` will be stale. To regenerate:

```bash
cargo test -p groth16-backend --test evm_export dump_fixture_for_foundry
cat target/tmp/proof_fixture.txt
```

Then paste the printed `a`, `b`, `c`, and `inputs` values into
`Verifier.t.sol`. The Rust test `exported_contract_sha256_is_pinned` will
also need updating in that case.
