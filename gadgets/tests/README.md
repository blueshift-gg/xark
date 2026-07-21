# xark-tests

The whole workspace's integration tests, benchmarks, and committed circuit
fixtures, gathered into one `publish = false` crate. Nothing here ships to
crates.io.

```
cargo test -p xark-tests # all integration tests (host + on-chain)
cargo test -p xark-tests --test sbpf # just the on-chain Mollusk suite
cargo bench -p xark-tests # all benchmarks
```

## Why one crate

Two constraints force the aggregator shape:

1. **On-chain tests need the fixtures in a lib.** `svm-unit-test` compiles each
 `#[svm_test]` body into its own SBF cdylib that depends on *this crate's
 lib*. The fixture `const`s therefore live in `src/lib.rs` (typed
 `Verifier<N>` / `Proof` / public-input arrays), reachable from every
 compilation context including those generated cdylibs.

2. **The lib must stay no_std / SBF-buildable.** So the heavy host-only deps
 (`xark-backend`, Arkworks, `criterion`, `proptest`) are **dev-dependencies**;
 only the no_std `xark-verifier` is a normal dependency, re-exported from the
 lib. This keeps the SBF cdylibs from trying to compile the prover for the
 Solana target.

The `xark_bin()` helper in `src/lib.rs` locates (and, if needed, builds) the
`xark` binary so the CLI integration tests can shell out to it without relying
on `CARGO_BIN_EXE_xark` (which is only set for tests inside the `cli` crate).

## Layout

- `src/lib.rs` — fixture consts + the `xark` binary locator.
- `tests/` — integration tests: CLI end-to-end and per-gadget (`aes128`,
 `keccak`, `poseidon`, …), the on-chain `sbpf` suite, public-input `binding`,
 `fuzz`, backend `ptau` / `serialization` / `solana_format` / `soundness`.
- `benches/groth16.rs` — proving/verifying benchmarks (`harness = false`).
- `examples/to_snarkjs.rs` — exports fixtures into snarkjs-compatible JSON for
 differential testing.

Fixtures live under `gadgets/tests/fixtures/groth16/` and are
embedded with `include_bytes!`; regenerate them with `xark export`.
