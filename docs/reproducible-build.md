# Reproducible build for the on-chain verifier

An audit is only as useful as the link between *the source someone read* and *the bytes the chain
runs*. This defines that link: a pinned toolchain, a pinned dependency graph, an exact
`cargo-build-sbf` invocation, and a SHA-256 of the resulting `.so` anyone can recompute.

## The audit unit

The reproducible-build target is a **reference Solana program** wrapping the verifier core
([`xark_verifier::verify_groth16`]) as its entrypoint:

* Crate: `crates/verifier/reference-program/`
* Output: `xark_verifier_reference_program.so`
* Pinned hash: `crates/verifier/reference-program/expected.sha256`

It reads its VK from account 0's data and the proof + public inputs from instruction data — so the
same `.so` works for *any* circuit, and the audit artifact is one fixed binary rather than one per
circuit. Production deployments typically embed their VK at compile time
(`Verifier<N>::from_le_bytes(include_bytes!("vk.bin"))`); for those, run this recipe with your own
program crate and pin *its* hash.

[`xark_verifier::verify_groth16`]: ../crates/verifier/src/verifier.rs

## Pinned toolchain

| Component | Pinned version | Install |
|---|---|---|
| `cargo-build-sbf` (Anza / Solana CLI) | `4.0.0` (`platform-tools v1.53`, `rustc 1.89.0`) | `sh -c "$(curl -sSfL https://release.anza.xyz/v4.0.0/install)"` |
| Host `cargo` (only drives `cargo-build-sbf`) | Workspace `rust-version = "1.85"` | Any 1.85+ stable is fine. |

`cargo-build-sbf` is the *only* thing that touches the SBF target's codegen. Its bundled
`platform-tools` includes a pinned `rustc`/`cargo`/`llvm`/`solana-ld` — that determines the
deterministic-codegen contract.

The reference program's release profile (`crates/verifier/reference-program/Cargo.toml`) also pins:

```toml
[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
overflow-checks = false
panic = "abort"
strip = "symbols"
incremental = false
```

— matching `cargo-build-sbf`'s defaults and forbidding the two things that break determinism in
practice (multi-codegen-unit parallelism, incremental builds).

## Vendored dependencies (`Cargo.lock`-as-source-of-truth)

The reference program lives in **its own workspace** (`excluded` from the root workspace) and ships
its own `Cargo.lock`, the source of truth for the dependency graph compiled into the `.so`:

* `xark-verifier` is a `path` dep back to `crates/verifier/`, so verifier source changes flow into
  the next build automatically.
* All other deps (`solana-program-entrypoint`, `solana-program-error`, `solana-nostd-alt-bn128`, …)
  are pinned to crates.io versions whose checksums are committed in `Cargo.lock`.

We do **not** vendor sources — `cargo` verifies each registry dependency against the checksum in
`Cargo.lock`. CI passes `--locked`, so the build fails if dependency resolution would change the
lockfile. It may still download missing, checksum-verified crates; fully offline builds additionally
need a populated Cargo cache or a separately audited vendor directory.

## The build command line

From the repo root:

```bash
cargo build-sbf \
  --arch v0 \
  --manifest-path crates/verifier/reference-program/Cargo.toml \
  --sbf-out-dir build-out/ \
  -- \
  --locked
```

This (1) resolves against `crates/verifier/reference-program/Cargo.lock` (`--locked` forwarded to the
inner `cargo`), (2) explicitly targets SBPFv0, whose dynamic syscall ABI the target selects,
(3) compiles with the pinned `platform-tools` rustc, and (4)
links a single `.so` into `build-out/`. Verify:

```bash
shasum -a 256 -c crates/verifier/reference-program/expected.sha256
```

`expected.sha256` is standard `shasum -c` format (`<hex-hash>  <basename>`); run from `build-out/`
(or adjust the path) and `shasum -c` exits 0 iff the binary matches.

## Verifying a deployed program against the audited bytes

Once deployed, fetch the on-chain bytecode and re-hash:

```bash
# `--output-file` writes the ELF the loader is executing.
solana program dump <PROGRAM_ID> deployed.so
shasum -a 256 deployed.so
```

The hash must match `expected.sha256` for the audited source revision. If it doesn't, *either* the
deployed program isn't the audited one *or* the audited source has drifted since deployment — either
is a security-relevant finding.

## Updating the pinned hash (rare)

Any change affecting the compiled bytes — a verifier source edit, a `cargo update` in
`reference-program/Cargo.lock`, a new pinned `platform-tools` — changes the SHA-256. To roll it:

1. Run the `cargo build-sbf` command above.
2. Recompute the SHA-256.
3. Update `crates/verifier/reference-program/expected.sha256` and commit it in the *same* PR as the
   change that produced it.

CI (`.github/workflows/reproducible-build.yml`) fails on mismatch — the PR can't merge with a drifted
hash.

## Threats this catches

* **Source-vs-deployed drift.** A different `.so` deployed than what was audited — hash comparison
  catches it.
* **Toolchain-vs-deployed drift.** A rebuild with different `platform-tools` — CI's pinned toolchain
  prevents the PR from updating the hash without an explicit toolchain bump.
* **Dependency drift.** A transitive dep bump or a tampered registry source — `Cargo.lock` +
  `--locked` catches version drift; cargo's per-crate checksum catches a registry swap.

## Threats this does *not* catch

* **Compromised pinned toolchain.** If the pinned `platform-tools` itself has a backdoor that survives
  source review, the hash matches but runtime behavior is malicious. Mitigation: independent
  third-party rebuilds using a different installation of the same pinned version.
* **Compromised on-chain loader.** Out of scope — the loader is a property of the Solana runtime, not
  the audited program.
