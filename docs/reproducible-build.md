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
| `platform-tools` (SBF `rustc`/`llvm`/`solana-ld`) | **`v1.54`, pinned explicitly** via `cargo-build-sbf --tools-version v1.54` | Fetched on demand by `cargo-build-sbf`. |
| `cargo-build-sbf` (Anza / Solana CLI) | Any recent release (CI uses `v4.0.0`) — only the *orchestrator* | `sh -c "$(curl -sSfL https://release.anza.xyz/v4.0.0/install)"` |
| Host `cargo` (only drives `cargo-build-sbf`) | Workspace `rust-version = "1.85"` | Any 1.85+ stable is fine. |

The `platform-tools` bundle (a pinned `rustc`/`cargo`/`llvm`/`solana-ld`) is the *only* thing that
determines the SBF codegen, so it — not the Anza CLI release — is what we pin, explicitly via
`--tools-version v1.54`. This is verified **orchestrator-independent**: two different
`cargo-build-sbf` versions (whose *defaults* were `v1.52` and `v1.54`), both invoked with
`--tools-version v1.54`, produce byte-identical `.so`s. So the CLI release above is just a convenient
source of `cargo-build-sbf`; bumping it does not change the hash, but bumping `--tools-version` does.

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
* All other deps (`pinocchio` — the zero-copy entrypoint, `solana-nostd-alt-bn128`, …) are pinned to
  crates.io versions whose checksums are committed in `Cargo.lock`.

We do **not** vendor sources — `cargo` verifies each dep's registry checksum against `Cargo.lock` on
build, so a committed `Cargo.lock` is byte-for-byte equivalent to a `vendor/` tree for
reproducibility. CI passes `--locked` (`--frozen --locked` semantics), failing if the lockfile would
need to change.

## The build command line

From the repo root:

```bash
cargo build-sbf \
  --manifest-path crates/verifier/reference-program/Cargo.toml \
  --sbf-out-dir build-out/ \
  --tools-version v1.54 \
  -- \
  --locked
```

This (1) resolves against `crates/verifier/reference-program/Cargo.lock` (`--locked` forwarded to the
inner `cargo`), (2) compiles for `sbpf-solana-solana` with the **`--tools-version v1.54`** pinned
`platform-tools` rustc, (3) links a single `.so` into `build-out/`. Verify:

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
`reference-program/Cargo.lock`, or a bump to `--tools-version` — changes the SHA-256. To roll it:

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
