# Reproducible build for the on-chain verifier

An audit is only as useful as the link between *the source someone read* and
*the bytes the chain runs*. This document defines that link: a pinned
toolchain, a pinned dependency graph, an exact `cargo-build-sbf` invocation,
and a SHA-256 of the resulting `.so` that anyone can recompute.

## The audit unit

The reproducible-build target is a **reference Solana program** that wraps
the verifier core ([`xark_verifier::verify_groth16`]) as its entrypoint:

* Crate: `crates/verifier/reference-program/`
* Output: `xark_verifier_reference_program.so`
* Pinned hash: `crates/verifier/reference-program/expected.sha256`

The reference program reads its VK out of account 0's data and the proof +
public inputs out of instruction data — so the same `.so` works for *any*
circuit, and the audit artifact is one fixed binary rather than one per
circuit. Production deployments will typically embed their VK at compile
time (`Verifier<N>::from_le_bytes(include_bytes!("vk.bin"))`); for those, run
this same recipe with your own program crate and pin *its* hash.

[`xark_verifier::verify_groth16`]: ../crates/verifier/src/verifier.rs

## Pinned toolchain

| Component | Pinned version | How to install |
|---|---|---|
| `cargo-build-sbf` (Anza / Solana CLI) | `stable` channel, captured by `release.anza.xyz/stable/install` (currently `solana-cli 3.x` with `platform-tools v1.52`, `rustc 1.89.0`) | `sh -c "$(curl -sSfL https://release.anza.xyz/stable/install)"` |
| Host `cargo` (only used to drive `cargo-build-sbf`) | Workspace `rust-version = "1.85"` (see `Cargo.toml`) | Any 1.85+ stable toolchain is fine — host `cargo` only invokes `cargo-build-sbf`. |

`cargo-build-sbf` is the *only* thing that touches the SBF target's code
generation. Its bundled `platform-tools` includes a pinned `rustc` /
`cargo` / `llvm` / `solana-ld` — that's what determines the
deterministic-codegen contract.

The reference program's release profile (in
`crates/verifier/reference-program/Cargo.toml`) also pins:

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

— matching `cargo-build-sbf`'s defaults and forbidding the two things that
break determinism in practice (multi-codegen-unit parallelism, incremental
builds).

## Vendored dependencies (`Cargo.lock`-as-source-of-truth)

The reference program lives in **its own workspace** (it is `excluded`
from the root workspace in `Cargo.toml`) and ships its own
`Cargo.lock`. That lockfile is the source of truth for the dependency
graph that gets compiled into the `.so`:

* `xark-verifier` is a `path` dependency back to `crates/verifier/`, so
  changes to the verifier source automatically flow into the next build.
* All other deps (`solana-program-entrypoint`, `solana-program-error`,
  `solana-nostd-alt-bn128`, …) are pinned to crates.io versions whose
  checksums are committed in `Cargo.lock`.

We do **not** vendor sources into the repo — `cargo` already verifies
the registry checksum of every dep against `Cargo.lock` on build, so a
committed `Cargo.lock` is byte-for-byte equivalent to a vendored
`vendor/` tree for reproducibility purposes. CI uses
`--frozen --locked` semantics by passing `--locked` (see workflow), which
fails the build if the lockfile would need to change.

## The build command line

From the repo root:

```bash
cargo build-sbf \
  --manifest-path crates/verifier/reference-program/Cargo.toml \
  --sbf-out-dir build-out/ \
  -- \
  --locked
```

This:

1. resolves against `crates/verifier/reference-program/Cargo.lock`
   (the `--locked` flag is forwarded to the inner `cargo`),
2. compiles for the `sbpf-solana-solana` target with the pinned
   `platform-tools` rustc,
3. links a single `.so` into `build-out/`.

Verify the result:

```bash
shasum -a 256 -c crates/verifier/reference-program/expected.sha256
```

`expected.sha256` is in the standard `shasum -c` format
(`<hex-hash>  <basename>`); run the command from `build-out/` (or
adjust the path) and `shasum -c` exits 0 iff the binary matches.

## Verifying a deployed program against the audited bytes

Once the program is deployed, fetch the on-chain bytecode and re-hash:

```bash
# `--output-file` writes the ELF the loader is executing.
solana program dump <PROGRAM_ID> deployed.so
shasum -a 256 deployed.so
```

The hash must match the `expected.sha256` for the source revision being
audited. If it doesn't, *either* the deployed program is not the audited
one, *or* the audited source has drifted since the deployment; either is a
security-relevant finding.

## Updating the pinned hash (rare)

Any change that affects the compiled bytes — a verifier source edit, a
`cargo update` in `reference-program/Cargo.lock`, a new pinned
`platform-tools` — will change the SHA-256. To roll it forward:

1. Run the `cargo build-sbf` command above.
2. Recompute the SHA-256.
3. Update `crates/verifier/reference-program/expected.sha256` and
   commit it in the *same* PR as the change that produced it.

CI (`.github/workflows/reproducible-build.yml`) enforces this by failing
on mismatch — the PR can't merge with a drifted hash.

## Threats this catches

* **Source-vs-deployed drift.** Someone deploys a different `.so` than
  what was audited. Hash comparison catches it.
* **Toolchain-vs-deployed drift.** Someone rebuilds with a different
  `platform-tools` and deploys that. CI's pinned toolchain prevents the
  PR from updating the hash without an explicit toolchain bump.
* **Dependency drift.** A transitive dep gets a new version (or its
  registry source is tampered with). `Cargo.lock` + `--locked` catches
  the version drift; cargo's per-crate checksum catches a registry swap.

## Threats this does *not* catch

* **Compromised pinned toolchain.** If the pinned `platform-tools`
  itself has a backdoor that survives source-level review, the hash
  matches but the runtime behavior is malicious. Mitigation: independent
  third-party rebuilds using a different installation of the same
  pinned version, which would catch a per-host-tampered toolchain.
* **Compromised on-chain loader.** Out of scope for this document; the
  loader is a property of the Solana runtime, not of the audited program.
