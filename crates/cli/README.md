# xark-cli

[![crates.io](https://img.shields.io/crates/v/xark-cli.svg)](https://crates.io/crates/xark-cli)

The `xark` command: build, test, prove and verify zero-knowledge circuits
written in Rust, and generate their Solana verifiers and TypeScript clients. Part
of [xark](https://github.com/blueshift-gg/xark).

```sh
cargo install xark-cli
xark doctor               # check your setup
```

It needs stable Rust 1.89 or newer. `xark build` adds the
`wasm32-unknown-unknown` target with `rustup` the first time it runs.

## From a new circuit to a proof

```sh
xark init my-circuit                                    # a circuit crate, with tests
xark test my-circuit                                    # build it, run its tests
xark prove my-circuit --inputs '{"secret": 3, "result": 9}'
xark verify my-circuit
xark export my-circuit                                  # the Solana verifier crate
```

The first `prove` makes the key from your machine's randomness: a single-party
trusted setup, sound unless whoever made it kept that randomness. For a key no one
party has to be trusted for, use `xark ceremony`.

## Commands

| Command | What it does |
|---|---|
| `doctor` | Checks your toolchain |
| `init` | Creates a circuit crate, set up for rust-analyzer |
| `build` | Compiles a circuit crate into `target/xark/<name>/` |
| `check` | Reports unsupported Rust as compiler diagnostics, for your editor |
| `test` | Builds the circuit, then runs the crate's `cargo test` |
| `inspect` | Prints the circuit's size: variables, constraints, public inputs |
| `profile` | Shows which source lines the constraints come from (`--html` for a shaded view) |
| `setup` | Makes the proving and verifying keys |
| `ceremony` | Runs a multi-party trusted setup |
| `prove` | Solves the witness from `--inputs` and makes a proof |
| `verify` | Checks a proof against the verifying key |
| `export` | Writes the Solana verifier crate, with the key embedded |
| `client` | Writes a typed TypeScript client |
| `clean` | Removes xark's build output |
| `completions` | Prints shell completions |

Each command takes the circuit crate's directory, the current one by default.
`xark <command> --help` lists its options.

## Learn more

- [Quickstart](https://github.com/blueshift-gg/xark#quickstart)
- [TypeScript clients](https://github.com/blueshift-gg/xark/blob/master/docs/typescript.md)
- [Editor diagnostics](https://github.com/blueshift-gg/xark/blob/master/docs/editor.md)
- [Trusted setup](https://github.com/blueshift-gg/xark/blob/master/docs/trusted-setup.md)
