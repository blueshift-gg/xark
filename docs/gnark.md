# Proving with gnark

`xark setup`, `xark prove` and `xark verify` take `--backend gnark`: the circuit
is still written in Rust and compiled by xark, and xark still solves the witness,
but the Groth16 setup, proof and verification are
[gnark](https://github.com/Consensys/gnark)'s. The default backend, xark's own
prover, is unchanged.

```sh
xark prove  --backend gnark --inputs '{"secret": 3, "result": 27}'
xark verify --backend gnark
```

The first `prove` builds the circuit and makes a key, as it does for the default
backend. It needs [Go](https://go.dev/dl) 1.24 or newer: the first use builds a
small Go helper, `xark-gnark`, into `~/.cache/xark/` (and downloads gnark's
modules). `XARK_GNARK=<path>` names a helper built ahead of time (`go build` in
`crates/cli/gnark/`), for a machine without Go or the network.

## What is written where

```text
<keys>/gnark/                 # xark setup --backend gnark
  circuit.r1cs                # the keyed rows, iden3 format
  circuit.ccs                 # the same rows as a gnark constraint system
  pk.bin  vk.bin              # gnark's proving and verifying keys
  metadata.json
target/xark/<name>/gnark/     # xark prove --backend gnark
  witness.wtns                # the solved witness, iden3 format
  proof.bin                   # gnark's proof
  public_witness.bin          # gnark's public witness
```

`<keys>` is where xark's own keys go: `keys/<name>/` in a project, otherwise
`target/xark/<name>/`.

## The conversion

xark hands the circuit over in iden3's two files, the formats circom writes and
snarkjs reads:

- `circuit.r1cs` holds the rows the key is made for, the same rows a xark key
  over a 2^k domain would get (`--r1cs-form` chooses them as for `xark setup`).
  Wire 0 is the constant one, the public inputs follow in declaration order, and
  every other variable comes after.
- `witness.wtns` holds the value of every wire for one proof.

`xark-gnark` reads the rows into a gnark `constraint.R1CS` and writes it as
`circuit.ccs`, which any gnark program reads back with
`groth16.NewCS(ecc.BN254).ReadFrom`. Every xark variable becomes a gnark input
wire (public or secret) and none an internal one: xark has already computed the
whole witness, so gnark's solver has nothing to derive and only checks each row.
The constraint count is exactly xark's.

To use the circuit from your own gnark code, take `circuit.ccs` and the keys, and
fill a witness from `witness.wtns` (`readWitness` in `crates/cli/gnark/main.go`
is thirty lines).

## What it does not do

- The key is from gnark's `groth16.Setup`: one machine's randomness, like `xark
  setup` without a `.ptau`. `--ptau-file`, `xark ceremony`, and the seeded and
  smooth-domain setups are the default backend's.
- gnark's keys and proofs are not xark's: `xark export` (the Solana verifier) and
  `xark client` take the default backend's. A gnark proof verifies with `xark
  verify --backend gnark`, or with gnark.
- BN254 only, as the rest of the proving toolchain.

## How the backends compare

[`benches/gnark/`](../benches/gnark/README.md) proves the same functions with
arkworks, xark's prover and gnark, and beside a circuit written directly in
gnark.
