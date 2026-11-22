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
backend. It needs [Go](https://go.dev/dl) 1.24 or newer, and the first use needs
the network: it builds a small Go helper, `xark-gnark`, into
`$XDG_CACHE_HOME/xark/` (`~/.cache/xark/` without one), and `go` downloads gnark's
modules for it, checked against the `go.sum` xark carries. `XARK_GNARK=<path>`
names a helper built ahead of time (`go build` in `crates/cli/gnark/`), for a
machine without Go or the network; one built from another version of xark is
refused. With neither a cache directory nor `XARK_GNARK` there is nowhere safe to
build it, and xark says so.

## What is written where

```text
<keys>/gnark/                 # xark setup --backend gnark
  circuit.r1cs                # the keyed rows, iden3 format
  circuit.ccs                 # the same rows as a gnark constraint system
  pk.bin  vk.bin              # gnark's proving and verifying keys
  metadata.json
target/xark/<name>/gnark/     # xark prove --backend gnark
  witness.wtns                # the solved witness, iden3 format (see below)
  proof.bin                   # gnark's proof
  public_witness.bin          # gnark's public witness
```

`<keys>` is where xark's own keys go: `keys/<name>/` in a project, otherwise
`target/xark/<name>/`. A key put elsewhere (`xark setup --backend gnark --out
<dir>`) is named as xark's own is: `xark prove --backend gnark --proving-key
<dir>/gnark/pk.bin`, and `xark verify --backend gnark --verifying-key
<dir>/gnark/vk.bin`.

## The witness file

gnark is another process, so the witness reaches it as a file, and the witness is
every private input and everything derived from them. `xark prove --backend gnark`
writes `witness.wtns` readable by you only (on unix) and removes it as soon as
gnark has read it, whether or not a proof came of it; `--keep-witness` leaves it
there, for a gnark program of your own to prove from. The default backend never
writes one.

`xark verify --backend gnark` exits with 2 when gnark's verifier refuses the
proof, as the default backend does, and with 1 when the helper could not run or
read its files: a missing Go is not a proof that failed.

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
fill a witness from a kept `witness.wtns` (`readWitness` in
`crates/cli/gnark/main.go` is sixty lines).

## The two files without gnark

The files are not gnark's: snarkjs and rapidsnark read them too. `xark export
--format iden3` writes `circuit.r1cs`, and with `--inputs` the `witness.wtns`
those inputs solve to, into `target/xark/<name>/iden3/` (or `--out`), with no Go
involved:

```sh
xark export --format iden3 --inputs '{"secret": 3, "result": 27}'
```

The rows are the ones a key over a 2^k domain is made for, and `--r1cs-form`
chooses them as it does for `xark setup`. xark has tested the files against gnark
only; a witness written this way stays where you put it.

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
