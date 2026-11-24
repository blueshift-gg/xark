# Proving a xark circuit with another prover

`xark export --format iden3` writes a circuit in iden3's two files, the formats
circom writes and snarkjs and rapidsnark read. The circuit is still written in
Rust and compiled by xark, and xark still solves the witness; the Groth16 setup,
proof and verification are the other prover's. `xark setup`, `xark prove` and
`xark verify` are unchanged, and nothing here needs anything but xark.

```sh
xark export --format iden3 --inputs '{"secret": 3, "result": 27}'
```

```text
target/xark/<name>/iden3/     # or --out
  circuit.r1cs                # the keyed rows
  witness.wtns                # with --inputs: the solved witness
```

## The two files

- `circuit.r1cs`
  ([format](https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md))
  holds the rows a key is made for: the same rows a xark key over a 2^k domain
  gets, and `--r1cs-form` chooses them as it does for `xark setup`. Wire 0 is the
  constant one, the public inputs follow in declaration order, and every other
  variable comes after. The header's private-input count is zero: xark's layout
  doesn't tell a private input from a derived variable, and no Groth16 setup reads
  it.
- `witness.wtns` holds the value of every wire for one set of inputs, so the
  other prover has nothing to compute: xark's solver has run.

The witness is every private input and everything derived from them. It is
written readable by you only (on unix) and stays where you put it: remove it when
the proof is made. `xark prove` never writes one.

## What reads them

- **snarkjs and rapidsnark** take the two files as they are (`snarkjs groth16
  setup circuit.r1cs …`, `snarkjs groth16 prove … witness.wtns`).
- **gnark** has no reader for them. [`benches/gnark/go/iden3/main.go`](../benches/gnark/go/iden3/main.go)
  has one, some 230 lines of it: `readR1CS` turns the rows into a gnark
  `constraint.R1CS`, every xark variable a gnark input wire (public or secret) and
  none an internal one, and `readWitness` fills a gnark witness. The constraint
  count is exactly xark's.

What is tested: xark reads its own files back and checks every row against the
witness (`gadgets/tests/tests/it/iden3.rs`), and gnark sets up, proves and
verifies from them for six circuits (`benches/gnark/run.sh`, in slow.yml). They
have not been run through snarkjs or rapidsnark.

## What it does not do

- The keys and proofs are the other prover's, not xark's: `xark verify`, `xark
  export` (the Solana verifier) and `xark client` take xark's own. A setup made
  by one machine with another tool is as trusted as `xark setup` without a
  `.ptau`.
- The rows are for a 2^k domain, the only one these provers have. xark's own
  keys default to a smooth domain where that makes the proof faster (`xark setup
  --domain`); that choice stays with xark's prover and doesn't reach the export.
- BN254 only, as the rest of the proving toolchain.

## How the provers compare

[`benches/gnark/`](../benches/gnark/README.md) proves the same functions with
arkworks, xark's prover and gnark, and beside a circuit written directly in
gnark.
