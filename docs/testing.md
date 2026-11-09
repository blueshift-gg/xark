# Testing a circuit

A circuit is a Rust crate, and you test it with `cargo test`: `xark test` builds
the circuit, then runs the crate's tests.

`#[circuit]` also generates a validator under the circuit's name for tests and
host code: the same parameters, each taking whatever converts to it. A `Field`
takes an integer, a decimal or `0x`-hex string, or an `ark_bn254::Fr`; a
gadget's input types take their natural form, such as an Ed25519 public key's
32 bytes or a Grumpkin point's `(x, y)`.

```rust
#[test]
fn accepts_a_cube_root() {
    cube(3, 27).unwrap();
    assert!(cube(3, 28).is_err());
}
```

Inputs that fail a check are reported as the statement that fails, in tests, in
`xark prove` and in the TypeScript client alike:

```text
error: witness does not satisfy the circuit

  src/lib.rs:96:20  id.nationality.require_in(policy.allowed);
```

Every build writes `sources.json` beside `circuit.xbc` for this: which source
line each constraint came from (the circuit itself is unchanged by it).

Circuit code also runs as plain Rust on the host: `Field` arithmetic,
comparisons, hints and whole gadgets compute their values, and a failed
`require` panics at its line. So tests and services call the same helpers the
circuit does. `zkyc`'s tests make the issuer's commitment with
`id.commitment()`, the very function the circuit checks it with, and
`pubkey.verify(sig, digest)` checks an ECDSA signature off-circuit. (Calling the
`#[circuit]` fn itself still checks the circuit through the prover.)

`xark test <crate>` passes its arguments after `--` on to `cargo test`, such as
`xark test my-circuit -- --nocapture`.
