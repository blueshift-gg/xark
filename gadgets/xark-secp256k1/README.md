# xark-secp256k1

[![crates.io](https://img.shields.io/crates/v/xark-secp256k1.svg)](https://crates.io/crates/xark-secp256k1)
[![docs.rs](https://img.shields.io/docsrs/xark-secp256k1)](https://docs.rs/xark-secp256k1)

ECDSA signature verification on secp256k1 (the Bitcoin and Ethereum curve) for
xark circuits. Use it to prove a message was signed by a key, for example a key
you keep private. The example's tests verify real signatures from the `k256`
crate.

```toml
[dependencies]
xark = "0.3"
xark-secp256k1 = "0.3"
```

## Use

```rust
use xark_secp256k1::prelude::*;

#[circuit]
pub fn secp256k1_ecdsa(pubkey: Public<Point>, sig: Public<Signature>, digest: Public<Scalar>) {
    pubkey.verify(sig, digest);
}
```

On the host, `pubkey` is the 64-byte uncompressed key `x ‖ y` (SEC1 without the
`0x04` tag), `sig` is the 64-byte `r ‖ s`, and `digest` is the 32-byte message
scalar. Make `digest` with `reduce_scalar`:

```rust
let digest = reduce_scalar(&Sha256::digest(msg));
```

See [`examples/secp256k1_ecdsa`](https://github.com/blueshift-gg/xark/tree/master/examples/secp256k1_ecdsa).

## API

| Item | What it does |
|---|---|
| `Point::verify(self, sig, digest)` | Verify an ECDSA signature against this public key. A wrong signature makes the circuit unsatisfiable. |
| `Point`, `Signature`, `Scalar` | The circuit inputs: a public key, `(r, s)`, and a 256-bit scalar. Each 256-bit value is 2 field elements. |
| `reduce_scalar(be)` | Host only: reduce a big-endian integer (a hash) mod the group order `n`, as 32 bytes. |
| `order()` | Host only: the group order `n`. |
| `affine` | A lower-level incomplete-affine curve gadget (`Point`, `ec_add_incomplete`, `ec_double_incomplete`, …), used by [`examples/ec_incomplete`](https://github.com/blueshift-gg/xark/tree/master/examples/ec_incomplete). |

## Notes

- The gadget checks that the public key is on the curve, that `r`, `s` and the
  digest are below `n`, and that `r` and `s` are nonzero.
- The message is not hashed in the circuit: `digest` is `int(hash(msg)) mod n`,
  computed by the caller.
- No public key is refused. A valid signature is refused only if its nonce `k`
  is one of six fixed multiples of the private key (`k ≡ μ·q`; the constants
  `μ` are listed in the source).
- A signature isn't unique: if `(r, s)` verifies, so does `(r, n − s)`, as in any
  ECDSA verifier. Don't use a signature as a nullifier or a "used once" key; if you
  need one form, require low-s yourself (`s ≤ (n − 1)/2`).

## Cost

- One signature verification: 227,168 constraints
  ([`examples/secp256k1_ecdsa`](https://github.com/blueshift-gg/xark/tree/master/examples/secp256k1_ecdsa)).

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
