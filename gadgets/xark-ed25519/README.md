# xark-ed25519

[![crates.io](https://img.shields.io/crates/v/xark-ed25519.svg)](https://crates.io/crates/xark-ed25519)
[![docs.rs](https://img.shields.io/docsrs/xark-ed25519)](https://docs.rs/xark-ed25519)

Ed25519 (EdDSA) signature verification for xark circuits, the signature scheme
Solana keys use. The example's tests verify real signatures from the
`ed25519-dalek` crate.

```toml
[dependencies]
xark = "0.3"
xark-ed25519 = "0.3"
```

## Use

```rust
use xark_ed25519::prelude::*;

#[circuit]
pub fn ed25519(pubkey: Public<PointL>, sig: Public<Signature>, digest: Public<Scalar>) {
    pubkey.verify(sig, digest);
}
```

On the host, `pubkey` is the 32-byte compressed public key, `sig` is 64 bytes:
the compressed `R`, then `S` **big-endian**, and `digest` is the challenge
`k = SHA-512(R ‖ A ‖ M) mod L`. The host helpers build these from an `ed25519-dalek`
signature:

```rust
use xark_ed25519::{challenge, scalar_le_to_be};

let pubkey = sk.verifying_key().to_bytes();
let raw = sk.sign(MSG).to_bytes(); // R(32) ‖ S(32, little-endian)
let mut sig = [0u8; 64];
sig[..32].copy_from_slice(&raw[..32]); // compressed R
sig[32..].copy_from_slice(&scalar_le_to_be(&raw[32..].try_into().unwrap())); // S big-endian

let r: [u8; 32] = sig[..32].try_into().unwrap();
let k = challenge(&r, &pubkey, MSG);
ed25519(pubkey, sig, k).unwrap();
```

See [`examples/ed25519`](https://github.com/blueshift-gg/xark/tree/master/examples/ed25519).

## API

| Item | What it does |
|---|---|
| `PointL::verify(self, sig, digest)` | Verify an Ed25519 signature against this public key, given the challenge `k`. |
| `PointL`, `Signature`, `Scalar` | The circuit inputs: a public key (32 bytes compressed on the host), `(R, S)`, and a scalar mod `L`. |
| `challenge(r, a, msg)` | Host only: `k = SHA-512(R ‖ A ‖ M) mod L`, big-endian. |
| `scalar_le_to_be(le)` | Host only: turn a standard little-endian `S` into the big-endian form `Signature` takes. |
| `point_be`, `base_be`, `base_mul_be` | Host only: decompress a point; the base point `B`; `[k]·B`. |
| `base()`, `mul_base(k_bits)` | In circuit: the base point and fixed-base scalar multiplication on the 3×86-bit `Point`. |

## Notes

- The circuit checks the cofactored equation `[8]·([S]·B − [k]·A − R) = O`, with
  `A` and `R` canonical and on the curve, and `S < L`. Being cofactored, it accepts
  small-order `A` and `R` (as ZIP-215 does): a signature by a small-order key, or
  with a small-order component added to `R`, verifies.
- The SHA-512 challenge is **not** computed in the circuit. The prover supplies
  `k`. If `k` is public, the verifier can recompute it from `R`, `A` and the
  message to tie the proof to that message.

## Cost

- One signature verification: 396,912 constraints
  ([`examples/ed25519`](https://github.com/blueshift-gg/xark/tree/master/examples/ed25519)).

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
