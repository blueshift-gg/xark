# xark-aes

[![crates.io](https://img.shields.io/crates/v/xark-aes.svg)](https://crates.io/crates/xark-aes)
[![docs.rs](https://img.shields.io/docsrs/xark-aes)](https://docs.rs/xark-aes)

AES-128 and AES-256 for xark circuits: the block cipher, CTR mode, and
authenticated GCM. Use it to prove a ciphertext encrypts a plaintext you know,
under a key you keep private. The block cipher is checked against the FIPS-197
known answers and GHASH against the `ghash` crate; the examples check CTR and GCM
against the `aes` and `aes-gcm` crates.

```toml
[dependencies]
xark = "0.3"
xark-aes = "0.3"
```

## Use

AES-128-GCM with 13 bytes of associated data, from
[`examples/aes_gcm`](https://github.com/blueshift-gg/xark/tree/master/examples/aes_gcm):

```rust
use xark_aes::prelude::*;

#[circuit]
pub fn aes_gcm(
    aad: Public<[u8; 13]>, // e.g. a record header — authenticated, not secret
    pt: Private<[u8; 20]>,
    key: Private<[u8; 16]>,
    nonce: Private<[u8; 12]>,
    ct: Public<[u8; 20]>,
    tag: Public<[u8; 16]>,
) {
    let (c, t) = aes128_gcm::<13, 20>(aad, pt, key, nonce);
    require_eq(c, ct);
    require_eq(t, tag);
}
```

A single block is one call:
`aes128_constrain(pt, key, ct)` ([`examples/aes`](https://github.com/blueshift-gg/xark/tree/master/examples/aes)).

## API

| Item | What it does |
|---|---|
| `aes128_gcm::<A, N>(aad, pt, key, nonce)`, `aes256_gcm` | GCM (NIST SP 800-38D) with `A` bytes of AAD and a 96-bit nonce. Returns `(ciphertext, tag)`. |
| `aes128_ctr::<N>(msg, key, nonce)`, `aes256_ctr` | CTR mode: keystream block `b` is `AES(key, nonce ‖ be_u32(b))`, counter from 0. |
| `aes128_encrypt_bytes(pt, key)`, `aes256_encrypt_bytes` | Encrypt one 16-byte block; inputs are bytes, range-checked. |
| `aes128_constrain(pt, key, ct)`, `aes256_constrain` | Encrypt one block and require it equal `ct`. |
| `aes128_encrypt`, `aes256_encrypt` | One block on bytes already split into bits (`[Field; 8]` each). |
| `gf128_mul`, `bytes_to_gf128`, `gf128_to_bytes` | The GCM field multiply and its bit-order conversions. |
| `sbox` | The AES S-box on one byte's bits. |
| `key_schedule_byte` | One byte of the expanded AES-128 key (for tests). |

All modes only encrypt; CTR and GCM decryption is the same operation. The
lengths `A` and `N` are compile-time constants.

## Cost

| Circuit | Constraints |
|---|---|
| AES-128, one block ([`aes`](https://github.com/blueshift-gg/xark/tree/master/examples/aes)) | 15,360 |
| AES-128-CTR, 20 bytes ([`aes_ctr`](https://github.com/blueshift-gg/xark/tree/master/examples/aes_ctr)) | 30,185 |
| AES-256-CTR, 20 bytes ([`aes256_ctr`](https://github.com/blueshift-gg/xark/tree/master/examples/aes256_ctr)) | 42,273 |
| AES-128-GCM, 20 bytes + 13 bytes AAD ([`aes_gcm`](https://github.com/blueshift-gg/xark/tree/master/examples/aes_gcm)) | 185,971 |
| AES-256-GCM, 20 bytes + 13 bytes AAD ([`aes256_gcm`](https://github.com/blueshift-gg/xark/tree/master/examples/aes256_gcm)) | 209,883 |

Most of GCM's cost is GHASH: each 16-byte block of AAD and ciphertext, and the
length block, is one `gf128_mul`.

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
