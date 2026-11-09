# xark-bignum

[![crates.io](https://img.shields.io/crates/v/xark-bignum.svg)](https://crates.io/crates/xark-bignum)
[![docs.rs](https://img.shields.io/docsrs/xark-bignum)](https://docs.rs/xark-bignum)

Non-native ("foreign field") arithmetic for writing xark gadgets: modular
arithmetic over a prime other than the circuit's BN254 field, with numbers split
into limbs. `xark-secp256k1`, `xark-secp256r1` and `xark-ed25519` are built on
it. Use it directly when you need another field or a wide modulus (the limb
buffers go up to 32 limbs of 86 bits, room for RSA-2048).

```toml
[dependencies]
xark = "0.3"
xark-bignum = "0.3"
```

## Use

`fp!` defines a field-element type from its modulus, with `+`, `-`, `*` and unary
`-`:

```rust
use xark::{circuit, require_eq, Field, Private, Public};

// A concrete 256-bit prime field (3 × 86-bit limbs), defined by its modulus alone.
xark_bignum::fp!(El, "41904174945551648470736051755806485464313947085173149");

#[circuit]
pub fn bignum_ops(a: Private<El>, b: Private<El>, out: Public<Field>) {
    let r = a * b + a - b;
    require_eq(r.limbs[0], out);
}
```

On the host each `El` input is one whole number; it is split into limbs for you.
See [`examples/bignum_ops`](https://github.com/blueshift-gg/xark/tree/master/examples/bignum_ops),
[`examples/bignum`](https://github.com/blueshift-gg/xark/tree/master/examples/bignum)
for the generic `Bignum<LIMBS, BITS>` type, and
[`examples/bignum_wide`](https://github.com/blueshift-gg/xark/tree/master/examples/bignum_wide)
for a 24-limb modulus.

## What's in it

| Item | What it does |
|---|---|
| `fp!(Name, "modulus")` | Define a field type with operators and `.inverse()`, `.sub2()`, `.triple()`, `.reduce()`. Defaults to 3 × 86-bit limbs; `fp!(Name, "0x…", 4, 64)` picks another layout. |
| `Bignum<LIMBS, BITS>` | Generic limbed number with `mul`, `add`, `sub`, `neg`, `inverse`, `sub2`, `triple`, `reduce`, `range_check`; the modulus is passed in. |
| `mod_mul`, `mod_add`, `mod_sub`, `mod_neg`, `mod_inverse` | The free functions behind them, on `[Field; LIMBS]`. |
| `mul_divmod` | `(⌊a·b / m⌋, a·b mod m)`, both constrained. |
| `sub2`, `triple_mod`, `reduce_once` | Fused `a − b − c`, `3·v`, and one conditional subtraction. |
| `range_check_limbs`, `require_lt`, `is_lt`, `assert_nonzero_limbs` | Limb range checks and comparisons. |
| `modulus_limbs`, `modulus_minus_1`, `complement` | `const fn`s that turn a modulus string into limb constants. |
| `scalar_to_bits`, `one_hot8`, … | Helpers and curve-specific routines used by the signature gadgets. |

## Notes

- Most operations assume canonical operands (`a, b < m`) with range-checked
  limbs; each function's docs give its precondition.
- `mod_mul` fails to compile for a `(LIMBS, BITS)` whose column products could
  wrap the BN254 field.
- In `xark_bignum::prelude`, `require_lt` is xark's scalar `require_lt`; call the
  limb version as `xark_bignum::require_lt`.

## Cost

| Circuit | Constraints |
|---|---|
| `a * b + a - b` over a 3 × 86-bit field ([`bignum_ops`](https://github.com/blueshift-gg/xark/tree/master/examples/bignum_ops)) | 2,041 |
| `(a · b) mod m`, 3 × 86 bits, constant modulus ([`fp_mul`](https://github.com/blueshift-gg/xark/tree/master/examples/fp_mul)) | 993 |
| `(a · b) mod m`, 3 × 86 bits, public modulus ([`bignum`](https://github.com/blueshift-gg/xark/tree/master/examples/bignum)) | 1,002 |
| `(a · b) mod m`, 24 × 86 bits ([`bignum_wide`](https://github.com/blueshift-gg/xark/tree/master/examples/bignum_wide)) | 9,763 |

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
