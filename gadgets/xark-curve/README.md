# xark-curve

[![crates.io](https://img.shields.io/crates/v/xark-curve.svg)](https://crates.io/crates/xark-curve)
[![docs.rs](https://img.shields.io/docsrs/xark-curve)](https://docs.rs/xark-curve)

Macros that emit an elliptic-curve gadget for a curve over a non-native field,
for writing xark gadgets. Each curve is one macro call with its constants;
`xark-secp256k1`, `xark-secp256r1` and `xark-ed25519` are built this way. If you
want signature verification, use those crates instead.

```toml
[dependencies]
xark = "0.3"
xark-bignum = "0.3"
xark-curve = "0.3"
```

The emitted code refers to `xark_bignum::…` and `xark::…`, so the crate that
calls a macro must depend on both.

## Use

From `xark-ed25519`'s `src/lib.rs`:

```rust
xark_curve::edwards! {
    base   = "57896044618658097711785492504343953926634992332820282019728792003956564819949",
    scalar = "7237005577332262213973186563042994240857116359379907606001950938285454250989",
    d      = "37095705934669439343138083508754565189542113879843219016388785533085940283555",
}
```

`weierstrass!` takes the base and scalar moduli, `a` (`0` or `-3`), `b`, four
generator points and an offset correction; see the `affine` modules of
`xark-secp256k1` and `xark-secp256r1`.

## What's in it

| Macro | What it emits |
|---|---|
| `weierstrass!` | A short-Weierstrass curve gadget: `Fp`, `Fq`, `Point`, `enforce_on_curve`, incomplete affine `ec_add_incomplete` / `ec_double_incomplete`, and Strauss–Shamir `double_scalar_mul_incomplete` (`u1·G + u2·Q`). |
| `edwards!` | A twisted-Edwards (`a = −1`) curve gadget: `Fp`, `Fq`, `Point`, `enforce_on_curve`, complete `ec_add` / `ec_double`, `identity`, `scalar_mul` and `double_scalar_mul`. |
| `curve_host_inputs!` | The host side shared by both: `Point` from `x ‖ y` bytes (or SEC1 with `0x04`), and `order()` / `reduce_scalar()`. Needs a host-only `num-bigint` dependency. |

Field elements are 3 limbs of 86 bits. `weierstrass!` takes an optional leading
`bits = N` to pick another limb width.

## Notes

- The Weierstrass addition is incomplete: inputs must be canonical and not hit
  `P = ±Q`. Check points from outside with `enforce_on_curve` first.
- The Edwards addition is complete (no exceptional cases) when `d` is a
  non-square, as it is for Ed25519.

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
