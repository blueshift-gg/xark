# xark-grumpkin

[![crates.io](https://img.shields.io/crates/v/xark-grumpkin.svg)](https://crates.io/crates/xark-grumpkin)
[![docs.rs](https://img.shields.io/docsrs/xark-grumpkin)](https://docs.rs/xark-grumpkin)

Grumpkin curve arithmetic for xark circuits. Grumpkin (`y² = x³ − 17`) and BN254
form a cycle: Grumpkin's coordinates are BN254 field elements, the circuit's own
field, so point addition and scalar multiplication are a few native constraints
each. Use it to verify the group side of recursion and folding schemes (IPA
accumulators, Nova instances) inside a BN254 proof. The tests check it against
`ark-grumpkin`.

```toml
[dependencies]
xark = "0.3"
xark-grumpkin = "0.3"
```

## Use

```rust
use xark_grumpkin::prelude::*;

#[circuit]
pub fn grumpkin(
    s0: Public<Field>,
    s1: Public<Field>,
    p0: Public<Affine>,
    p1: Public<Affine>,
    r: Public<Affine>,
) {
    let out = multi_scalar_mul([s0, s1], [[p0.x, p0.y], [p1.x, p1.y]]);
    require_eq(out[0], r.x);
    require_eq(out[1], r.y);
}
```

This checks `r = s0·p0 + s1·p1` for 128-bit scalars. See
[`examples/grumpkin`](https://github.com/blueshift-gg/xark/tree/master/examples/grumpkin),
and [`examples/grumpkin_ipa`](https://github.com/blueshift-gg/xark/tree/master/examples/grumpkin_ipa)
for full-width scalars with `wide_scalar_mul`.

## API

| Item | What it does |
|---|---|
| `ec_add(p, q)`, `ec_double(p)` | Incomplete affine addition (`p ≠ ±q`) and doubling. |
| `scalar_mul(bits, p)` | `m·p` for a 128-bit scalar given as little-endian bits; `p` is a witness point. |
| `multi_scalar_mul(scalars, points)` | `s₀·P₀ + s₁·P₁` for two 128-bit scalars. |
| `wide_scalar_mul(s, p)` | `s·p` for a full-width (254-bit) `WideScalar`. |
| `decompose(x)` | `x` as 128 little-endian bits, constrained. |
| `enforce_on_curve(p)` | Assert `p` is on Grumpkin. |
| `Affine`, `WideScalar`, `Instance` | Circuit inputs: a point; a scalar as two 127-bit limbs; a committed relaxed-R1CS (Nova) instance. |
| `N_BITS`, `K` | Scalar bit length (128) and the number of pairs in `multi_scalar_mul` (2). |

## Notes

- The scalar multiplications reject a result at infinity (for example a zero
  scalar), and `multi_scalar_mul` rejects `P₀ = ±P₁`. A prover can't forge a
  result at these edges; an honest prover with such inputs can't prove.
- Grumpkin's scalar field is not the circuit's field, so arithmetic on scalars
  (such as Fiat–Shamir challenges) can't be done soundly here. Scalars enter as
  inputs.

## Cost

- `multi_scalar_mul` of two 128-bit scalars, checked against a public point:
  1,569 constraints ([`examples/grumpkin`](https://github.com/blueshift-gg/xark/tree/master/examples/grumpkin)).
- Four full-width `wide_scalar_mul`s summed with three `ec_add`s: 8,188
  constraints ([`examples/grumpkin_ipa`](https://github.com/blueshift-gg/xark/tree/master/examples/grumpkin_ipa)).

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
