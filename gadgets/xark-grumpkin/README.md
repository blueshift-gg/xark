# xark-grumpkin

[![crates.io](https://img.shields.io/crates/v/xark-grumpkin.svg)](https://crates.io/crates/xark-grumpkin)
[![docs.rs](https://img.shields.io/docsrs/xark-grumpkin)](https://docs.rs/xark-grumpkin)

Grumpkin curve arithmetic for xark circuits. Grumpkin (`y² = x³ − 17`) and BN254
form a cycle: Grumpkin's coordinates are BN254 field elements, the circuit's own
field, so point addition and scalar multiplication are a few native constraints
each. Use it to verify the group side of recursion and folding schemes (IPA
accumulators, Nova instances) inside a BN254 proof, or a Schnorr signature for about
5,000 constraints (an Ed25519 signature costs ~397,000). The tests check it against
`ark-grumpkin`.

```toml
[dependencies]
xark = "0.4"
xark-grumpkin = "0.4"
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

## Schnorr signatures

```rust
use xark_grumpkin::prelude::*;
use xark_grumpkin::schnorr::{self, Signature};

#[circuit]
pub fn authorised(pubkey: Public<Affine>, msg: Public<[Field; 2]>, sig: Private<Signature>) {
    schnorr::verify(pubkey, sig, msg);
}
```

`verify` checks `s·G = R + e·P` for the key `P`, the signature `(R, s)` and the
challenge `e = Poseidon2(R.x, R.y, P.x, P.y, msg…)`, a sponge whose capacity is seeded
with the tag `"grumpkin-schnorr"·2⁶⁴ + (4 + N)`, so a challenge is never a plain
`xark_poseidon2::hash` of the same elements. `R` and `P` must be on the curve (Grumpkin
has cofactor 1, so that is the whole subgroup check) and `s` below the group order
`n`, so a signature has one encoding. The digest is a field element below `r < n`, and
the challenge is that integer, unreduced; its 127-bit limbs are pinned to it and below
`r`, so the prover can't pick `e + r` instead. See
[`examples/grumpkin_schnorr`](https://github.com/blueshift-gg/xark/tree/master/examples/grumpkin_schnorr).

On the host, `schnorr::host` signs and verifies with `ark-grumpkin`:

```rust
use xark_grumpkin::schnorr::host::{Base, SigningKey};

let sk = SigningKey::from_seed(&seed).unwrap(); // or from_scalar
let sig = sk.sign(&[Base::from(1u64), Base::from(2u64)]);
// `#[circuit]`'s inputs struct for the circuit above:
let inputs = AuthorisedInputs {
    pubkey: sk.public_key().into(),
    msg: [1u64.into(), 2u64.into()],
    sig: sig.into(),
};
```

The nonce is deterministic: two lanes of a Poseidon2 sponge (tag
`"grumpkin-schnorr-nonce"`) over the secret, the key and the message, reduced mod
`n` from `[0, r²)`. [`schnorr_ref.py`](schnorr_ref.py) recomputes the tests' known
answer in plain Python.

## API

| Item | What it does |
|---|---|
| `ec_add(p, q)`, `ec_double(p)` | Incomplete affine addition (`p ≠ ±q`) and doubling. |
| `scalar_mul(bits, p)` | `m·p` for a 128-bit scalar given as little-endian bits; `p` is a witness point. |
| `multi_scalar_mul(scalars, points)` | `s₀·P₀ + s₁·P₁` for two 128-bit scalars. |
| `wide_scalar_mul(s, p)` | `s·p` for a full-width (254-bit) `WideScalar`. |
| `decompose(x)` | `x` as 128 little-endian bits, constrained. |
| `enforce_on_curve(p)` | Assert `p` is on Grumpkin. |
| `schnorr::verify(pubkey, sig, msg)` | Require a Schnorr signature `sig` on `msg: [Field; N]` (above). |
| `schnorr::challenge(r, pubkey, msg)` | Its challenge `e`, a field element. |
| `schnorr::host` | `SigningKey` (`from_seed`, `from_scalar`, `public_key`, `sign`), `verify`, `challenge`; not in a circuit build. |
| `Affine`, `WideScalar`, `Instance` | Circuit inputs: a point; a scalar as two 127-bit limbs; a committed relaxed-R1CS (Nova) instance. |
| `N_BITS`, `K` | Scalar bit length (128) and the number of pairs in `multi_scalar_mul` (2). |

## Notes

- The scalar multiplications reject a result at infinity (for example a zero
  scalar), and `multi_scalar_mul` rejects `P₀ = ±P₁`. A prover can't forge a
  result at these edges; an honest prover with such inputs can't prove.
- Grumpkin's scalar field is not the circuit's field, so arithmetic on scalars
  (such as products of Fiat–Shamir challenges) can't be done soundly here. Scalars
  enter as inputs; a challenge can be used as a scalar only as the integer it is,
  as `schnorr::verify` does.

## Cost

- `multi_scalar_mul` of two 128-bit scalars, checked against a public point:
  1,569 constraints ([`examples/grumpkin`](https://github.com/blueshift-gg/xark/tree/master/examples/grumpkin)).
- `schnorr::verify` on a two-element message: 5,051 constraints
  ([`examples/grumpkin_schnorr`](https://github.com/blueshift-gg/xark/tree/master/examples/grumpkin_schnorr)).
- Four full-width `wide_scalar_mul`s summed with three `ec_add`s: 8,188
  constraints ([`examples/grumpkin_ipa`](https://github.com/blueshift-gg/xark/tree/master/examples/grumpkin_ipa)).

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
