# The circuit Rust subset

xark compiles a **restricted subset** of Rust to an arithmetic circuit. You write ordinary Rust and
`rustc` type-checks it, but only constructs with a well-defined *fixed arithmetic* meaning are
accepted — everything else is rejected at build time with a diagnostic (pointing at the source line).
This page is the reference for what's in the subset, and *why* common patterns are rejected.

## The mental model

A circuit is a **fixed system of arithmetic constraints over a finite field**. xark builds it by
compiling your crate to wasm with any stable `rustc` and *running* it with every witness value kept
symbolic: constants, loop counters and indices simply execute (that is the unrolling and inlining),
and every operation on a witness becomes constraints. Rule of thumb:

> **Everything that decides the *shape* of the circuit — loop lengths, array sizes, which memory is
> touched — must be known at compile time, or provably take only a few values. Witness *values* may
> flow anywhere, including into `if`s.**

`Field` is the field element type (BN254 scalar). `Private<Field>`/`Public<Field>` mark input
visibility. `require_eq(a, b)` emits an equality **constraint**.

```rust
use xark::prelude::*;

/// Prove knowledge of a cube root: `secret^3 == result`.
#[circuit]
pub fn cube(secret: Private<Field>, result: Public<Field>) {
    require_eq(secret.pow(3), result);
}
```

## Supported

- **Types:** `Field`; native `u8`..`u128`; fixed-size arrays (nested too); tuples and structs of
  these. Circuit inputs must be built from `Field` and `uN` with **constant** array lengths; each
  `uN` input is range-checked `< 2^N` on entry, and each `[u8; N]` `#[circuit]` parameter byte-wise.
  A parameter is any `xark::Input` type: these, `#[input]` structs of them, the standard
  types (`Date`, `Text`, `Choice<E>`, `Bitfield<E>`) and gadget types.
- **`Field` arithmetic:** `+`, `-`, `*`, `/`, unary `-`, compound assignment (`+=`, …), `.pow(n)`
  (exponentiation by a **constant** `n`). `^` is boolean XOR (`.xor()`), not a power.
  Multiplication by a constant is free (folds into a linear combination); only `var * var` emits a
  gate. `a == b` / `a != b` give a circuit `bool` (`Field::from(b)` turns it back into a `{0,1}`
  field value).
- **Native `uN` witnesses:** comparisons (signed too), wrapping and checked `+ - *`, `/` and `%`
  (by a witness too), bitwise ops, shifts (by a witness amount too), and `as` casts — widening is
  free, narrowing truncates (a range-checked gadget), as in Rust.
- **Control flow:** `if`/`match` on anything — see [Branches on witness values](#branches-on-witness-values);
  loops with a constant bound, or a witness bound small enough that the loop provably ends (e.g.
  `0..(x & 3)`); iterators and adapters over arrays and constant ranges; `assert!` and overflow /
  bounds checks on witnesses (each becomes a constraint).
- **Memory:** `&mut` borrows, slices, `copy_from_slice`, nested-array rows. An index or pointer
  that depends on a witness works when it can take at most 1024 values (`t[(x & 7) as usize]`,
  `t[x as u8 as usize]`, a `match` lookup table): it becomes a select over every possible slot.
- **Functions:** ordinary calls, including across crates — **gadgets are just Rust libraries**
  (`xark-sha256`, `xark-bits`, …) — plus generics, trait objects, function pointers and recursion,
  as long as the call target and depth don't depend on a witness.
- **Bit / integer gadgets:** `Field::to_bits::<N>()` / `from_bits::<N>()`, comparisons, and the gadget
  crates, all with **constant** widths.

## Branches on witness values

An `if` (or `match`) whose condition depends on a witness runs **both** arms and selects the
results. What an arm *requires* only binds when that arm is taken:

- A requirement inside an arm (`require_eq`, `assert!`, checked arithmetic, a range proof) is
  emitted as `g · (a − b) = 0`, where `g` is `1` exactly when the arm is taken. In the untaken arm
  it is vacuous — so a check you need unconditionally belongs *before* the `if`.
- An arm that can only panic (an `assert!` that fails, `/ 0`, an out-of-bounds index) is treated as
  impossible: the circuit requires the condition to go the other way. If both arms panic, the
  inputs are rejected.
- Hints inside an arm see `0` where the arm isn't taken and are pinned to `0` there, so every
  variable stays determined by the inputs.
- A loop whose exit depends on a witness and isn't provably short is refused at build time ("a loop
  whose exit depends on a witness value can't be unrolled" / "… nest too deeply").

`crates/frontend/README.md` has the details; the Lean side is `gated_sat`, `guard_mul`, `pin_dead`
and `select_taken` in `formal/Formal/Rewrites.lean`.

## Not supported — and what to do instead

| You wrote | Why it's rejected | Do this instead |
|---|---|---|
| `while i < n` / `for i in 0..n` with `n` an unbounded witness | the loop length would depend on the witness | bound it with a constant (`for i in 0..MAX { if i < n { … } }`) |
| `arr[i]` with `i` a wide witness (a `u32`, a `Field`) | a select over more than 1024 slots | narrow the index (`(i & 7) as usize`), or mux by hand |
| `let n = read_len(); [Field; n]` | array length must be constant | use a `const` / const-generic `N` |
| calling through a fn pointer / trait object chosen by a witness | the call target would depend on the witness | branch on the witness and call each function directly |
| `x as u8` on a `Field` | `Field` isn't a primitive integer | `Field::to_bits::<N>()` and recombine, or keep values as `uN` |
| `memory.grow` / a memory fill or copy whose size depends on a witness | the memory layout would depend on the witness | use fixed-size buffers |
| `f32` / `f64` arithmetic on a witness | floats only run on constants (compile-time evaluation) | fixed-point integers or `Field` |

If you hit a rejection not covered here, the diagnostic names the exact construct and source line —
that message is the source of truth.

## Why `Field` doesn't implement `Ord`

`Field` values have no natural order (they are residues mod p), so `<` needs an explicit width:
`a.lt::<N>(b)` and friends range-check both sides to `N` bits first (`N ≤ 252`, so `2^(N+1)` stays
under the field order). `==` needs no width, so `Field` implements `PartialEq` directly. This keeps
every operation's circuit meaning unambiguous.

## Testing a circuit

Circuit crates are tested with **`xark test`**: it builds the `target/xark/` artifacts first, then
runs the crate's tests, which load the built circuit and check the witness solves. Bare `cargo test`
also works: a test whose circuit is missing, or older than any source it was built from (the
crate's `src/` and `Cargo.toml`, and its path dependencies, gadget crates included), rebuilds it
with the `xark` on `PATH` (`$XARK` if set) first. A `#[circuit]`-style test expecting failure asserts the solve is `Err`. Run `xark build` then
`xark prove <dir> --inputs '{"x": "42", …}'` to prove end-to-end; `--inputs` takes inline JSON or a
file (a JSON object, or `name = value` lines), with array elements under their flat names (`path[0]`).

See also: [architecture.md](architecture.md) (compile pipeline),
[integer-ops.md](integer-ops.md) (bit/integer gadget layer).
