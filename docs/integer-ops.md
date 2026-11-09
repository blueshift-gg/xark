# Integer operations on `Field`

How `Field` supports integer-flavoured operations (equality, ordering, shifts, modulus) in a
circuit, and why the surface is shaped this way.

Integers beyond this surface are native Rust integers, not `Field` methods: a circuit takes `u8`..`u128`,
`i8`..`i128` and `bool` inputs (range-checked on entry), and native integer code on witnesses
(signed comparisons, checked and wrapping `+ - *`, `/`, `%`, shifts, casts) lowers to range-checked
gadgets. See [the supported subset](subset.md#supported).

## The core problem: a `Field` has no width

A `Field` is a residue in `[0, p)` for the BN254 scalar field (`p ≈ 2²⁵⁴`), **not** a fixed-width
integer: no MSB, so `<<`/`>>` have no intrinsic meaning; ordering mod `p` isn't integer ordering
unless you fix a range. So every integer op needs a **bit-width** `N`, **enforced with a range
check**; otherwise a malicious prover can place any residue in a wire and defeat an unchecked
comparison or shift. The width is never implicit. It comes **from the concrete integer already in
the expression.**

## Design principles

1. **Width comes from a native-int operand.** `x < 100u32`, `x >> 3u16`, `x % 8u8`: the right-hand
   side's *type* supplies the domain width of `x`, its *value* the bound, amount or modulus. No new
   types, no hidden defaults.
2. **Cost stays visible.** The width (and its range-check cost) is spelled at the call site: the
   literal's type (`…u32`) or an explicit `::<N>` for the `Field`-vs-`Field` case. No global default
   width hides the ~`N`-constraint cost behind a clean `a < b`.
3. **Decomposition is cached, not repeated.** A value bounded once is shifted, compared or masked at
   the same width for free afterwards (see [Bit caching](#bit-caching)).
4. **Bare `Field` stays orderless and shiftless.** `PartialOrd`, `Shl` and `Rem` between two `Field`s
   (no width) are **not** provided: they'd be unsound by omission of a width. `<`, `>>` and `%` exist
   only against a native-int right-hand side, or through an explicit-width method.

## The surface

Let `T ∈ { bool, u8, u16, u32, u64, u128 }` and `N = bitwidth(T)` (`bool → 1`, …, `u128 → 128`).
Every op interprets its `Field` operand `x` as an `N`-bit value: it range-checks `x < 2ᴺ` by
`to_bits::<N>(x)`, then does the bit-level op.

| Trait impl (for `Field`) | Enables | Meaning |
|---|---|---|
| `PartialEq<T>` | `x == c`, `x != c` | equality with `c` (no range check) |
| `PartialOrd<T>` | `x < c`, `<=`, `>`, `>=` | `N`-bit ordering against `c` |
| `Shl<T>` (`u8..u128`) | `x << n` | `(x mod 2ᴺ) << n`, truncated to `N` bits |
| `Shr<T>` (`u8..u128`) | `x >> n` | `(x mod 2ᴺ) >> n` = `⌊x / 2ⁿ⌋` |
| `Rem<T>` (`u8..u64` only) | `x % m` | `x mod m` |

`PartialEq<i32>` also exists, so `x == 0` works with an untyped literal: equality needs no width.
An ordered comparison does, so write `x < 5u32`, not `x < 5`.

`Shl`/`Shr` cover `u8..u128`: a shift is pure bit re-wiring, and `from_bits::<N>` with
`N ≤ 128 ≤ 253` can't wrap the field. **`Rem` is `u8..u64` only:** its general-modulus path pins a
`hint_div_rem` witness `[q, r]` with `m·q + r == x`, sound only while `m·q + r` can't wrap the field,
i.e. `2·N ≤ 253`. `u8..u64` satisfy this (`2·N ≤ 128`); `u128` (`2·N = 256 > 253`) does not, so
`x % 5u128` doesn't compile. Use a `u64`-or-narrower modulus.

There are no `Field` impls against signed `i8..i128` operands: signed values are native `iN`
witnesses, whose comparisons the frontend lowers itself.

### `Field`-vs-`Field`

Comparing two *witness* values has no integer operand to carry a width, so it takes an **explicit
const-generic method**:

```rust
a.lt::<32>(b)   a.gt::<32>(b)   a.le::<32>(b)   a.ge::<32>(b)   // -> bool wire
```

The `::<32>` keeps its cost honest. There is intentionally **no** `PartialOrd` between two `Field`s
for this; see principle 4.

`require_lt`, `require_le`, `require_gt` and `require_ge` are generic over `PartialOrd`, so they work
against a native-int right-hand side (`require_lt(x, 100u32)`) and on native integers.

## Semantics and constraint cost (per op, width `N`)

All ops first obtain `bits = to_bits::<N>(x)`: `N` rows (`N − 1` booleanity rows and one
`b₀(b₀ − 1) = 0` for the bit computed from the others), **once per `(x, N)`**. Then:

* **`x == c` / `x != c`**: a bare equality needs no bits, only an is-zero on `x − c`. About 0–2
  constraints.
* **`x < c` (constant right-hand side)**: compares `bits` against the compile-time `c`, with no
  second decomposition: cheaper than a `Field`-vs-`Field` compare. `>`, `<=` and `>=` derive from
  `<` and `==`.
* **`x >> n`**: the high `N − n` bits, recomposed. The shift is free re-wiring; the cost is the
  shared `to_bits::<N>`.
* **`x << n`**: bits `0..N−n` placed at `n..N`, the low bits zero. Free re-wiring. It **truncates** at
  `2ᴺ` (integer `<<`), not `x·2ⁿ mod p`.
* **`x % m`** (`u8..u64` only): for `m = 2ᵏ`, the low `k` bits (free). A general `m`: a
  `hint_div_rem` plus range checks (`r < m`, `q < 2ᴺ`), sound because `2·N ≤ 253` keeps `m·q + r`
  from wrapping. Modulus zero takes the general path and is unprovable (not a compile error: `m` is
  a runtime value to rustc).

### Soundness

Each op range-checks `x < 2ᴺ` via `to_bits::<N>`. A prover holding an `x` outside the declared
domain **cannot satisfy** the circuit (the decomposition is unsatisfiable), so no false proof is
possible: the width is a *contract* the author states via the right-hand side's type, enforced in
the circuit. Picking too small an `N` makes valid large values unprovable (a liveness bug the author
sees at once), never an unsound accept.

## Bit caching

The frontend memoizes decompositions (`bit_cache` in `crates/frontend/src/host.rs`). When an op
needs `to_bits::<N>(x)`, it looks up `(canonical(x), N)`, where the key is `x`'s canonical linear
combination (sorted, merged terms): a **miss** decomposes and stores the bits, a **hit** reuses them
and emits no rows. So `x < 100u32; x >> 3u32; x & mask_u32` on the same `x` share **one** 32-bit
decomposition.

* **Soundness:** circuit values are immutable once lowered, so cached bits never go stale; the first
  decomposition already constrained them.
* **Keying:** the key is canonical, so `x`, `x + 0` and `0 + x` hit the same entry.
* **Granularity:** per exact `(x, N)`. A 32-bit request doesn't reuse the low bits of a cached 64-bit
  decomposition.
* **Witness-only regions** don't add to the cache: their bits aren't constrained.
* **Already bits:** when `x` is exactly `Σᵢ<N 2ⁱ·vᵢ` over distinct variables already proven boolean,
  `to_bits::<N>(x)` returns those `vᵢ` with no new rows (`bit_sum_shortcut` in
  `crates/frontend/src/builder.rs`): they are `x`'s decomposition.

This is the automatic form of what `xark-bits` does by hand (threading `[Field; 32]` words).

## Rust wrinkles

* `PartialOrd::partial_cmp` returns `Option<Ordering>`, a native value that only makes sense when
  both sides are compile-time constants. On witnesses a comparison must produce a `{0, 1}` *wire*,
  so the impls call the `__xark_eq` / `__xark_ult::<N>` intrinsics, which the frontend implements as
  circuit operations. The trait impls give the syntax and type-check; the frontend owns the meaning.
* `PartialOrd<u32> for Field` gives `x < c` (`Field` on the left). For `c < x`, write `x > c`.

## What `Field` deliberately doesn't provide

* **`PartialOrd`/`Shl`/`Shr`/`Rem` between two `Field`s**: ill-defined without a width, and a hidden
  default would be a footgun.
* **`Eq`/`Ord`**: a circuit `==` yields a *wire*, not a total relation; these would wrongly suggest a
  `Field` is a valid map key or sortable.
* **`^` as a power**: `^` is boolean XOR (`BitXor<Field>`), as in Rust. It checks that each operand
  is 0 or 1 (free for known bits, one row otherwise), and a constant other than 0 or 1 doesn't build.
  Exponentiation is `.pow(n)`; bitwise XOR of integers is `^` on `uN`.
* **Signed or overflow-checked `Field` arithmetic**: `Field` `+`/`-`/`*` are plain field operations
  with no width. Signed values and checked fixed-width arithmetic are native `iN`/`uN` (an overflow
  panic becomes a constraint; see [the supported subset](subset.md)).

## Constants wider than 128 bits

`Field::from(u8..=u128)` stops at `u128`, Rust's widest integer literal. A full-width constant is
`Field::from("<decimal>")`.
