# The circuit Rust subset

xark compiles a **restricted subset** of Rust to an arithmetic circuit. You write ordinary Rust and
`rustc` type-checks it, but only constructs with a well-defined *fixed arithmetic* meaning are
accepted — everything else is rejected at build time with a diagnostic (pointing at the source span).
This page is the reference for what's in the subset, and *why* common patterns are rejected.

## The mental model

A circuit is a **fixed system of arithmetic constraints over a finite field**, decided entirely at
compile time. It has no runtime: no value-dependent control flow, no data-dependent memory access,
no I/O. Rule of thumb:

> **Everything that decides the *shape* of the circuit — loop lengths, array indices, branch
> conditions, array sizes — must be a compile-time constant. Only `Field` *values* may depend on the
> inputs.**

`Field` is the field element type (BN254 scalar). `Private<Field>`/`Public<Field>` mark input
visibility. `require_eq(a, b)` emits an equality **constraint** (it does *not* return a native `bool`).

```rust
#![no_std]
use xark::prelude::*;

/// Prove knowledge of a cube root: `secret^3 == result`.
pub fn circuit(secret: Private<Field>, result: Public<Field>) {
    require_eq(secret ^ 3, result);
}
```

## Supported

- **Types:** `Field`; fixed-size arrays `[Field; N]` (nested too); tuples and plain structs of
  `Field`. Circuit inputs must be `Field` or arrays/tuples/structs of `Field`, with **constant**
  array lengths.
- **`Field` arithmetic:** `+`, `-`, `*`, unary `-`, `^ n` (exponentiation by a **constant** `n`).
  Multiplication by a constant is free (folds into a linear combination); only `var * var` emits a gate.
- **Constants & host integers:** integer literals and `usize`/`u*` values for loop bounds, indices,
  widths — as long as compile-time constant.
- **Control flow, compile-time only:** `if cond { … } else { … }` where `cond` is constant; `while i < N`
  / `for i in 0..N` where `N` is constant (loops are fully **unrolled**).
- **Functions:** ordinary function calls, including across crates — **gadgets are just Rust libraries**
  (`xark-sha256`, `xark-bits`, …). They're inlined.
- **Bit / integer gadgets:** `Field::to_bits::<N>()` / `from_bits::<N>()`, comparisons, and the gadget
  crates, all with **constant** widths.

## Not supported — and what to do instead

| You wrote | Why it's rejected | Do this instead |
|---|---|---|
| `a += b`, `a -= b`, `a *= b` | compound assignment on `Field` isn't modeled | `a = a + b` |
| `for x in slice` / iterators | iterator desugaring isn't a circuit operation | `for i in 0..N { let x = arr[i]; }` |
| `while cond` on a `Field`-derived `cond` | witness-dependent control flow — loop length would depend on inputs | make the bound a constant |
| `if secret_field == 0 { … }` | branches can't depend on a witness value | compute both sides and **mux**: `b + cond·(a − b)` with a boolean `cond` |
| `arr[i]` where `i` is a `Field`/input | witness-dependent indexing would leak / can't be lowered | use a constant or loop-counter index; for a data-dependent choice, mux |
| `let n = read_len(); [Field; n]` | array length must be constant | use a `const` / const-generic `N` |
| `&mut x` on a `Field` | a mutable borrow of a `Field` isn't supported | restructure to `x = …` (SSA-style) |
| `foo(a)` via a trait object / fn pointer | indirect / dynamic calls aren't supported | call the function directly (it gets inlined) |
| a function that calls itself | recursion isn't supported (no runtime stack) | unroll to a fixed depth, or use a loop with a constant bound |
| `a == b` expecting a `bool` | `==` would need a native `bool`; a circuit needs a *constraint* | `require_eq(a, b)` |
| `a != b` expecting a `bool` | same reason; inequality is a *constraint*, not a native `bool` | `require_ne(a, b)` (unsatisfiable iff `a == b`) |
| reading a whole inner array out of a nested array (`grid[i]` as a value) | only *scalar* nested access is modeled | rebuild element-by-element: `for j in 0..M { row[j] = grid[i][j]; }` |
| `x as u8` on a `Field` | only compile-time integer casts are supported | keep field values as `Field`; use bit gadgets for byte views |

If you hit a rejection not covered here, the diagnostic names the exact construct and source line —
that message is the source of truth.

## Why `Field` doesn't implement `==` / `Ord`

Native `==`/`<` return a `bool` the host evaluates — but a circuit can't branch on a witness. So
equality is an **`require_eq(a, b)` constraint**, and comparisons are explicit width-bounded gadgets
(`N ≤ 252` so `2^(N+1)` stays under the field order). This keeps every operation's circuit meaning
unambiguous.

## Testing a circuit

Circuit crates are tested with **`xark test`** (not bare `cargo test`): it builds the `target/xark/`
artifacts first, then runs the crate's tests, which load the built circuit and check the witness
solves. A `#[circuit]`-style test expecting failure asserts the solve is `Err`. Run `xark build` then
`xark prove <dir> --input name=value …` to prove end-to-end; `--input` takes a decimal string per
declared input (`--input x=42`, repeated per array element).

See also: [architecture.md](architecture.md) (compile pipeline),
[integer-ops.md](integer-ops.md) (bit/integer gadget layer).
