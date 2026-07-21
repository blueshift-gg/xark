# Integer operations on `Field`

Status: **the `Field`-level surface is what ships.** PR #8 (`core-cmp`) *did*
ship first-class typed integers — `U<N>` (unsigned) and `I<N>` (signed) wrapper
types with range-proved inputs and checked fixed-width arithmetic — but those
were **removed** in favor of the `Field`-level comparison surface described
here (equality + range-checked ordering against a native-int width). Signed
integers and checked fixed-width (`U<N>`-style overflow-rejecting) arithmetic
are **not currently provided**; if reintroduced they would be `Field` methods,
not separate types (see [Explicitly not building](#explicitly-not-building)).

This document defines how `Field` supports integer-flavoured operations —
equality, ordering, shifts, and modulus — in circuits, and why the surface is
shaped the way it is.

## The core problem: a `Field` has no width

A `Field` is a residue in `[0, p)` for the BN254 scalar field (`p ≈ 2²⁵⁴`). It
is **not** a fixed-width integer:

* there is no most-significant bit, so `<<` / `>>` have no intrinsic meaning;
* ordering mod `p` is not the integer ordering unless you fix a range;
* every integer op therefore needs a **bit-width** `N`, and that width must be
  **enforced with a range check** — a malicious prover can otherwise place any
  residue in a wire and defeat an unchecked comparison/shift.

So the width can never be implicit or free. The only design question is *where
the width comes from*, and the answer this spec adopts is: **from the concrete
integer that is already in the expression.**

## Design principles

1. **Width comes from a native-int operand.** `x < 100u32`, `x >> 3u16`,
   `x % 8u8` — the RHS is a Rust integer, so its *type* supplies the domain
   width of `x` and its *value* supplies the bound / amount / modulus. No new
   types, no hidden defaults.
2. **Cost stays visible.** The width (and therefore the range-check cost) is
   spelled at the call site, either as the RHS literal's type (`…u32`) or, for
   the `Field`-vs-`Field` fallback, as an explicit `::<N>`. We deliberately do
   **not** add a global default width or dataflow inference that would hide the
   ~`N`-constraint cost behind clean-looking `a < b`.
3. **Decomposition is cached, not repeated.** The compiler memoizes
   `to_bits::<N>` so a value bounded once is shifted/compared/masked for free
   thereafter (see [Bit caching](#bit-caching)).
4. **Bare `Field` stays orderless and shiftless.** `Field: PartialOrd`,
   `Shl for Field`, `Rem for Field` (Field-on-both-sides, no width) are **not**
   provided — they are unsound-by-omission-of-a-width. `<` / `>>` / `%` exist
   only against a native-int RHS or via an explicit-width method.

## The surface

Let `T ∈ { bool, u8, u16, u32, u64, u128 }` and write `N = bitwidth(T)`
(`bool → 1`, `u8 → 8`, …, `u128 → 128`). Every op below interprets its
`Field` operand `x` as an `N`-bit value: it emits `to_bits::<N>(x)` (which
range-checks `x < 2ᴺ`) and then does the bit-level operation.

| Trait impl (for `Field`) | Enables | Meaning |
|---|---|---|
| `PartialEq<T>` | `x == c`, `x != c` | equality vs the constant `c` |
| `PartialOrd<T>` | `x < c`, `x <= c`, `x > c`, `x >= c` | `N`-bit ordering vs constant `c` |
| `Shl<T>` (`u8..u128`) | `x << n` | `(x mod 2ᴺ) << n`, truncated to `N` bits |
| `Shr<T>` (`u8..u128`) | `x >> n` | `(x mod 2ᴺ) >> n` = `⌊x / 2ⁿ⌋` |
| `Rem<T>` (`u8..u64` only) | `x % m` | `x mod m` |

`Shl`/`Shr` cover `u8..u128` (all sound — a shift is pure bit re-wiring and
`from_bits::<N>` with `N ≤ 128 ≤ 253` cannot wrap the field). `Rem` is provided
for `u8..u64` **only**: its general-modulus path pins a `hint_div_rem` witness
`[q, r]` with `m·q + r == x`, which stays sound only while `m·q + r` cannot wrap
the field, i.e. `2·N ≤ 253`. `u8..u64` satisfy this (`2·N ≤ 128`); `u128`
(`N = 128`, `2·N = 256 > 253`) does not, so `Rem<u128>` is **omitted** — `x %
5u128` fails to compile. Use a `u64`-or-narrower modulus.

Signed `i8..i128` may be added later with the same shape (bias by `2ᴺ⁻¹` into
`[0, 2ᴺ)` and reuse the unsigned path — this is how PR #8's removed `__xark_ilt`
worked); they are out of scope for v1.

### `Field`-vs-`Field` (the one case with no native RHS)

Comparing two *witness* values has no integer operand to carry a width, so it
keeps an **explicit const-generic method**:

```rust
a.lt::<32>(b)   a.gt::<32>(b)   a.le::<32>(b)   a.ge::<32>(b)   // -> bool wire
```

This is the genuinely rarer case, and the `::<32>` keeps its cost honest. It
lowers through the `__xark_ult::<N>` intrinsic (unsigned; a signed `ilt` variant
is not currently provided). There is intentionally **no** `PartialOrd for Field`
operator for this — see principle 4.

## Semantics & constraint cost (per op, width `N`)

All ops first obtain `bits = to_bits::<N>(x)` — `N` booleanity constraints + 1
recomposition constraint — **once per `(x, N)`**, then:

* **`x == c` / `x != c`** — a bare equality does not even need bits: it is
  `require`/`is_zero` on `x − c`. (Only reach for the decomposition if the same
  `x` is used in a width-`N` op elsewhere.) ~0–2 constraints.
* **`x < c` (const RHS)** — compare `bits` against the constant `c`; no second
  decomposition (the RHS is compile-time). Cheaper than a `Field`-vs-`Field`
  compare. `> / <= / >=` derive from `<` and `==` by negation/swap.
* **`x >> n`** — return the high `N − n` bits (`bitsₙ..`) recomposed; the shift
  itself is **free re-wiring**. Cost is just the shared `to_bits::<N>`.
* **`x << n`** — take bits `0..N−n`, place them at positions `n..N`, zero-fill
  low; recompose. Free re-wiring. **Truncates** at `2ᴺ` (integer `<<`
  semantics), *not* `x·2ⁿ mod p` — be explicit about this in the impl.
* **`x % m`** (`u8..u64` only) — for `m = 2ᵏ`, the low `k` bits (free). For
  general `m`, a `hint_div_rem` + range checks (`r < m` and `q < 2ᴺ`), sound
  because `2·N ≤ 253` keeps `m·q + r` from wrapping the field. `u128` is
  excluded for exactly this reason (`2·N = 256 > 253`); mod-by-zero lands on the
  general path and is unprovable (not a compile error, since `m` is runtime from
  rustc's view).

### Soundness

Each op range-checks `x < 2ᴺ` via `to_bits::<N>`. A prover holding an `x`
outside the declared domain **cannot satisfy** the circuit (the decomposition
is unsatisfiable), so no false proof is possible — the width is a *contract*
the author states via the RHS type, enforced in-circuit. Picking too small an
`N` makes valid large values unprovable (a liveness bug the author sees
immediately), never an unsound accept.

## Bit caching

The single optimization that makes the above cheap across repeated use.

The lowering already resolves every local to a canonical `LinearCombination`
(`simplified()` → sorted, merged terms). Add a memo table on the lowering env:

```rust
bit_cache: BTreeMap<(CanonicalLc, usize /* width N */), Vec<VarId>>
```

When any op needs `to_bits::<N>(x)`:

* **miss** → decompose as usual, store the bit vars under `(canonical(x), N)`;
* **hit** → reuse the stored bit vars; **skip** the `N` booleanity constraints
  and the recomposition constraint entirely.

So `x < 100u32; x >> 3u32; x & mask_u32` on the same `x` share **one** 32-bit
decomposition.

* **Soundness / invalidation:** circuit values are immutable in the lowering
  (each local → a stable LC), so cached bits never go stale; the first
  decomposition already fully constrained them.
* **Keying:** the LC is already canonical, so `x`, `x + 0`, `0 + x` normalize to
  the same key and hit. Needs an `Ord`/hash view over
  `(constant: FieldConst, sorted Vec<Term>)`.
* **v1 granularity:** cache per exact `(LC, N)`. A later refinement can let a
  wider cached split answer a narrower request (reuse the low bits of a cached
  64-bit decomposition for a 32-bit op).
* **Scope:** this is the automatic, general form of what `xark-bits` does by
  hand today (threading `[Field; 32]` around). Self-contained pass in
  `lower_mir`; no IR or surface changes.
* **Not the solver:** caching in the witness solver would save prover *time*
  only; the *constraint-count* win is entirely at lowering.

With this, const-generic methods get the same amortization a `U<N>` wrapper
would — which is why `U<N>`/`I<N>` are **not** needed for efficiency (see
below).

## Rust wrinkles

* `PartialOrd::partial_cmp` returns `Option<Ordering>`. That native return only
  makes sense for the **const-folded** case (both sides compile-time). The
  witness case must produce a `{0,1}` *wire*, so the operator lowering
  special-cases these `Field` comparisons through the `__xark_eq` / `__xark_ult`
  intrinsics rather than relying on a normal `partial_cmp` — this is exactly
  what PR #8's comparison intrinsics are for. The trait impls exist to satisfy
  type-check and give the syntax; the compiler owns the meaning.
* `PartialOrd<u32> for Field` gives `x < c` (Field on the left). The mirror
  `c < x` needs `PartialOrd<Field> for u32` (allowed — `Field` is local), but
  it's simpler to just write `x > c`.

## Explicitly not building

* **`PartialOrd` / `Shl` / `Shr` / `Rem` on bare `Field`** (Field-vs-Field, no
  width) — ill-defined without a width; would need a hidden default (footgun).
* **`Eq` / `Ord` markers** — a circuit `==` yields a *wire*, not a real total
  relation; these would wrongly imply `Field` is a valid map key / sortable.
* **`BitXor<Field>`** — `^` already means *pow* (`BitXor<u64>`); overloading it
  to xor for a `Field` RHS is a readability trap. Keep `.xor()` for that.
* **`U<N>` / `I<N>` typed integer wrappers** — shipped in PR #8, then
  **removed**. Their only edges over this surface were (a) operator sugar for
  `Field`-vs-`Field` and (b) cached bits; (b) is delivered by the memo table,
  and (a) is a narrow case served by `a.lt::<N>(b)`. Revisit only if a lot of
  word-heavy code (more hashes, fixed-point) makes a first-class bounded-int
  type worth two types + their full trait matrix. If reintroduced, `U<N>` would
  be "a `Field` plus its cached `[Field; N]` bits, operators delegating to this
  same surface."
* **Signed integers (`I<N>` / `i8..i128`)** — the signed ordering/bias path
  (`__xark_ilt`) shipped in PR #8 and was removed with `I<N>`; there is
  currently **no** signed comparison surface. It could return as
  `Field::ilt::<N>` etc. on the same bias-then-unsigned-compare pattern.
* **Checked fixed-width arithmetic** (`U<N>`-style `+`/`-`/`*` that
  range-re-prove their result so overflow is unsatisfiable) — shipped in PR #8,
  removed with the wrapper types; **not currently provided**. `Field` `+`/`-`/`*`
  are plain field ops with no width or overflow check. A future `Field` method
  could offer opt-in checked arithmetic.

## Cleanup carried by this work

PR #8 shipped an inconsistent state that this spec resolves:

* `impl PartialEq for Field` exists and works (`==` / `!=`) — keep.
* `require_lt` / `require_le` / `require_gt` / `require_ge` call `a < b` on `Field`,
  which does not compile (`E0369`, no `PartialOrd`) — they are **dead**. Either
  reimplement against this surface (const RHS → operator; two witnesses →
  `.lt::<N>`) or remove until the surface lands.
* The `lang.rs` comment claiming "`PartialOrd` on `Field` / `U<N>` / `I<N>`" is
  aspirational — none of those exist. Update it to describe the real surface.

## Related follow-ups (this review pass)

* **`require_eq` vs `require`** — keep `require_eq` as the primitive
  (`(a−b)·1 = 0`); `require(cond) = require_eq(cond, true)`. Do **not** invert
  (would make `require_eq` compute an is-zero boolean). *Resolved: no change.*
* **>128-bit constants** — `Field::from(u8..=u128)` caps at `u128` (Rust literal
  limit), *not* a value ceiling; full-width constants use `Field::from("<dec>")`
  (verified sound via the MiMC 254-bit round constants). Ergonomic gap only.
* **Comparison/shift width ceiling** — the intrinsics take any `N`; the real
  ceiling is the field width (~252–253 bits), far above the `u128`-typed
  surface here. `>128`-bit shifts are not a real need.
