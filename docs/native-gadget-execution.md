# Native gadget execution

Status: **proposal**. This document requests an architecture decision; it does
not authorize an implementation.

## Decision

Add host execution one gadget at a time by sharing each gadget's pure algorithm
over a private, minimal backend trait. Keep `xark::Field` symbolic in every
build. A gadget's optional `native` module instantiates the shared algorithm
with its real host type, beginning with `ark_bn254::Fr` for Poseidon2.

The first implementation should answer one product need only:

> A wallet can call the Poseidon2 implementation used by a circuit and obtain
> the same BN254 field element without maintaining a second permutation.

## Existing invariants

The design keeps the boundaries documented in
[`architecture.md`](architecture.md) and [`integer-ops.md`](integer-ops.md):

- `xark::Field` and the `__xark_*` functions are compiler markers. Their bodies
  do not define host behavior.
- Gadget calls lower because rustc monomorphizes trait calls and the compiler
  resolves them to concrete impl MIR before inlining.
- The compiler backend remains unaware of individual gadgets.
- `Private<T>` / `Public<T>` remain the visibility surface.
- Native integers do not acquire circuit semantics, and `U<N>` / `I<N>` are not
  reintroduced.

## Goals

1. Share the Poseidon2 round schedule, constants, S-box, and linear layers
   between circuit and host execution.
2. Make feature unification safe: enabling host support must not change the
   meaning or bodies of `xark::Field` operations.
3. Keep the default gadget crate `#![no_std]` and free of Arkworks dependencies.
4. Give the native path a direct differential test against the solved circuit,
   not only two independent known-answer tests.
5. Establish a pattern that another arithmetic gadget can evaluate before any
   common runtime abstraction is created.

## Non-goals

This proposal does **not**:

- run an entire `#[circuit]` function on the host;
- add host bodies to `xark::Field`, assertions, comparisons, hints, or bit ops;
- treat arbitrary Rust computations as witness-generation programs;
- change visibility, entry discovery, control-flow lowering, or integer types;
- promise native execution for non-arithmetic gadgets;
- add a shared backend trait to `xark` before two gadgets demonstrate the same
  abstraction.

Those are separate language/runtime decisions. They must not enter the
Poseidon2 pilot as incidental scope.

## Proposed API shape

The public circuit API remains byte-for-byte compatible:

```rust
pub fn poseidon2_perm(state: [xark::Field; 3]) -> [xark::Field; 3];
pub fn hash2(a: xark::Field, b: xark::Field) -> xark::Field;
```

With the gadget-local `native` feature enabled, an explicit host module is
added:

```rust
#[cfg(feature = "native")]
pub mod native {
    pub type Field = ark_bn254::Fr;

    pub fn poseidon2_perm(state: [Field; 3]) -> [Field; 3];
    pub fn hash2(a: Field, b: Field) -> Field;
}
```

The native functions return `Fr`; Arkworks defines its canonical byte
conversion. A later proposal can add a wallet-specific byte convenience API.

## Internal shape

`xark-poseidon2` owns a private capability trait containing only what the
permutation uses:

```rust
trait Poseidon2Backend:
    Copy + core::ops::Add<Output = Self> + core::ops::Mul<Output = Self>
{
    fn from_u64(value: u64) -> Self;
    fn from_decimal(value: &'static str) -> Self;
    fn pow5(self) -> Self;
}
```

The existing implementation becomes a private generic kernel:

```rust
fn poseidon2_perm_impl<F: Poseidon2Backend>(state: [F; 3]) -> [F; 3] {
    // Existing constants and round code, with F constructors.
}

impl Poseidon2Backend for xark::Field {
    // Delegates to the existing Field marker operations.
}

#[cfg(feature = "native")]
impl Poseidon2Backend for ark_bn254::Fr {
    // Real BN254 arithmetic.
}
```

The public circuit and native wrappers select the concrete backend. The crate
keeps the trait private to avoid creating an ecosystem contract in the pilot.

The compiler contains the required mechanisms: `lower_mir` resolves a
monomorphized trait method to its concrete impl with
`Instance::try_resolve`, then inlines available MIR. Existing `Field::from`
tests cover trait-instance resolution. A disposable compiler spike also
verified the proposed composition—a generic kernel, private trait, and
`xark::Field` impl—by lowering `(x + 3)^5 == out` to the expected three
constraints. This establishes feasibility only; acceptance gate 1 must still
prove the full Poseidon2 path without snapshot drift.

## Keep `xark::Field` symbolic

Cargo features are additive and unified across a dependency graph. Changing
marker bodies behind `xark/native` gives one type two global meanings and makes
partial support dangerous: an unsupported equality, assertion, conversion, or
hint can still reach a non-terminating marker body.

Keeping `xark::Field` symbolic avoids that class of failure. The host wrapper
uses a type with complete host semantics, including equality,
debugging, inversion, and serialization. Enabling `xark-poseidon2/native` adds
an API; it does not alter the circuit API.

## Share the complete permutation

Sharing only constants is insufficient. Drift can occur in round ordering,
initial/final linear layers, domain separation, or sponge padding while every
constant remains identical. The pure permutation kernel is the unit that must
be shared.

Conversely, the pilot should not genericize unrelated circuit code. The trait
is restricted to the exact operations used by Poseidon2 so the review can see
the complete semantic boundary.

## Acceptance gates for the Poseidon2 pilot

An implementation is mergeable only if all gates below pass:

1. **Circuit compatibility:** existing Poseidon2 R1CS and primitive snapshots
   are byte-identical.
2. **Native KAT:** the host permutation matches the existing canonical
   `[1, 2, 3]` and `hash2(0, 0)` vectors.
3. **Direct differential:** solve a circuit using the circuit wrapper and
   compare its output to the native wrapper for the same inputs.
4. **Feature isolation:** `cargo tree -e features` confirms that
   `xark-poseidon2/native` does not enable a semantic feature on `xark`.
5. **Default build:** the gadget still builds `#![no_std]` without Arkworks when
   default features are used.
6. **Native CI:** CI runs `cargo test -p xark-poseidon2 --features native`; the
   native tests may not exist only behind an unexercised feature.
7. **No compiler changes:** the pilot does not modify MIR validation, lowering,
   hints, visibility, or control flow.

## Rollout

1. Implement the Poseidon2 pilot exactly within the gates above.
2. Measure native call cost, including decimal constant construction, before
   adding caching or changing constant representation.
3. Evaluate one second arithmetic gadget. Use the result to decide whether the
   private trait shape repeats.
4. Propose any shared gadget-backend crate or wider runtime as a separate
   architecture decision backed by both implementations.

Reviewers who approve the pilot do not approve a later phase.

## Review questions

1. Is `ark_bn254::Fr` the right first public host representation, or should the
   native module expose canonical bytes only?
2. Is `native` precise enough as a gadget-local feature name, or should
   it be named `arkworks`?
3. Does a private per-gadget trait keep the abstraction local enough, or should
   the first pilot share only a private generic function and delay naming the
   capability boundary?

Do not start implementation until reviewers answer these three questions.
