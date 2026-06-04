# Memory opcode handling in xark

This document is the **design note** for ROADMAP step **WS-C.3**. The matching
implementation work is split across two follow-up steps:

* **WS-C.4** — constant-index memory (the easy 80%).
* **WS-C.5** — variable-index memory via a selector argument.

When starting C.4, follow the "Constant-index lowering" section below. When
starting C.5, follow the "Variable-index plan (C.5)" section.

## What Noir emits

Noir lowers Rust-like array access into **two opcodes** (see
`/tmp/noir-probe/acvm-repo/acir/src/circuit/opcodes.rs` and
`/tmp/noir-probe/acvm-repo/acir/src/circuit/opcodes/memory_operation.rs`):

```rust
Opcode::MemoryInit {
    block_id: BlockId,
    init: Vec<Witness>,
    block_type: BlockType,   // Memory | CallData(u32) | ReturnData
}

Opcode::MemoryOp {
    block_id: BlockId,
    op: MemOp<F>,
}

pub struct MemOp<F> {
    pub operation: MemOpKind,   // Read | Write
    pub index: Witness,
    pub value: Witness,
}
```

Semantics:

* `MemoryInit { block_id, init, block_type }` declares a block of length
  `init.len()`, initialised to the witness values listed in `init`. Block
  IDs are global within a circuit; there is **exactly one MemoryInit per
  block_id**, and all `MemoryOp`s on that block come after the init.
* `MemoryOp` for a **read** (`operation == Read`) enforces
  `value == block[index]`.
* `MemoryOp` for a **write** (`operation == Write`) updates
  `block[index] := value` for the purposes of subsequent reads.

### Note on the wire vs. in-memory shape of `MemOp`

The wire format (used by `Program::serialize_program`) stores `operation`,
`index`, and `value` as full `Expression<F>`s for backwards compatibility.
But the in-memory deserialised form **normalises each to a single
`Witness`**:

```rust
impl<'de, F: AcirField + Deserialize<'de>> Deserialize<'de> for MemOp<F> {
    fn deserialize<D: ...>(deserializer: D) -> Result<Self, D::Error> {
        let wire = MemOpWire::<F>::deserialize(deserializer)?;
        // operation must be 0 or 1
        let operation = ...;
        // index/value must each be `to_witness()`-able, else error.
        let index = wire.index.to_witness().ok_or_else(...)?;
        let value = wire.value.to_witness().ok_or_else(...)?;
        Ok(MemOp { operation, index, value, _phantom: PhantomData })
    }
}
```

This matters for our constant-index detection (see below): a literal
constant index in Noir source is not represented as a constant
`Expression`-style `q_c` term inside the MemOp — Noir pre-pins the index to
a witness via an earlier `AssertZero`. We detect "this index is constant"
by inspecting the *witness map* or the preceding `AssertZero` constraint
chain, not by inspecting the MemOp itself.

`BlockType::CallData(_)` / `BlockType::ReturnData` are databus markers used
for recursive proof schemes. For C.4 we treat them identically to
`Memory`; C.5 may need to revisit if databus blocks ever have variable
index access in practice.

## Why this is hard in R1CS

Random-access memory in R1CS requires one of:

* **Constant index** (the easy case). Emit a direct equality constraint to
  the matching slot. `O(1)` per access.
* **Variable index** (the hard case). Must encode "the read value equals the
  value at position `index`" without knowing `index` at circuit-definition
  time. Standard approaches:
  * **Selector argument.** Allocate `N` boolean selectors `s_0, ..., s_{N-1}`
    with `Σ s_j = 1` and `s_j * (index - j) = 0` for each `j`. Then
    `value = Σ s_j * arr[j]`. **`O(N)` per access.**
  * **Permutation argument.** Rearrange a witness vector into access order
    and check it's a permutation of the memory contents. `O(N)` total but a
    smaller constant factor. Plonkish-friendly, awkward in R1CS-only.
  * **Indexed lookup tables (PLOOKUP / Caulk).** Require extra commitments
    and a different proving system — too plonkish for a pure Groth16
    backend.

**Selector argument is the only R1CS-natural option** for xark. Cost per
variable-index access: `~2 + N` constraints (1 sum constraint, `N`
index-equality constraints, 1 read constraint; writes are similar).

## Decision: constant-index first (C.4), variable-index later (C.5)

**Rationale.**

1. Many Noir programs index arrays with **compile-time constants**: array
   literals, fully-unrolled loops, struct field access. Those programs
   should pay near-zero extra constraint cost — just plain ACIR wiring.
2. Constant-index handling unblocks the easy 80% of array-using programs in
   a small, low-risk step.
3. Variable-index is `O(N)` per access. Splitting it out gives users an
   **honest understanding of the cost** before they commit (a single
   `arr[x] = y` in a 1024-element array costs ~2K constraints).
4. The constant-index path has zero overlap with the selector argument, so
   shipping C.4 doesn't lock us into anything for C.5.

## Constant-index lowering (C.4)

### Detection

During lowering of `MemoryOp`, the `op.index` is a `Witness`. To decide
whether it's a constant we need to know its value at *constraint-definition
time*, not at proving time:

* In **proving mode**, the witness map carries `Fr` values for every witness;
  we can read `op.index`'s value from there.
* In **setup mode** (no witness map), the value is unknown — but Noir's
  constant indices are pinned via a preceding `AssertZero` that fully
  determines `index_witness`. Detect this by walking the preceding
  AssertZero opcodes for the function and folding linear constraints into a
  small `witness -> Fr` map. If `op.index` resolves to a constant, it's a
  constant index; otherwise reject.

Concretely (sketch):

```rust
// Build once per `synthesize` call, before the opcode loop:
let const_witnesses: BTreeMap<Witness, Fr> =
    collect_constant_witnesses(self.artifact.opcodes());

// In the MemoryOp arm:
match const_witnesses.get(&op.index) {
    Some(const_index) => lower_const_index(...),
    None => return Err(BackendError::UnsupportedOpcode {
        opcode: "MemoryOp[variable-index]",
        index: i,
        help: "Variable-index array access requires the selector \
               argument in ROADMAP step WS-C.5.",
    }),
}
```

`collect_constant_witnesses` is a forward sweep that recognises trivial
shape `AssertZero(w - c)` (i.e. `mul_terms.is_empty() &&
linear_combinations == [(1, w)] && q_c == -c`) and any chain that resolves
to the same.

### State management

The lowering layer holds a `BTreeMap<BlockId, Vec<WitnessIndex>>` shadow of
declared blocks:

* `MemoryInit { block_id, init, .. }` populates the map:
  `shadow.insert(block_id, init.iter().map(WitnessIndex::from_witness).collect())`.
* `MemoryOp { block_id, op: Read }` for constant index `j`: allocate
  `value_var = builder.alloc_witness(WitnessIndex::from_witness(op.value))`
  and `slot_var = builder.alloc_witness(shadow[block_id][j])`, then enforce
  `value_var == slot_var` via the standard `0*0 = value_var - slot_var`
  equality.
* `MemoryOp { block_id, op: Write }` for constant index `j`: allocate
  `value_var = builder.alloc_witness(WitnessIndex::from_witness(op.value))`
  and update `shadow[block_id][j] = WitnessIndex::from_witness(op.value)`.
  **No constraint emitted** — the write's effect propagates through any
  subsequent read constraints, and the prover-supplied witness for
  `op.value` is already pinned by whatever constraint produced it.

### Soundness sketch

For each constant-index **read**, we emit a constraint `value_witness ==
arr[index]_witness`. Both sides are witnesses pinned by other constraints
in the surrounding ACIR (either an `AssertZero` or the initial
`MemoryInit`). The prover cannot lie because lying about either side fails
its other constraint.

For **writes**, the shadow update means subsequent reads see the new
witness. The write itself contributes zero R1CS constraints — its effect is
purely in the lowering layer's bookkeeping. This is sound because:

* The post-write witness `op.value` is constrained elsewhere (by the
  AssertZero that produced it).
* Subsequent reads of the same slot pin to that same `op.value` witness,
  inheriting its constraints.
* The original `init` witness for that slot is simply no longer referenced
  from C.4's lowering — it stands or falls on whatever constraints existed
  before the write, which is fine.

### `block_type` handling in C.4

For `BlockType::Memory`, behaviour as described above. For
`BlockType::CallData(_)` and `BlockType::ReturnData`, behave identically in
C.4. If we later need databus-specific behaviour (e.g. enforcing the
calldata is exposed as public input), that's its own step — track as an
open question against C.4.

### What to test (C.4's acceptance criteria)

1. **Happy path.** A Noir program with `let a = [1, 2, 3]; assert(a[0] ==
   1)` proves and verifies. Add as `examples/array_const_index`.
2. **Multiple constant indices.** `let a = [1, 2, 3]; assert(a[0] + a[2] ==
   4)` proves and verifies.
3. **Constant-index write.** A program that writes to one slot, then reads
   back the new value, proves and verifies.
4. **Variable-index rejection.** A program with `assert(a[x] == y)` where
   `x` is a runtime variable must reject with a clear
   `UnsupportedOpcode { opcode: "MemoryOp[variable-index]", help: "...
   WS-C.5 ..." }` error.
5. **Tampering.** Tampering with any witness in the constraint chain (the
   init value, the read result, or any AssertZero-pinned witness in
   between) must cause verify to fail.

## Variable-index plan (C.5)

Implement the **selector argument** approach. Per variable-index
`MemoryOp`:

```text
Let N = block_length, i = index_witness, arr = shadow[block_id].

Allocate selectors s_0, ..., s_{N-1}, each constrained boolean:
    s_j * (s_j - 1) = 0       for j in 0..N         // N constraints

Enforce exactly one selector active:
    Σ s_j = 1                                       // 1 constraint

Enforce s_j picks out i = j:
    s_j * (i - j) = 0           for j in 0..N       // N constraints

For a read `value = arr[i]`:
    value = Σ s_j * arr[j]                          // 1 constraint
                                                    // (via Σ s_j*arr[j] - value = 0)

For a write `arr_post[i] := value`:
    arr_post[j] = (1 - s_j) * arr_pre[j] + s_j * value
                                  for j in 0..N     // N constraints
    (each `arr_post[j]` becomes the new shadow witness for slot j.)
```

**Cost.**

| Access type | Constraints     |
|-------------|-----------------|
| Read        | `2N + 2`        |
| Write       | `3N + 1`        |

That's a hard tradeoff: a single `arr[x] = y` in a 1024-element array
costs roughly **2K–3K constraints**. **Recommend Noir programs avoid
variable-index access when possible** — fully unrolled loops with compile-
time indices are dramatically cheaper.

### Implementation location for C.5

* Implement the selector logic in a new `gadgets::memory` module (or a
  submodule thereof), keeping the C.4 constant-index path in the same
  module for cohesion.
* Reuse `gadgets::range`'s boolean-enforcement helpers for the selector
  constraints.
* Extend `LoweredAcirCircuit` (or a sibling state struct) to hold the
  block shadows. C.5's write produces fresh `arr_post[j]` aux witnesses
  per slot per write — these accumulate; consider whether a long sequence
  of variable-index writes needs a more compact representation.

### What to test (C.5's acceptance criteria)

1. **Variable-index read.** `let i = x % len; assert(a[i] == expected)`
   proves and verifies.
2. **Variable-index write.** `a[i] = v; assert(a[i] == v)` proves and
   verifies for a runtime `i`.
3. **Out-of-bounds.** When `i >= N`, no selector can be 1 (because
   `s_j * (i - j) = 0` forces `i == j` for the active selector), so
   `Σ s_j = 1` and `s_j * (i - j) = 0` are jointly unsatisfiable. Proving
   fails. Verify the error surface is clean (probably
   `AssignmentMissing` from the selector value function, or
   `Unsatisfiable` at `is_satisfied()` time).
4. **Constraint count benchmark.** Add a microbench that measures per-access
   constraint count for `N ∈ {8, 64, 1024}` and pins the values in a
   `tests/` assertion, so we notice if the cost regresses.

## Open questions to confirm before C.4 starts

* Does Noir always pin constant indices via a single trivial `AssertZero`
  that we can detect with the `(w - c)` shape above, or does it sometimes
  inline the constant differently (e.g. as a witness with no constraints,
  relying on Brillig to populate it)? Spot-check by inspecting ACIR for
  `let a = [1, 2, 3]; assert(a[0] == 1)` after C.2 lands.
* Are `BlockType::CallData` / `ReturnData` blocks ever produced by the Noir
  programs we care about? If they are, do they ever have variable index
  access? This affects whether C.4 needs to special-case databus.
* When a `MemoryOp` writes to a constant index `j`, do we need to track
  *which AssertZero in the chain produced `op.value`* for the read-after-
  write soundness story, or is the per-witness constraint chain enough?

## Open questions to confirm before C.5 starts

* Is the `O(N)` per-access cost acceptable for the user-facing Noir programs
  we want to support, or should we offer a `--max-block-size-for-variable-
  index` flag that rejects oversized blocks before lowering?
* Should writes share selectors across a contiguous sequence of accesses to
  the same block (small constant-factor saving), or is per-op duplication
  fine for v1?

## Links

* **C.4** (constant-index implementation): see `ROADMAP.md` § WS-C.4.
* **C.5** (variable-index implementation): see `ROADMAP.md` § WS-C.5.
* Related lowering doc: `docs/acir-lowering.md`.
* Related ACIR types:
  `/tmp/noir-probe/acvm-repo/acir/src/circuit/opcodes.rs`,
  `/tmp/noir-probe/acvm-repo/acir/src/circuit/opcodes/memory_operation.rs`.
