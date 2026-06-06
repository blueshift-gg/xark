# Audit status

> **Has xark been externally audited?** No.

This document is the canonical place to track what *has* been internally
reviewed, what's known to be load-bearing for soundness, and what an
external auditor should focus on first. Pairs with
[`security.md`](security.md), which walks the per-gadget soundness claims.

---

## What's been reviewed internally

* [`security.md`](security.md) — per-gadget soundness sketches written
 alongside each gadget's implementation. Authored by the same person
 who wrote the gadget, so it should be read as an *assertion* of
 soundness rather than independent corroboration.
* [`brillig.md`](brillig.md) — soundness argument for the
 trust-outputs Brillig lowering strategy. Relies on a property of
 Noir's compiler, not on anything xark enforces directly.
* [`memory.md`](memory.md) — soundness of the selector-argument
 variable-index memory lowering.
* [`CEREMONY.md`](CEREMONY.md) — the phase-2 MPC ceremony
 driver and the admissibility checks on imported `.ptau` transcripts.
* Test suite of ~200 unit + integration tests including:
 * KAT cross-checks against `k256`, `p256`, `sha2`, `keccak`,
 `blake2`, `blake3`, `aes`, `ark-grumpkin`.
 * Tampering tests: every gadget's e2e test mutates the witness and
 verifies the constraint system reports unsatisfied.
 * Adversarial tests for `enforce_on_curve` (off-curve point
 rejection) and `enforce_in_range_one_to_n` (zero rejection).

This is **not** an external audit. Until an external firm has reviewed
the code, the README's "experimental — do not use in production" label
stays.

---

## Where an external auditor should start

Listed in rough order of "biggest blast radius if wrong":

### 1. Non-native arithmetic over secp curves (`gadgets/ecdsa.rs`)

The single largest soundness surface. Every ECDSA proof depends on the
correctness of:

* `bigint256_mul_mod` — limb-by-limb non-native multiplication with
 prover-aided quotient. The carry-decomposition bound (currently
 70 bits) is the subtle bit; off-by-one in the bound is unsound.
* `sub_mod` — the direct subtraction form
 (`a − b + k·m − c = 0`, `k ∈ {0, 1}`). The argument that `k` and
 `c < m` together pin `c` uniquely is in the function-level doc.
* `inv_mod` — modular inverse via `a · a_inv = 1`. Soundness reduces
 to `mul_mod`'s correctness plus a non-zero check on `a`.
* `enforce_on_curve` — `y² = x³ + a·x + b mod p`. Verifies prover
 supplied a valid curve point.
* `enforce_in_range_one_to_n` — `r, s ∈ [1, n − 1]`. Without it, a
 malicious prover could exploit the `inv_mod(s)` step.
* GLV decomposition (`glv_decompose_in_circuit`) — proves
 `k = k1 + λ·k2 (mod n)` with `|k1|, |k2| < 2^129`. The 129-bit
 bound is the standard GLV margin; tighter bounds would be unsound
 in edge cases.
* The fixed-base comb tables for `u1·G` — precomputed natively, used
 in-circuit as constants. The comb-row-2 case uses explicit
 doubling instead of the generic `ec_add_native_with_modulus`
 (which rejects same-x inputs); the Möbius-inversion polynomial
 expansion in `const_table16_select_point` is straightforward but
 worth a careful read.

### 2. Brillig trust-outputs assumption (`opcodes/brillig.rs`, `docs/brillig.md`)

`BrilligCall` outputs are allocated as fresh witnesses with **no**
in-circuit constraints. Soundness rests on a compiler-level property:
*every Brillig output must be pinned by surrounding ACIR `AssertZero`
opcodes.* xark does not verify this; we trust Noir's compiler.

An auditor should:

* Read the compiler invariants cited in [`brillig.md`](brillig.md).
* Construct adversarial ACIR artifacts where a Brillig output is **not**
 pinned and confirm that the proof's public-input semantics break in a
 detectable way. If they don't, the trust-outputs assumption is wrong.
* Consider whether a `--strict` static analyser should ship (a
 conservative checker that every Brillig output is pinned by
 AssertZero / range / equality chain). See the README's
 "remaining gaps" list.

### 3. Universal predicate gating (`r1cs_builder.rs:enforce_gated`)

The e-aux trick: under an active call-site predicate `p`, every
`A · B = C` becomes `A · B = C + e` plus `p · e = 0`. When `p = 0`,
`e` is free and the original is disabled; when `p = 1`, `e = 0` and
the original is enforced. The linear-only fast path (when `A` and
`B` are empty LCs) collapses to `p · C = 0` directly.

Soundness depends on `p` being a real boolean (the
`materialize_predicate` helper enforces it) and on the `e`
allocation's value closure computing `A·B − C` honestly. The closure
reads variable assignments via `cs.assigned_value`; any variable
referenced in A, B, or C must already have its value populated. The
in-circuit assertion is that all such variables are allocated
before the enforce call — this is a structural property of the
lowering, not an in-circuit check. An auditor should look for any
gadget that emits a constraint referencing a variable allocated *after*
the constraint.

### 4. R1CS lowering layer (`acir-r1cs/src/lower.rs`)

* `lower_assert_zero_gated` — emits `p · combined = 0` under a
 predicate. The "combined" LC sums all the mul-term auxes plus the
 linear part plus the constant; off-by-one in coefficient signs is
 unsound.
* `lower_call_at` — inlines callee opcodes with witness/block-id
 shifting. The combined-predicate computation
 (`combine_predicates`) multiplies parent and inner predicates as
 booleans.
* Pinned-constant detection (`memory.rs:extract_pinned_constants`)
 — distinguishes constant-index from variable-index memory ops.
 An auditor should consider whether a malicious ACIR stream could
 fool the pinning detector into treating a variable-index op as
 constant-index and exploit the cheaper lowering path.

### 5. Trusted-setup ceremony (`xark-backend/src/setup_phase2.rs`, `ceremony.rs`, `ptau.rs`)

* `.ptau` admissibility checks — degree match, subgroup membership,
 pairing-consistency, etc.
* Phase-2 contribution — Schnorr proof of knowledge for each δ
 contribution; chain verification.
* The deterministic-RNG path for `--insecure-dev-mode` (the only RNG
 path used by tests) is explicitly *not* production-safe; the
 CLI guards prevent its use outside dev mode.

### 6. Serialisation boundaries (`xark-backend/src/{serialization,solana}.rs`)

* Binary VK/proof format — pinned by
 [`serialization.md`](serialization.md) and snapshot-tested.
* Solana export — little-endian uncompressed encoding (`x || y`, each
 field element 32-byte LE), with `Fq2` components in `(c0, c1)` order.
 This is what `xark-verifier` consumes on chain via the `alt_bn128_*_le`
 syscalls; `assemble_{vk,proof,public_inputs}_bytes_le` in `solana.rs`
 is the canonical encoder. (The module also keeps the legacy big-endian
 `(c1, c0)` Ethereum-precompile encoders — now used only as a canonical
 point representation for ceremony transcript hashing, not for export.)

---

## Out of scope

* External audit cost / scoping — not yet engaged.
* Side-channel analysis of the prover binary — Groth16's standard
 threat model treats the prover as a black box; the prover's
 randomness source is documented in [`security.md`](security.md).
* Fault attacks on the prover machine — handled at the deployment
 layer.
* Network-level integrity between prover and verifier — out of scope.

---

## How to update this document

When an audit happens, replace the *Has xark been externally
audited?* line at the top with the audit firm, date, scope, and link
to the published report. Move "findings" into a new
`## Audit findings (YYYY-MM-DD, <firm>)` section and link to the
report. Keep this document concise — it is not a re-statement of
[`security.md`](security.md), only a pointer for an external
reviewer.
