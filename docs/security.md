# Security Review Checklist

The release-gating soundness walk-through for xark's Groth16 backend.

Two audiences: (1) a release engineer ticking
[§5](#5-release-gating-checklist) before shipping a circuit; (2) an external
auditor reading [§2](#2-per-gadget-soundness-sketches) to find load-bearing
claims to attack. Every claim has a pointer into the codebase; when the
implementation drifts, *this document is the canonical place to update*.
Supporting design notes: [`architecture.md`](architecture.md),
[`serialization.md`](serialization.md), [`trusted-setup.md`](trusted-setup.md).

---

## 1. Threat model

### What the prover can do

The prover is fully adversarial:

* may construct any witness assignment (any assignment to private witnesses).
* may lie about hint/advice outputs (modular inverses, bit decompositions,
 quotients/remainders) supplied via the `hint_*` primitives.
* may craft public inputs that do not match the circuit's intended semantics.
* may attempt to produce a proof for a statement the verifier rejects.

We do **not** model:

* the prover obtaining the trusted-setup trapdoor (τ, α, β, γ, δ). Anyone with
 these can produce proofs for any statement; this is the standard Groth16
 assumption.
* the prover compromising the verifier's view of `(VK, public_inputs)`. The
 verifier's transport-level integrity is out of scope.

### What the verifier consumes

The verifier sees only `(verifying_key, proof, public_inputs)`. Claims below
are conditional on those three values being the ones xark produced from a
fixed, audited artifact.

### Groth16 as a soundness oracle

We treat the Groth16 pairing equation
`e(A, B) = e(α, β) * e(vk_x, γ) * e(C, δ)` as a sound non-interactive
argument of knowledge for satisfaction of the R1CS we emitted, modulo
discrete-log assumptions on BN254 and the trusted-setup assumption. **What we
constrain into the R1CS is enforced; what we leave outside is unconstrained
and the prover can choose freely.**

The soundness argument in this document therefore reduces to: *for every gadget
we emit, the emitted R1CS constraints imply the claimed input/output relation*.

### Trusted setup

We assume τ (the Powers-of-Tau toxic waste) and the circuit-specific γ, δ
were unknown to the prover at proving time and remain unknown going forward.
α, β, γ, δ are public in the verifying key. See [§3](#3-trusted-setup) for
the current state of xark's setup modes.

### Out of scope

We are explicitly *not* defending against:

* **A circuit or gadget that leaves a hint/advice output unconstrained.**
 Our hint model assumes every `hint_*` output witness is pinned by
 surrounding R1CS constraints; see
 [§2.15](#215-hint-outputs-advice) below. It is the circuit author's and
 gadget's responsibility to constrain every hint value.
* **A future Arkworks Groth16 implementation regression.** We pin via
 Cargo.lock; bumping `ark-groth16` requires re-verifying the byte-level
 serialization round-trip test
 (`crates/tests/tests/serialization.rs`).
* **Side-channel leakage in the prover.** No constant-time guarantees are
 made; the prover should not run on untrusted hardware.
* **Side-channel leakage in trusted-setup randomness.** `OsRng` is treated as
 a primitive; if the host entropy is compromised, so is the setup.
* **Curve-level attacks on BN254.** BN254 has ~100 bits of security against
 Special TNFS at this size; consumers needing more should not use BN254
 Groth16.

---

## 2. Per-gadget soundness sketches

Every gadget below lives in its own `xark-*` gadget crate. Each subsection
states the relation the gadget claims to enforce, the R1CS rows it emits, and
the argument that the rows imply the relation over `Fr = BN254 scalar field`.

### 2.1 `enforce_boolean`

**File.** `crates/xark-bits/src/lib.rs`.

**Relation.** For input variable `x`, after this gadget runs, any satisfying
assignment has `x ∈ {0, 1}` as field elements.

**Constraint emitted.** A single R1CS row

```
x * (x - 1) = 0
```

**Argument.** `Fr` is a prime field, hence an integral domain (no zero
divisors). The polynomial `X * (X - 1) ∈ Fr[X]` has degree 2 and roots exactly
`{0, 1}`. Therefore `x * (x - 1) = 0 ⟺ x = 0 ∨ x = 1` for any `x ∈ Fr`.

**Cost.** 1 constraint.

### 2.2 `decompose_into_bits` (range gadget)

**File.** `crates/xark-bits/src/lib.rs`. Constant
`MAX_BITS = 253`.

**Relation.** For input variable `value_var` and width `n ≤ MAX_BITS`,
allocates `n` boolean variables `b_0, …, b_{n-1}` such that any satisfying
assignment has both:

1. `b_i ∈ {0, 1}` for every `i`, and
2. `Σ_{i=0..n-1} 2^i * b_i = value_var`.

**Constraints emitted.** `n` boolean checks (via [§2.1](#21-enforce_boolean))
plus one linear "recompose" constraint
`Σ_i 2^i * b_i - value_var = 0`.

**Argument.** Each `b_i ∈ {0, 1}` by §2.1. Given that, the linear constraint
forces `value_var` to be the integer with those bits as its little-endian
binary expansion. **Uniqueness of the decomposition** requires `2^n - 1` to
be representable as a distinct field element from any other integer in
`[0, 2^n - 1]`. The BN254 scalar field has order

```
r ≈ 2.188 × 10^77 < 2^254
```

so any `n ≤ 253` keeps `2^n ≤ 2^253 < r`, meaning `[0, 2^n - 1]` injects
into `Fr` and the bit pattern is unique.

**Boundary.** If we ever allowed `n ≥ 254`, the prover could choose a bit
pattern such that `Σ_i 2^i * b_i ≡ value_var (mod r)` for *more than one*
distinct bit pattern in `[0, 2^n - 1]` (specifically, both `value_var` and
`value_var + r` would have valid bit decompositions if both are
representable in `n` bits). This would break the soundness of every gadget
that consumes the resulting bits — XOR, AND, range checks would all admit
multiple satisfying assignments for the same input. The `MAX_BITS = 253`
constant is therefore load-bearing; do not raise it.

**Cost.** `n` constraints (booleans) + 1 (recompose) = `n + 1`.

### 2.3 32-bit XOR (`xor`)

**File.** `crates/xark-bits/src/lib.rs`.

**Relation.** Inputs `a, b: Word32` (each `Word32` is 32 LCs, each LC's value
in `{0, 1}` by prior bit-decomposition). Output `out: Word32` such that
`out.bits[i] = a.bits[i] XOR b.bits[i]` for `i ∈ 0..32`.

**Constraints emitted per bit.**

1. Allocate `out_i` and enforce `out_i ∈ {0, 1}` via §2.1 (1 constraint).
2. Enforce `(2 * a_i) * b_i = a_i + b_i - out_i` (1 constraint).

**Argument.** Rearranging the second constraint gives
`out_i = a_i + b_i - 2 a_i b_i`. Tabulating for `a_i, b_i ∈ {0, 1}`:

| `a_i` | `b_i` | `a_i + b_i - 2 a_i b_i` | XOR |
|-------|-------|--------------------------|-----|
| 0 | 0 | 0 | 0 |
| 0 | 1 | 1 | 1 |
| 1 | 0 | 1 | 1 |
| 1 | 1 | 0 | 0 |

So whenever the inputs are boolean (which the caller guarantees), the algebra
forces the XOR table. The extra boolean check on `out_i` is redundant in this
case but defends against a future caller passing non-boolean LCs; we keep it
because composability is cheaper than re-auditing.

**Cost.** 32 bool + 32 mul = 64 constraints per word.

**KAT.** Tests in `gadgets::bitwise::tests::xor_matches_native_random` and
`xor_n_matches_native_random_widths` (the `WordN` variant for widths 8/16/32/64).

### 2.4 32-bit AND (`and`)

**File.** `crates/xark-bits/src/lib.rs`.

**Relation.** Same shape as XOR: `out.bits[i] = a.bits[i] AND b.bits[i]`.

**Constraint emitted per bit.** `a_i * b_i = out_i`.

**Argument.** For `a_i, b_i ∈ {0, 1}`, the product is the AND table value.
`out_i` is implicitly boolean because the product of two booleans is
boolean (so we save a redundant boolean check that XOR has to pay).

**Cost.** 32 mul = 32 constraints per word.

**KAT.** `gadgets::bitwise::tests::and_matches_native_random` and the
`WordN` `and_n_matches_native_random_widths`.

### 2.5 32-bit ADD mod 2^32 (`add_mod_32`)

**File.** `crates/xark-bits/src/lib.rs`.

**Relation.** Given up to `MAX_TERMS = 8` 32-bit input words, returns a
`Word32` equal to the `mod 2^32` sum of the inputs.

**Constraints emitted.**

1. Allocate 32 boolean result bits + `⌈log2(MAX_TERMS)⌉ = 3` boolean carry
 bits (32 + 3 = 35 boolean checks).
2. One linear constraint:
 `Σ_terms Σ_i 2^i * a_i = Σ_{i=0..32} 2^i * result_i + Σ_{j=0..k} 2^(32+j) * carry_j`.

**Argument.** Each result/carry bit is in `{0, 1}` by §2.1. The linear
constraint pins the integer value of the right-hand side to the integer
value of the left-hand side, *as field elements*. For uniqueness we need
both sides to lie in `[0, r)` as integers, which is satisfied because the
left-hand side is at most `MAX_TERMS * (2^32 - 1) = 8 * (2^32 - 1) < 2^35`
and the right-hand side is at most `2^35` by construction. Since the
left-hand side is the integer sum of the inputs, the right-hand side is
forced to be the same integer, and its bit decomposition is unique (per §2.2
applied to a 35-bit value). Therefore `result` equals the low 32 bits of
the integer sum.

**Cost.** 35 boolean checks + 1 linear constraint = 36 constraints per call.

**KAT.** `gadgets::bitwise::tests::add_mod_32_matches_native` and the
adversarial counterpart `add_mod_32_constraint_fails_on_bad_witness`.

### 2.6 SHA-256 compression

**File.** `crates/xark-sha256/src/lib.rs`. Round constants
`K256[0..64]` and the schedule mirror NIST FIPS 180-4 §6.2.

**Relation.** Given a 16-word message block and 8-word state, returns the
8-word post-compression state.

**Constraints emitted.** Composition of [§2.3](#23-32-bit-xor-xor),
[§2.4](#24-32-bit-and-and), [§2.5](#25-32-bit-add-mod-232-add_mod_32),
`rotr`, `shr`, `not`. The latter three are pure index permutations / bit
complements that emit *zero* constraints (they re-arrange or re-coefficient
LCs in place).

**Argument.** The composition is byte-by-byte the FIPS 180-4 algorithm:

* Message schedule W[16..64] uses `σ0(x) = ROTR^7 ⊕ ROTR^18 ⊕ SHR^3` and
 `σ1(x) = ROTR^17 ⊕ ROTR^19 ⊕ SHR^10`, each a triple-XOR of pure
 permutations of `w[i-15]` / `w[i-2]`, then sums four 32-bit words via
 `add_mod_32`.
* Working state updates use `Σ0`, `Σ1`, `Ch(e,f,g) = (e ∧ f) ⊕ (¬e ∧ g)`,
 `Maj(a,b,c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)`, each of which is a fixed
 pattern of `xor`, `and`, `not` calls.
* The final state is `state[i] + working[i] mod 2^32` for each `i`.

Because every primitive used (`xor`, `and`, `not`, `rotr`, `shr`,
`add_mod_32`) is itself sound by §2.1–§2.5 (and the pure-permutation ops
emit no constraints, so they can't introduce unsoundness), and because the
composition mirrors the spec character-by-character, the gadget emits a
constraint system whose unique satisfying assignment is FIPS 180-4
compression.

**KAT.** `gadgets::hash::tests::compression_matches_sha2_crate_on_abc_block`
cross-checks the in-circuit compression on the padded "abc" message block
against the `sha2` crate's `compress256`.

### 2.7 Keccak-f[1600]

**File.** `crates/xark-keccak/src/lib.rs`.

**Relation.** Implements the Keccak-f[1600] permutation as 24 rounds over a
5×5 array of 64-bit lanes. Each lane is held as a `WordN` of width 64; each
round consists of θ, ρ, π, χ, ι steps.

**Argument.** θ and χ reduce to per-bit XOR (and one AND for χ); ρ is a
fixed per-lane rotation (pure permutation, no constraints); π is a fixed
lane permutation (no constraints); ι XORs a constant into lane (0,0). All
constraints reduce to the 64-bit generalizations of §2.3 / §2.4, plus the
range/boolean primitives. The round-constant table is the standard
`RC[0..24]` from FIPS 202.

**KAT.** `gadgets::keccak::tests::in_circuit_zero_state_matches_kat` (against
the `keccak` crate on the all-zeros block) and
`in_circuit_random_state_matches_native` (random states cross-checked).

### 2.8 Blake2s

**File.** `crates/xark-blake2s/src/lib.rs`.

**Relation.** Implements the Blake2s compression (10 rounds, 32-bit lanes,
G mixing function) plus the streaming wrapper (variable-length
input → 32 output bytes).

**Argument.** Same recipe as SHA-256: G's mixing reduces to `xor`, `add_mod_32`,
and right-rotation by fixed offsets (12, 7, 8, 16). Padding follows the
Blake2 spec; we cross-check the *native* implementation against the `blake2`
crate before checking the in-circuit one against the native one.

**KAT.** `gadgets::blake2s::tests::blake2s_native_matches_blake2_crate_on_abc`
plus `blake2s_in_circuit_matches_native_on_abc`,
`blake2s_in_circuit_random_lengths`, `blake2s_in_circuit_empty_input`.

### 2.9 Blake3

**File.** `crates/xark-blake3/src/lib.rs`. Supports both single-chunk
(`inputs.len() ≤ CHUNK_BYTES = 1024`) and multi-chunk inputs via the standard
binary-tree CV combination.

**Argument.** The compression function is almost identical to Blake2s with
slightly different mixing constants. Single-chunk uses the fast path
(`chunk_compress_in_circuit` directly); multi-chunk computes per-chunk CVs
and combines them via a binary tree per the BLAKE3 spec.

**KAT.** `gadgets::blake3::tests::blake3_native_matches_blake3_crate_on_abc`,
`blake3_in_circuit_matches_native_on_abc`,
`blake3_in_circuit_block_boundaries`,
`blake3_in_circuit_random_lengths`,
`blake3_in_circuit_rejects_oversized_input`.

### 2.10 Poseidon2 permutation

**File.** `crates/xark-poseidon2/src/lib.rs`. Constants match the standard
reference Poseidon2-BN254 parameter set; they are vendored verbatim into the
crate rather than re-derived.

**Relation.** State width `T = 4`, `R_F = 8` full rounds, `R_P = 56` partial
rounds, S-box `x^5`, external matrix `M_E` (the standard 4×4 partner of the
diagonal one), internal matrix `M_I` defined by `INTERNAL_DIAG_HEX`.

**Argument.** Each S-box `x^5` is three R1CS multiplications
(`t = x*x`, `u = t*t`, `out = u*x`); each correctly pins the output to the
fifth power of the input. Linear layers (matrix multiplications) fold into
LCs and emit one fresh witness allocation per state cell per round to keep
LC sizes bounded. Because Poseidon2 is field-native (no bit decomposition),
the only soundness-relevant arithmetic is field multiplication and
addition, both of which are R1CS-native and bit-exact.

The parameter set is the load-bearing claim here: we re-derive nothing, we
copy the constants. If the upstream reference parameter table has a
soundness bug, we inherit the same bug.

**KAT.** `gadgets::poseidon::tests::native_matches_external_kat_all_zeros`
(matches the reference Poseidon2-BN254 `Poseidon2(0, 0, 0, 0)` output) and
`in_circuit_matches_external_kat_all_zeros` /
`in_circuit_matches_native_on_1_2_3_4`.

### 2.11 AES-128 encryption

**File.** `crates/xark-aes/src/lib.rs`. CBC mode, no padding —
input length must be a positive multiple of 16; PKCS#7 padding (if needed)
is the caller's responsibility before invoking the gadget.

**Relation.** Per-block: 10-round AES-128 over GF(2^8).

**Argument.** The painful primitive is the S-box. We do *not* use the
Boyer-Peralta optimization (the published 32-AND/83-XOR straight-line
program); we use an algebraic decomposition:

1. Hint `x_inv = x^{-1}` in GF(2^8) (with `x_inv = 0` when `x = 0`) via a
 witness.
2. Enforce `x * is_zero = 0` and `x_inv * is_zero = 0` for a boolean
 `is_zero` indicator. Together these pin `is_zero = (x == 0)` *as long as
 `x` is in [0, 255]*, which is true because the caller bit-decomposes
 every byte. (If `x` were outside the byte range, `is_zero = 1` could be
 satisfied with `x ≠ 0`; the byte range check upstream prevents this.)
3. Compute the 64 cross-products `p_{i,j} = bit_i(x) * bit_j(x_inv)` via 64
 AND constraints.
4. Reduce the polynomial product mod the AES reduction polynomial
 `m(x) = x^8 + x^4 + x^3 + x + 1` to get the bits of `x * x_inv` in
 GF(2^8); enforce these equal `1` if `x ≠ 0` else `0`. This pins
 `x_inv = x^{-1}` (or both are 0).
5. Apply the AES affine transform to `x_inv` to get the S-box output.

ShiftRows is a pure index permutation (zero constraints). MixColumns and
AddRoundKey are byte-wise XOR with `xtime` (the multiply-by-2 in GF(2^8))
helpers. Key expansion uses the same S-box and `Rcon` table.

**KAT.** `gadgets::aes::tests::aes_native_matches_aes_crate_on_fips197_kat`
(against the `aes` crate on the FIPS-197 test vectors),
`aes_in_circuit_matches_native_on_kat`,
`aes_in_circuit_two_block_cbc`,
plus the full-table cross-check `sbox_all_inputs_match_table` and
`gf256_inv_roundtrips` (256-input exhaustive cross-checks of the S-box
and the GF(2^8) inverse helper).

### 2.12 Grumpkin curve (point add + MSM)

**File.** `crates/xark-grumpkin/src/lib.rs`.

**Relation.** Affine `(x, y, is_infinity)` points on Grumpkin (whose base
field is BN254 `Fr`). `ec_add_in_circuit` enforces affine addition with
edge-case handling for doubling, identity, and inversion.

**Argument.** The constraint system uses selector witnesses:

* `same_x ∈ {0, 1}` pinned by `same_x * (x2 - x1) = 0` plus an inverse hint
 `(x2 - x1) * inv_dx = 1 - same_x`. The hint forces `same_x = 1 ⟺ x1 = x2`:
 if `x1 = x2` then the first row trivially holds and `inv_dx = 0`, `same_x = 1`
 satisfies the second; if `x1 ≠ x2` then the first row forces `same_x = 0`,
 and `inv_dx = (x2 - x1)^{-1}` satisfies the second.
* `same_y` is analogous.
* `is_double = same_x ∧ same_y ∧ ¬lhs_inf ∧ ¬rhs_inf`,
 `is_inverse = same_x ∧ ¬same_y ∧ ¬lhs_inf ∧ ¬rhs_inf`. Both are pinned
 via Boolean AND chains.
* `lambda` is computed from one of three formulas (doubling, inversion,
 general add) selected by the selectors; the result coordinates are then
 computed from `lambda` via the standard `x3 = lambda^2 - x1 - x2`,
 `y3 = lambda * (x1 - x3) - y1`.

The selector polynomial argument ensures each case is mutually exclusive
and exhaustive. The inverse hints are the load-bearing soundness step: an
adversarial prover cannot satisfy both rows with a wrong `same_x` because
the second row would require `(x2 - x1) * inv_dx = 0` when in fact
`x2 - x1 ≠ 0`, forcing `inv_dx = 0`, then row two becomes `0 = 1 - 0 = 1`
which is unsatisfiable.

MSM uses double-and-add over the bit decomposition of each scalar limb pair
(`(lo, hi)`). Each bit step is a conditional add via `conditional_select_point`.

**KAT.** `gadgets::curve::tests::ec_add_native_matches_arkworks`,
`ec_add_in_circuit_matches_native_generic`,
`ec_add_in_circuit_handles_doubling`,
`ec_add_in_circuit_handles_infinity_lhs`,
`ec_add_in_circuit_handles_infinity_rhs`,
`ec_add_in_circuit_handles_inverse`,
`msm_in_circuit_single_point_small_scalar`,
`msm_in_circuit_two_points`,
`random_scalars_match_native`.

### 2.13 xark-IR arithmetic → R1CS lowering

**Files.** `crates/xark-ir/` (the xark-IR arithmetic ops the MIR
lowering emits) and `crates/xark-prover/` (R1CS synthesis).

**Relation.** Each arithmetic assertion asserts
`q_c + Σ_k coef_k * w_k + Σ_i q_M_i * a_i * b_i = 0` for the linear
combinations referenced by the expression. `assert_eq(x, y)` lowers to
the `x - y = 0` form of this.

**Constraints emitted.** Three cases based on the number of mul terms:

* **0 mul terms (linear-only).** Emit one row `0 * 0 = -(linear + q_c)`,
 which forces `linear + q_c = 0`.
* **1 mul term `q_M * a * b`.** Emit one row `a * (q_M * b) = -(linear + q_c)`.
* **`m > 1` mul terms.** For each `(q_M_i, a_i, b_i)`, allocate an aux
 variable `t_i` and emit `a_i * b_i = t_i` (one row each, pinning `t_i` to
 the witness product). Then emit one final linear row
 `Σ_i q_M_i * t_i + linear + q_c = 0`.

**Argument.** In all three cases, the emitted rows are equivalent to the
original `expression = 0`. For the multi-mul case, the `t_i = a_i * b_i`
constraints uniquely determine each `t_i` from the witness assignment, so
the final linear row evaluates to the original expression. Because R1CS
rows are evaluated as field-element identities, satisfaction of the rows is
equivalent to satisfaction of the original expression over `Fr`.

### 2.14 Public input ordering

**Files.** `crates/xark-prover/` (R1CS synthesis) and
`crates/xark-ir/` (the variable table, where each `Public` variable is
recorded in declaration order).

**Relation.** The verifier consumes public inputs in the *exact same order*
the prover provided them to the constraint system. Mismatches would result
in the verifier silently accepting a proof for a different statement.

**Argument.** The prover allocates public-input variables in the order the
`circuit` function's `Public<Field>` parameters appear in its signature,
**before any arithmetic constraint is lowered**. This guarantees the
Arkworks R1CS sees public-input variables in the same order the verifier
expects. The circuit hash folds the public-input variable indices into the
hash, so any reordering changes the circuit identity.

**Tests.** `lower::tests::circuit_hash_changes_with_public_input_order` pins
the public-input ordering into the circuit hash. (A prior end-to-end
public-input tamper matrix was removed on this branch; restoring it is tracked
as a follow-up — see the audit notes.)

### 2.15 Hint outputs (advice)

**Where.** The `hint_*` primitives (e.g. `Field::hint_inverse`,
`hint_bits`) in `crates/xark/` (the `lang` module) and their witness-solver
counterparts in `crates/xark-prover/`.

**Relation.** A hint allocates a fresh witness that the prover fills during
witness generation but for which the circuit emits **no constraint at the
hint itself**.

**Argument.** Soundness relies on a gadget-authoring invariant: every hint
output witness must also be referenced by at least one surrounding R1CS
constraint that pins its value relative to other constrained witnesses. The
canonical example is "supply `w = x⁻¹` as advice, then assert `x * w = 1`".
The check-half is what the R1CS enforces; the hint-half we trust to produce
*a* value but rely on the check to pin it to the *right* value (see the
`inverse` example).

If a gadget ever emits a hint output that is not subsequently constrained,
the corresponding witness is free to be anything the prover chooses, and the
proof is unsound. This is an explicit out-of-scope assumption per
[§1](#1-threat-model): it is the circuit author's and gadget's
responsibility to constrain every hint value.

---

## 3. Trusted setup

### Assumption restated

The Groth16 verifying key contains group elements derived from the
trapdoor `(τ, α, β, γ, δ)`. **Soundness assumes the prover does not know
any of these.** Knowledge of `τ` (the phase-1 power) breaks every circuit
sharing the same Powers-of-Tau ceremony; knowledge of `(γ, δ)` (the
phase-2, circuit-specific values) breaks only the specific circuit they
were derived for.

### Current state

| Setup mode | Source of randomness | `production_safe` | metadata.json `setup_mode` |
|------------------------|----------------------|-------------------|-----------------------------|
| `--insecure-dev-mode` | `OsRng` (default) or `ChaCha20Rng(seed)` if `--deterministic-rng <seed>` | `false` | `"insecure-dev-mode"` |
| `xark setup --ptau-file` | snarkjs Powers-of-Tau (phase-1) + a single phase-2 contribution | `true` | `"phase2-from-ptau"` |
| `xark ceremony …` | snarkjs Powers-of-Tau (phase-1) + multi-contributor phase-2 MPC | `true` | `"phase2-from-ptau+mpc[N contributors]"` |

`KeyMetadata` is defined in
`crates/backend/src/keys.rs` and includes:

* `setup_mode: String` — e.g. `"insecure-dev-mode"`.
* `production_safe: bool` — `false` for any dev-mode key.
* `deterministic_rng_seed: Option<u64>` — present only when the operator
 explicitly chose reproducibility.
* `ptau_source: Option<String>` — filename of the consumed Powers-of-Tau
 transcript.
* `phase2_seed_hash: Option<String>` — SHA-256 of the *seed* used to
 derive `(γ, δ)`; the seed itself must be discarded immediately after
 setup.

### Dev-mode trapdoor lifecycle

In `--insecure-dev-mode`, the trapdoor exists transiently in process memory
during `ark-groth16`'s `circuit_specific_setup`. After return the only
durable artifacts are the proving key (the trapdoor *exponentiated into
group elements*, not the scalar itself) and the verifying key. Recovering
the trapdoor would require solving discrete log on BN254. A dev-mode key
is therefore no worse than a one-party "ceremony" with the operator as
sole contributor — still insufficient for production because the operator
is a single point of failure, there's no public transcript, and the
metadata flag `production_safe: false` should be rejected by any
production deployment script.

### Production setup

Production setup requires a Powers-of-Tau transcript plus a phase-2
contribution. Both are **implemented**: `crates/backend/src/ptau.rs`
parses a snarkjs `.ptau` (with admissibility checks), `setup_phase2.rs`
derives a phase-2 setup from it, and `ceremony.rs` drives a multi-contributor
MPC ceremony (Schnorr PoKs + δ-consistency pairing checks), exposed as
`xark ceremony {init,contribute,verify,finalize}`. The `--insecure-dev-mode`
path remains for local iteration only (`production_safe: false` in metadata).
See [`docs/trusted-setup.md`](trusted-setup.md).

---

## 4. Known unaudited paths

Working list; update as work lands.

* **`xark build` / `xark test` execute the target circuit crate's code.**
 Compiling a circuit runs its `build.rs`, any proc-macros, and (for `xark
 test`) its test harness with the host toolchain — i.e. arbitrary code
 execution, exactly like a plain `cargo build`. Treat a circuit crate as
 trusted source; do not run `xark build`/`test` on an untrusted crate.

* **Lowering pipeline not formally verified end to end.** Gadget *relations*
 are mechanised in Lean (`formal/` — non-native field arithmetic, the curve
 laws, ECDSA/EdDSA soundness, on-curve membership), and a cargo-fuzz harness
 (`crates/tests/tests/fuzz.rs`) covers the parsers and the IR→R1CS lowering.
 But the MIR→xark-IR→R1CS *pipeline itself* is not proof-assistant-verified;
 it rests on unit tests, KAT cross-checks against reference crates (`sha2`,
 `keccak`, `blake2`, `blake3`, `aes`, arkworks Grumpkin), and adversarial
 forged-witness tests.

* **Solana on-chain verifier.** `crates/verifier/` is tested in Mollusk
 on the real `alt_bn128` syscalls (`crates/tests/tests/sbpf.rs` — positive
 across every committed circuit plus on-chain negative tests) and with
 adversarial fuzzing (`crates/tests/tests/fuzz.rs`).
 **Never deployed to mainnet**; not externally audited.

* **Poseidon2 parameters.** Vendored verbatim from the standard reference
 Poseidon2-BN254 parameter set into `crates/xark-poseidon2`.
 **Not independently re-derived.** A regression in the upstream reference
 table ships here unchanged.

* **AES S-box decomposition.** Algebraic `x * x_inv = 1 - is_zero`, not the
 Boyer-Peralta straight-line program. Exhaustively cross-checked against
 `aes` on all 256 inputs (`sbox_all_inputs_match_table`,
 `gf256_inv_roundtrips`, `sbox_zero_input_special_case`) but the algebraic
 uniqueness argument has **not been independently audited**.

* **Grumpkin embedded-curve arithmetic.** The shipped `scalar_mul` /
 `multi_scalar_mul` use an **offset double-and-add** accumulator over the
 incomplete affine `ec_add` / `ec_double` (`crates/xark-grumpkin`) — sidestepping
 the exceptional cases rather than a complete-addition selector polynomial. The
 curve algebra and on-curve membership are mechanised in `formal/Formal/Curve.lean`
 (`enforce_on_curve_grumpkin_sound`), and inputs are now range-/on-curve-checked
 (`enforce_on_curve`); the offset construction itself is tested against reference
 vectors but not separately proven.

* **Trusted-setup ceremony.** Implemented end-to-end (ptau ingest,
 phase-2 derivation, MPC driver) and cross-checked against snarkjs, but the
 ceremony code itself has **not been externally audited**, and a real
 deployment's security still rests on the off-chain conduct of the ceremony
 (honest participants, transcript integrity).

* **`RecursiveAggregation`.** Rejected. BN254 doesn't form a cycle
 with itself; supporting recursion requires a curve cycle.

* **ECDSA-secp256k1 / -secp256r1.** Not implemented; rejected.

* **Side-channel safety of the prover.** Out of scope per
 [§1](#1-threat-model).

---

## 5. Release-gating checklist

This is the literal checklist a release engineer should walk through
before tagging a production release of a circuit deployed via xark.

* [ ] **Toolchain pinned.** The nightly toolchain the `xark` tool builds
 circuits with is pinned (`rust-toolchain.toml`) and matches the one used
 to produce the deployed circuit — MIR extraction is nightly-only and its
 shape can drift across nightlies.
* [ ] **All gadgets used by the target circuit have a KAT test.** Enumerate
 the gadget crates the circuit depends on and cross-reference each against
 [§2](#2-per-gadget-soundness-sketches).
* [ ] **`circuit_hash` is recorded in deployed metadata** and matches what
 the verifier (both the host-side `verify` command and the on-chain
 programs) expects.
* [ ] **Setup mode is not `insecure-dev-mode`.** Check
 `metadata.json`'s `setup_mode` field — for production it must be
 `"phase2-from-ptau"` (or whatever a production mode ships) and
 `production_safe: true`.
* [ ] **`deterministic_rng_seed` is `null` in production metadata.** A
 non-null seed means the operator chose reproducibility, which is
 acceptable only in dev/test artifacts.
* [ ] **Public input order matches the verifier's expected order.**
 Run the end-to-end verify against the deployed verifier with the
 canonical `public_inputs.json` from the build.
* [ ] **Constraint count has been benchmarked and matches a recorded
 baseline.** Sudden changes in constraint count without a corresponding
 change in the source artifact indicate either a backend regression or
 an artifact regression.
* [ ] **Tampered-input integration tests cover every public input.** For
 each public input `p_i`, an integration test flips `p_i` and asserts
 the verifier returns false.
* [ ] **Solana verifier program ID matches the deployed `.so`.** Re-build
 the verifier with `cargo build-sbf` and confirm the program ID hash
 matches the deployed program's on-chain hash.
* [ ] **Operator has read [§4](#4-known-unaudited-paths)** and explicitly
 acknowledged each item that touches the deployed circuit.

---

## 6. Recommended audit scope

External auditors should focus first on:

1. **The lowering layer** — `crates/xark-ir/` and
 `crates/xark-prover/` (MIR → xark-IR → R1CS) plus every gadget crate
 (`crates/xark-*`). This is the layer that turns circuit
 semantics into R1CS rows; a bug here is a soundness break in every
 downstream circuit. The load-bearing sub-claims are
 [§2.2](#22-decompose_into_bits-range-gadget) (the 253-bit boundary),
 [§2.11](#211-aes-128-encryption) (the algebraic S-box decomposition),
 [§2.12](#212-grumpkin-curve-point-add--msm) (the selector
 polynomial), and [§2.10](#210-poseidon2-permutation) (parameter-set
 inheritance from the reference spec).
2. **The serialization layer** — `crates/backend/src/serialization.rs`
 and `crates/backend/src/solana.rs`. Any byte-layout drift here would
 silently cause the on-chain verifier to read a different proof than the
 one the prover produced. The little-endian G2 `(c0, c1)` component order
 and the 32-byte LE limb encoding in the Solana exporter
 (`encode_g2_le` / `assemble_*_bytes_le`) are the easiest places to get
 wrong; the round-trip tests in `solana::tests` pin them.
3. **The on-chain verifier program** —
 `crates/verifier/src/verifier.rs`. The instruction-data
 parser (`split_instruction_data`), the pairing input assembly, and the
 pre-negated `A` convention should all be reviewed against a concrete
 proof byte-for-byte.
