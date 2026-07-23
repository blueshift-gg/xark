# Security Review Checklist

The release-gating soundness walk-through for xark's Groth16 backend.

Two audiences: (1) a release engineer ticking [§5](#5-release-gating-checklist)
before shipping; (2) an external auditor reading
[§2](#2-per-gadget-soundness-sketches) for load-bearing claims to attack. Every
claim points into the codebase; when the implementation drifts, *update this
document*. Design notes: [`architecture.md`](architecture.md),
[`serialization.md`](serialization.md), [`trusted-setup.md`](trusted-setup.md).

## 1. Threat model

### What the prover can do

The prover is fully adversarial and may:

* construct any assignment to private witnesses;
* lie about hint/advice outputs (inverses, bit decompositions, quotients/remainders)
  supplied via `hint_*` primitives;
* craft public inputs that don't match the circuit's intended semantics;
* attempt a proof for a statement the verifier rejects.

We do **not** model: the prover obtaining the trusted-setup trapdoor
(τ, α, β, γ, δ) — anyone with these can forge proofs for any statement (standard
Groth16 assumption); nor the prover compromising the verifier's view of
`(VK, public_inputs)` (transport integrity is out of scope).

### What the verifier consumes

Only `(verifying_key, proof, public_inputs)`. Claims below are conditional on those
three being the ones xark produced from a fixed, audited artifact.

### Groth16 as a soundness oracle

We treat the pairing equation `e(A, B) = e(α, β) * e(vk_x, γ) * e(C, δ)` as a sound
NIZK argument of knowledge for satisfaction of the R1CS we emitted, modulo
discrete-log assumptions on BN254 and the trusted-setup assumption. **What we
constrain into the R1CS is enforced; what we leave outside is unconstrained and the
prover chooses freely.** So the soundness argument reduces to: *for every gadget, the
emitted R1CS constraints imply the claimed input/output relation.*

### Trusted setup

We assume τ (Powers-of-Tau toxic waste) and the circuit-specific γ, δ were and remain
unknown to the prover. α, β, γ, δ are public in the VK. See [§3](#3-trusted-setup).

### Out of scope

We are explicitly *not* defending against:

* **A circuit/gadget that leaves a hint output unconstrained.** Our hint model
  assumes every `hint_*` output witness is pinned by surrounding R1CS constraints
  (see [§2.16](#216-hint-outputs-advice)); constraining every hint value is the
  author's/gadget's responsibility.
* **A future Arkworks Groth16 regression.** We pin via Cargo.lock; bumping
  `ark-groth16` requires re-verifying the serialization round-trip test
  (`gadgets/tests/tests/serialization.rs`).
* **Side-channel leakage in the prover.** No constant-time guarantees; do not run the
  prover on untrusted hardware.
* **Side-channel leakage in trusted-setup randomness.** `OsRng` is a primitive; if
  host entropy is compromised, so is the setup.
* **Curve-level attacks on BN254.** ~100 bits against Special TNFS; consumers needing
  more should not use BN254 Groth16.

## 2. Per-gadget soundness sketches

Each gadget lives in its own `xark-*` crate. Each states the relation enforced, the
R1CS rows emitted, and why the rows imply the relation over `Fr = BN254 scalar field`.

### 2.1 `enforce_boolean`

`gadgets/xark-bits/src/lib.rs`. **Relation:** any satisfying assignment has
`x ∈ {0, 1}`. **Constraint:** `x * (x - 1) = 0`. **Argument:** `Fr` is a prime field
(integral domain); `X·(X−1)` has roots exactly `{0,1}`, so the row holds iff
`x ∈ {0,1}`. **Cost:** 1.

### 2.2 `decompose_into_bits` (range gadget)

`gadgets/xark-bits/src/lib.rs`. Constant `MAX_BITS = 253`.

**Relation.** For `value_var` and width `n ≤ MAX_BITS`, allocates booleans
`b_0..b_{n-1}` with `b_i ∈ {0,1}` and `Σ 2^i·b_i = value_var`.

**Constraints.** `n` boolean checks ([§2.1](#21-enforce_boolean)) + one recompose
`Σ 2^i·b_i − value_var = 0`.

**Argument.** Each `b_i ∈ {0,1}` by §2.1; the linear constraint makes `value_var` the
little-endian integer of those bits. Uniqueness needs `[0, 2^n−1]` to inject into
`Fr`. BN254 scalar field order `r ≈ 2.188×10^77 < 2^254`, so `n ≤ 253` keeps
`2^n ≤ 2^253 < r` and the bit pattern is unique.

**Boundary (load-bearing).** With `n ≥ 254` a prover could find two distinct patterns
in `[0, 2^n−1]` with `Σ 2^i·b_i ≡ value_var (mod r)` (both `value_var` and
`value_var + r` decomposable), breaking every consumer (XOR, AND, range checks). The
`MAX_BITS = 253` constant is load-bearing; **do not raise it.**

**Cost.** `n + 1`.

### 2.3 32-bit XOR (`xor`)

`gadgets/xark-bits/src/lib.rs`. **Relation:** `out.bits[i] = a.bits[i] XOR b.bits[i]`,
inputs boolean by prior decomposition. **Per bit:** allocate `out_i`, enforce boolean
(§2.1), and `(2·a_i)·b_i = a_i + b_i − out_i`. **Argument:** rearranged,
`out_i = a_i + b_i − 2·a_i·b_i`, which tabulates to the XOR table for boolean inputs:

| `a_i` | `b_i` | `a_i+b_i−2a_i b_i` |
|---|---|---|
| 0 | 0 | 0 |
| 0 | 1 | 1 |
| 1 | 0 | 1 |
| 1 | 1 | 0 |

The extra boolean check on `out_i` is redundant here but defends a future non-boolean
caller. **Cost:** 64/word (32 bool + 32 mul). **KAT:**
`gadgets::bitwise::tests::xor_matches_native_random`, `xor_n_matches_native_random_widths`.

### 2.4 32-bit AND (`and`)

`gadgets/xark-bits/src/lib.rs`. **Relation:** `out.bits[i] = a_i AND b_i`.
**Per bit:** `a_i * b_i = out_i` (product of booleans is boolean, so no extra boolean
check). **Cost:** 32/word. **KAT:** `and_matches_native_random`,
`and_n_matches_native_random_widths`.

### 2.5 32-bit ADD mod 2^32 (`add_mod_32`)

`gadgets/xark-bits/src/lib.rs`. **Relation:** sum mod `2^32` of up to `MAX_TERMS = 8`
32-bit words. **Constraints:** 32 boolean result bits + 3 boolean carry bits (35
checks) + one linear
`Σ_terms Σ_i 2^i·a_i = Σ_{i<32} 2^i·result_i + Σ_j 2^{32+j}·carry_j`.
**Argument:** bits boolean by §2.1; LHS ≤ `8·(2^32−1) < 2^35`, RHS ≤ `2^35`, both in
`[0, r)`, so the 35-bit decomposition is unique (§2.2) and `result` is the low 32 bits
of the integer sum. **Cost:** 36. **KAT:** `add_mod_32_matches_native`,
`add_mod_32_constraint_fails_on_bad_witness` (adversarial).

### 2.6 SHA-256 compression

`gadgets/xark-sha256/src/lib.rs`. `K256[0..64]` and schedule mirror NIST FIPS 180-4
§6.2. **Relation:** 16-word block + 8-word state → post-compression state.
**Constraints:** composition of §2.3/§2.4/§2.5 plus `rotr`, `shr`, `not` (pure index
permutations / bit complements emitting *zero* constraints). **Argument:** the
composition is FIPS 180-4 character-for-character (`σ0/σ1` message schedule; `Σ0/Σ1`,
`Ch`, `Maj` working-state updates; final `state[i]+working[i] mod 2^32`); every
primitive is sound by §2.1–§2.5 and permutation ops can't introduce unsoundness, so
the unique satisfying assignment is FIPS 180-4 compression. **KAT:**
`compression_matches_sha2_crate_on_abc_block` (vs `sha2::compress256`).

### 2.7 Keccak-f[1600]

`gadgets/xark-keccak/src/lib.rs`. 24 rounds over a 5×5 array of 64-bit lanes;
θ/ρ/π/χ/ι. **Argument:** θ and χ reduce to per-bit XOR (+ one AND for χ); ρ (fixed
rotation), π (fixed lane permutation) emit no constraints; ι XORs a constant into lane
(0,0). All constraints are 64-bit generalizations of §2.3/§2.4 + boolean/range
primitives; round constants are `RC[0..24]` from FIPS 202. **KAT:**
`in_circuit_zero_state_matches_kat` (vs `keccak` crate), `in_circuit_random_state_matches_native`.

### 2.8 Blake2s

`gadgets/xark-blake2s/src/lib.rs`. Blake2s compression (10 rounds, 32-bit lanes, G
mixing) + streaming wrapper (variable input → 32 bytes). **Argument:** same recipe as
SHA-256 — G reduces to `xor`, `add_mod_32`, fixed right-rotations (12, 7, 8, 16);
padding per the Blake2 spec (native cross-checked against `blake2` crate, then
in-circuit vs native). **KAT:** `blake2s_native_matches_blake2_crate_on_abc`,
`blake2s_in_circuit_matches_native_on_abc`, `blake2s_in_circuit_random_lengths`,
`blake2s_in_circuit_empty_input`.

### 2.9 Blake3

`gadgets/xark-blake3/src/lib.rs`. Single-chunk (`len ≤ CHUNK_BYTES = 1024`) and
multi-chunk via the standard binary-tree CV combination. **Argument:** compression
nearly identical to Blake2s with different mixing constants; single-chunk fast path,
multi-chunk computes per-chunk CVs and tree-combines per the BLAKE3 spec. **KAT:**
`blake3_native_matches_blake3_crate_on_abc`, `blake3_in_circuit_matches_native_on_abc`,
`blake3_in_circuit_block_boundaries`, `blake3_in_circuit_random_lengths`,
`blake3_in_circuit_rejects_oversized_input`.

### 2.10 Poseidon2 permutation

`gadgets/xark-poseidon2/src/lib.rs`. Constants are the standard reference
Poseidon2-BN254 parameter set, **vendored verbatim, not re-derived.** **Relation:**
`T = 4`, `R_F = 8` full rounds, `R_P = 56` partial rounds, S-box `x^5`, external matrix
`M_E`, internal matrix `M_I` (`INTERNAL_DIAG_HEX`). **Argument:** each `x^5` is three
R1CS muls (`t=x*x`, `u=t*t`, `out=u*x`), each pinning its output; linear layers fold
into LCs with one fresh witness per state cell per round to bound LC size. Field-native
(no bit decomposition), so the only soundness-relevant arithmetic is R1CS-native mul/add.
**Load-bearing:** the parameter set — if the upstream reference table has a soundness
bug, we inherit it. **KAT:** `native_matches_external_kat_all_zeros`,
`in_circuit_matches_external_kat_all_zeros`, `in_circuit_matches_native_on_1_2_3_4`.

### 2.11 AES-128 encryption

`gadgets/xark-aes/src/lib.rs`. CBC mode, no padding — input length must be a positive
multiple of 16; PKCS#7 padding is the caller's responsibility. **Relation:** per-block
10-round AES-128 over GF(2^8). **Argument (S-box):** we do *not* use Boyer-Peralta;
algebraic decomposition:

1. Hint `x_inv = x^{-1}` in GF(2^8) (`x_inv = 0` when `x = 0`) via a witness.
2. Enforce `x·is_zero = 0` and `x_inv·is_zero = 0` for boolean `is_zero`. These pin
   `is_zero = (x == 0)` *only because `x ∈ [0,255]`* (guaranteed by the upstream byte
   bit-decomposition; without it `is_zero = 1` with `x ≠ 0` could satisfy).
3. 64 cross-products `p_{i,j} = bit_i(x)·bit_j(x_inv)` via 64 AND constraints.
4. Reduce the product mod `m(x) = x^8+x^4+x^3+x+1` to get bits of `x·x_inv`; enforce
   `= 1` if `x ≠ 0` else `0`, pinning `x_inv = x^{-1}` (or both 0).
5. Apply the AES affine transform to `x_inv`.

ShiftRows is a pure permutation (0 constraints); MixColumns/AddRoundKey are byte-wise
XOR with `xtime`; key expansion reuses the S-box and `Rcon`. **KAT:**
`aes_native_matches_aes_crate_on_fips197_kat`, `aes_in_circuit_matches_native_on_kat`,
`aes_in_circuit_two_block_cbc`, `sbox_all_inputs_match_table`, `gf256_inv_roundtrips`
(256-input exhaustive).

### 2.12 Grumpkin curve (point add + MSM)

`gadgets/xark-grumpkin/src/lib.rs`. Affine `(x, y, is_infinity)` on Grumpkin (base
field BN254 `Fr`). `ec_add_in_circuit` handles doubling, identity, inversion.
**Argument (selector witnesses):**

* `same_x ∈ {0,1}` pinned by `same_x·(x2−x1) = 0` + inverse hint
  `(x2−x1)·inv_dx = 1−same_x`, forcing `same_x = 1 ⟺ x1 = x2`. `same_y` analogous.
* `is_double = same_x ∧ same_y ∧ ¬lhs_inf ∧ ¬rhs_inf`,
  `is_inverse = same_x ∧ ¬same_y ∧ ¬lhs_inf ∧ ¬rhs_inf`, pinned via boolean AND chains.
* `lambda` from one of three formulas (doubling / inversion / general) by selector;
  then `x3 = lambda²−x1−x2`, `y3 = lambda·(x1−x3)−y1`.

The selector argument makes cases mutually exclusive and exhaustive; the inverse hints
are the load-bearing step (a wrong `same_x` makes row two unsatisfiable). MSM is
double-and-add over the scalar's `(lo, hi)` bit decomposition, each bit a conditional
add via `conditional_select_point`. **KAT:** `ec_add_native_matches_arkworks`,
`ec_add_in_circuit_matches_native_generic`, `ec_add_in_circuit_handles_doubling`,
`..._handles_infinity_lhs`, `..._handles_infinity_rhs`, `..._handles_inverse`,
`msm_in_circuit_single_point_small_scalar`, `msm_in_circuit_two_points`,
`random_scalars_match_native`.

### 2.13 Merkle membership (Poseidon)

`gadgets/xark-merkle/src/lib.rs`. Folds a Poseidon 2-to-1 compression
(`xark-poseidon`) up an authentication path. **Relation:** `node₀ = leaf`,
`nodeᵢ₊₁ = hash2(select bᵢ sᵢ nodeᵢ, select bᵢ nodeᵢ sᵢ)`, `merkle_verify` asserts
`node_DEPTH == root`. **Argument:** each `bᵢ` is boolean-constrained (`bᵢ·bᵢ == bᵢ`)
before gating the mux `select b t f = f + b·(t − f)`; a boolean bit makes this a genuine
conditional swap (no third value reachable), so the only prover freedom is the position
bit — the intended membership freedom. Compression determinacy is Poseidon's
(field-native); the fold allocates no advice. **FV:** `formal/Formal/Merkle.lean`
(`merkle_level_swap_sound`, `merkle_select_pair_preserved`) composed with
`poseidon_permutation_determined`; bridge `merkle_matches_lean_model`. **KAT:**
`xark-merkle`'s `tests/vec.rs` (honest path accepted; wrong root, tampered sibling,
non-boolean bit each rejected).

### 2.14 xark-IR arithmetic → R1CS lowering

**Files.** `crates/ir/` (arithmetic ops) and `crates/prover/` (R1CS synthesis).
**Relation.** Each assertion asserts
`q_c + Σ coef_k·w_k + Σ q_M_i·a_i·b_i = 0`; `require_eq(x, y)` lowers to the `x−y=0`
form. **Constraints (by mul-term count):**

* **0 mul terms:** `0 * 0 = -(linear + q_c)`, forcing `linear + q_c = 0`.
* **1 mul term `q_M·a·b`:** `a * (q_M·b) = -(linear + q_c)`.
* **`m > 1` mul terms:** allocate `t_i`, emit `a_i·b_i = t_i` each, then one linear row
  `Σ q_M_i·t_i + linear + q_c = 0`.

**Argument.** All three are equivalent to `expression = 0`; the `t_i = a_i·b_i` rows
uniquely determine each `t_i` from the witness, so the final row evaluates to the
original expression as a field-element identity.

### 2.15 Public input ordering

**Files.** `crates/prover/` (synthesis) and `crates/ir/` (variable table, each
`Public` var recorded in declaration order). **Relation:** the verifier consumes public
inputs in the *exact same order* the prover provided; a mismatch would silently accept a
proof for a different statement. **Argument:** the prover allocates public-input
variables in signature order **before any arithmetic constraint is lowered**, so the
Arkworks R1CS matches the verifier's expected order. The circuit hash folds public-input
variable indices, so any reorder changes circuit identity. **Tests:**
`lower::tests::circuit_hash_changes_with_public_input_order`. (A prior end-to-end
public-input tamper matrix was removed on this branch; restoring it is a tracked
follow-up.)

### 2.16 Hint outputs (advice)

**Where.** `hint_*` primitives (`Field::hint_inverse`, `hint_bits`) in `crates/lang/`
(the `lang` module) and their witness-solver counterparts in `crates/prover/`.
**Relation.** A hint allocates a fresh witness the prover fills, with **no constraint at
the hint itself**. **Argument.** Soundness relies on a gadget-authoring invariant: every
hint output must also be referenced by ≥1 surrounding R1CS constraint that pins its value
(canonically "supply `w = x⁻¹` as advice, then require `x·w = 1`"). **If a gadget emits a
hint output that is not subsequently constrained, that witness is free and the proof is
unsound** — an explicit out-of-scope assumption per [§1](#1-threat-model): constraining
every hint value is the author's/gadget's responsibility.

## 3. Trusted setup

### Assumption restated

The VK contains group elements derived from the trapdoor `(τ, α, β, γ, δ)`.
**Soundness assumes the prover does not know any of these.** Knowing `τ` (phase-1)
breaks every circuit sharing the Powers-of-Tau ceremony; knowing `(γ, δ)` (phase-2,
circuit-specific) breaks only that circuit.

### Current state

| Setup mode | Randomness | `production_safe` | metadata `setup_mode` |
|---|---|---|---|
| `--insecure-dev-mode` | `OsRng` (default) or `ChaCha20Rng(seed)` if `--deterministic-rng <seed>` | `false` | `"insecure-dev-mode"` |
| `xark setup --ptau-file` | snarkjs Powers-of-Tau (phase-1) + one phase-2 contribution | `true` | `"phase2-from-ptau"` |
| `xark ceremony …` | snarkjs Powers-of-Tau (phase-1) + multi-contributor phase-2 MPC | `true` | `"phase2-from-ptau+mpc[N contributors]"` |

`KeyMetadata` (`crates/backend/src/keys.rs`) includes: `setup_mode: String`;
`production_safe: bool` (`false` for any dev-mode key); `deterministic_rng_seed:
Option<u64>` (present only when the operator chose reproducibility); `ptau_source:
Option<String>`; `phase2_seed_hash: Option<String>` — SHA-256 of the seed used to derive
`(γ, δ)`; **the seed itself must be discarded immediately after setup.**

### Dev-mode trapdoor lifecycle

In `--insecure-dev-mode` the trapdoor exists transiently in process memory during
`ark-groth16`'s `circuit_specific_setup`. The only durable artifacts are the proving key
(trapdoor *exponentiated into group elements*, not the scalar) and VK; recovering the
trapdoor requires solving discrete log on BN254. Still insufficient for production: the
operator is a single point of failure, there's no public transcript, and
`production_safe: false` should be rejected by any production deployment script.

### Production setup

Requires a Powers-of-Tau transcript plus a phase-2 contribution. Both **implemented**:
`ptau.rs` parses snarkjs `.ptau` (with admissibility checks), `setup_phase2.rs` derives a
phase-2 setup, `ceremony.rs` drives a multi-contributor MPC (Schnorr PoKs +
δ-consistency), via `xark ceremony {init,contribute,verify,finalize}`. The
`--insecure-dev-mode` path is local-only (`production_safe: false`). See
[`docs/trusted-setup.md`](trusted-setup.md).

## 4. Known unaudited paths

* **`xark build`/`test` execute the circuit crate's code.** Compiling runs `build.rs`,
  proc-macros, and (for `xark test`) the test harness with the host toolchain — arbitrary
  code execution, like plain `cargo build`. Treat a circuit crate as trusted source; do
  not run `xark build`/`test` on an untrusted crate.
* **Lowering pipeline not formally verified end to end.** Gadget *relations* are
  mechanised in Lean (`formal/` — non-native field arithmetic, curve laws, ECDSA/EdDSA
  soundness, on-curve membership), and a cargo-fuzz harness
  (`gadgets/tests/tests/fuzz.rs`) covers the parsers and IR→R1CS lowering. But the
  MIR→xark-IR→R1CS *pipeline itself* is not proof-assistant-verified; it rests on unit
  tests, KAT cross-checks (`sha2`, `keccak`, `blake2`, `blake3`, `aes`, arkworks
  Grumpkin), and adversarial forged-witness tests.
* **Solana on-chain verifier.** `crates/verifier/` is tested in Mollusk on the real
  `alt_bn128` syscalls (`gadgets/tests/tests/sbpf.rs` — positive across every committed
  circuit plus on-chain negatives) and fuzzed (`fuzz.rs`). **Never deployed to mainnet**;
  not externally audited.
* **Poseidon2 parameters.** Vendored verbatim from the standard reference
  Poseidon2-BN254 set into `gadgets/xark-poseidon2`. **Not independently re-derived.**
* **AES S-box decomposition.** Algebraic `x·x_inv = 1 − is_zero`, not Boyer-Peralta.
  Exhaustively cross-checked vs `aes` on all 256 inputs (`sbox_all_inputs_match_table`,
  `gf256_inv_roundtrips`, `sbox_zero_input_special_case`) but the algebraic uniqueness
  argument has **not been independently audited**.
* **Grumpkin embedded-curve arithmetic.** Shipped `scalar_mul`/`multi_scalar_mul` use an
  **offset double-and-add** accumulator over incomplete affine `ec_add`/`ec_double`
  (`gadgets/xark-grumpkin`), sidestepping exceptional cases rather than a complete-add
  selector. Curve algebra + on-curve membership mechanised in `formal/Formal/Curve.lean`
  (`enforce_on_curve_grumpkin_sound`), inputs now range-/on-curve-checked
  (`enforce_on_curve`); the offset construction is tested against reference vectors but
  not separately proven.
* **Trusted-setup ceremony.** Implemented end-to-end (ptau ingest, phase-2 derivation,
  MPC driver) and cross-checked against snarkjs, but **not externally audited**; a real
  deployment's security still rests on off-chain conduct (honest participants, transcript
  integrity).
* **`RecursiveAggregation`.** Rejected — BN254 doesn't form a cycle with itself.
* **ECDSA-secp256k1 / -secp256r1.** Not implemented; rejected.
* **Side-channel safety of the prover.** Out of scope per [§1](#1-threat-model).

## 5. Release-gating checklist

Walk through before tagging a production release of a circuit deployed via xark:

* [ ] **Toolchain pinned.** The nightly the tool builds circuits with is pinned
  (`rust-toolchain.toml`) and matches the one used for the deployed circuit — MIR
  extraction is nightly-only and its shape can drift across nightlies.
* [ ] **All gadgets used have a KAT test.** Enumerate the gadget crates and
  cross-reference [§2](#2-per-gadget-soundness-sketches).
* [ ] **`circuit_hash` recorded in deployed metadata** and matches what the verifier
  (host `verify` + on-chain programs) expects.
* [ ] **Setup mode is not `insecure-dev-mode`.** `metadata.json`'s `setup_mode` must be
  `"phase2-from-ptau"` (or a production mode) and `production_safe: true`.
* [ ] **`deterministic_rng_seed` is `null` in production metadata.** Non-null means the
  operator chose reproducibility — dev/test only.
* [ ] **Public input order matches the verifier's.** Run end-to-end verify against the
  deployed verifier with the `instruction_data.bin` emitted by `xark prove`.
* [ ] **Constraint count benchmarked vs a recorded baseline.** Sudden change without a
  source change indicates a backend or artifact regression.
* [ ] **Tampered-input tests cover every public input.** For each `p_i`, a test flips it
  and asserts verify returns false.
* [ ] **Solana verifier program ID matches the deployed `.so`.** Re-build with
  `cargo build-sbf` and confirm the on-chain hash matches.
* [ ] **Operator has read [§4](#4-known-unaudited-paths)** and acknowledged each item
  touching the deployed circuit.

## 6. Recommended audit scope

External auditors should focus first on:

1. **The lowering layer** — `crates/ir/` and `crates/prover/` (MIR → xark-IR → R1CS)
   plus every gadget crate. A bug here is a soundness break in every downstream circuit.
   Load-bearing sub-claims: [§2.2](#22-decompose_into_bits-range-gadget) (253-bit
   boundary), [§2.11](#211-aes-128-encryption) (algebraic S-box),
   [§2.12](#212-grumpkin-curve-point-add--msm) (selector polynomial),
   [§2.10](#210-poseidon2-permutation) (parameter-set inheritance).
2. **The serialization layer** — `crates/backend/src/serialization.rs` and `solana.rs`.
   Byte-layout drift would silently make the on-chain verifier read a different proof.
   The little-endian G2 `(c0, c1)` component order and the 32-byte LE limb encoding
   (`encode_g2_le` / `assemble_*_bytes_le`) are the easiest to get wrong; round-trip
   tests in `solana::tests` pin them.
3. **The on-chain verifier** — `crates/verifier/src/verifier.rs`. The instruction-data
   parser (`split_instruction_data`), pairing input assembly, and the pre-negated `A`
   convention should be reviewed against a concrete proof byte-for-byte.
