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

### Proofs are not unique (replay)

A Groth16 proof attests to a statement (the public inputs), not to one byte
string: anyone holding a valid proof can re-randomize it into a different valid
proof of the same public inputs, without any secret. The verifier's `*_strict`
entry points reject non-canonical *encodings* of the proof's points; they can't
reject a re-randomized proof, which is canonical. So an application must never
use proof bytes (or their hash) as a replay or "already used" key. Replay
protection belongs in the public inputs: a nullifier or nonce the circuit
derives from a secret, or the signer or context the proof is for, recorded by
the application. The generated verifier crate's README says the same.

### Trusted setup

We assume τ (Powers-of-Tau toxic waste) and the circuit-specific γ, δ were and remain
unknown to the prover. α, β, γ, δ are public in the VK. See [§3](#3-trusted-setup).

### Out of scope

We are explicitly *not* defending against:

* **A circuit/gadget that leaves a hint output unconstrained.** Our hint model
  assumes every `hint_*` output witness is pinned by surrounding R1CS constraints
  (see [§2.16](#216-hint-outputs-advice)); constraining every hint value is the
  author's/gadget's responsibility.
* **A future arkworks BN254 regression.** We pin `ark-bn254` / `ark-ff` / `ark-ec`
  via Cargo.lock; bumping them requires re-running the differential tests against
  `ark-groth16` (`crates/groth16/tests/prover.rs`) and the serialization round
  trip (`gadgets/tests/tests/it/serialization.rs`).
* **Side-channel leakage in the prover.** No constant-time guarantees; do not run the
  prover on untrusted hardware.
* **Side-channel leakage in trusted-setup randomness.** `OsRng` is a primitive; if
  host entropy is compromised, so is the setup.
* **Curve-level attacks on BN254.** ~100 bits against Special TNFS; consumers needing
  more should not use BN254 Groth16.

## 2. Per-gadget soundness sketches

Each gadget lives in its own `xark-*` crate. Each states the relation enforced, the
R1CS rows emitted, and why the rows imply the relation over `Fr = BN254 scalar field`.

### 2.1 Booleanity (`Field::require_bool`)

`crates/lang/src/lang.rs`. **Relation:** any satisfying assignment has
`x ∈ {0, 1}`. **Constraint:** `x * x = x`. **Argument:** `Fr` is a prime field
(integral domain); `X·(X−1)` has roots exactly `{0,1}`, so the row holds iff
`x ∈ {0,1}`. **Cost:** 1. **Lean:** `boolean_sound` in `formal/Formal/Gadgets.lean`.

### 2.2 `Field::to_bits` (range gadget)

`crates/lang/src/lang.rs`, lowered by `decompose_bits_gated` in
`crates/frontend/src/builder.rs`. Width cap `N ≤ 253`, a compile-time assertion.

**Relation.** For `x` and width `n ≤ 253`, outputs booleans `b_0..b_{n-1}` with
`Σ 2^i·b_i = x`, so `x < 2^n`.

**Constraints.** Bits `1..n−1` are hinted and pinned by `w·w = w`; bit 0 is the linear
form they leave, `b_0 = x − Σ_{i≥1} 2^i·b_i`, pinned by `b_0·(b_0 − 1) = 0`. The
recomposition is built into `b_0`, so no separate recompose row.

**Argument.** Each `b_i ∈ {0,1}` by §2.1, and `b_0`'s definition makes `x` the
little-endian integer of those bits. Uniqueness needs `[0, 2^n−1]` to inject into
`Fr`. BN254 scalar field order `r ≈ 2.188×10^77 < 2^254`, so `n ≤ 253` keeps
`2^n ≤ 2^253 < r` and the bit pattern is unique.

**Boundary (load-bearing).** With `n ≥ 254` a prover could find two distinct patterns
in `[0, 2^n−1]` with `Σ 2^i·b_i ≡ x (mod r)` (both `x` and `x + r` decomposable),
breaking every consumer (XOR, AND, range checks). The 253-bit cap is load-bearing;
**do not raise it.** (`Field::to_bits_canonical` covers all 254 bits by also requiring
the bits to spell a number `≤ r − 1`.)

**Cost.** `n` rows and `n − 1` new variables. **Lean:** `model_sound` in
`formal/Formal/ToBits.lean`, over the exported rows.

### 2.3 XOR (`Field::xor`, `xark_bits::xor32`)

`crates/lang/src/lang.rs` (`Field::xor`, emitted by `emit_xor` in
`crates/frontend/src/builder.rs`); `gadgets/xark-bits/src/lib.rs` (word layer).
**Relation:** `out_i = a_i XOR b_i`, inputs boolean by prior decomposition. **Per
bit:** one row `(2·a_i)·b_i = a_i + b_i − out_i`, with `out_i` a fresh variable.
**Argument:** rearranged, `out_i = a_i + b_i − 2·a_i·b_i` for any field inputs (no
prover freedom in `out_i`), which tabulates to the XOR table for boolean inputs:

| `a_i` | `b_i` | `a_i+b_i−2a_i b_i` |
|---|---|---|
| 0 | 0 | 0 |
| 0 | 1 | 1 |
| 1 | 0 | 1 |
| 1 | 1 | 0 |

Booleanity of the inputs is **not** checked here: on non-boolean inputs the output is
determined but isn't XOR, so callers pass `to_bits` outputs or earlier bit gadgets'
results. With a constant operand the row folds to a linear form. The three-input
`xor3`, `maj3`, `ch` and `chi` are one row each, on the same input assumption.
**Cost:** 32/word. **Lean:** `formal/Formal/BoolOps.lean` (`xor`/`or`),
`formal/Formal/HashOps.lean` (the three-input rows).

### 2.4 AND (`Field::and`, `xark_bits::and32`)

`crates/lang/src/lang.rs`, `gadgets/xark-bits/src/lib.rs`. **Relation:**
`out_i = a_i AND b_i`. **Per bit:** `a_i * b_i = out_i` (product of booleans is
boolean, so no extra boolean check). **Cost:** 32/word.

### 2.5 ADD mod 2^32 (`add32`, `reduce::<N>`)

`gadgets/xark-bits/src/lib.rs`. **`add32`:** the two words' field sum (`< 2^33`) is
decomposed into 33 hinted bits, each pinned boolean, plus one recomposition equality;
the low 32 bits are the result. **`reduce::<N>`** (and `add3`, `reduce::<34>` over
three words): the low 32 bits of a sum `< 2^N`, `33 ≤ N ≤ 253`; bits `0..N−1` are
hinted and pinned boolean and the top carry `t` they leave is pinned by
`t·(t − 2^(N−1)) = 0`. **Argument:** bits boolean by §2.1; the sum is below `2^N ≤
2^253 < r`, so the decomposition is unique (§2.2) and `result` is the low 32 bits of
the integer sum. **Cost:** `add32` 34; `reduce::<N>` `N`. **Lean:**
`formal/Formal/Add32.lean`, `formal/Formal/Reduce.lean` (sound with no input
assumption).

### 2.6 SHA-256 compression

`gadgets/xark-sha256/src/lib.rs`. `K256[0..64]` and schedule mirror NIST FIPS 180-4
§6.2. **Relation:** 16-word block + 8-word state → post-compression state.
**Constraints:** `Σ`/`σ` are one `xor3` row per bit, `Maj` one `maj3` row, `Ch` one `ch`
row; modular sums are `reduce::<N>` (§2.5); `rotr`, `shr` are pure index permutations
emitting *zero* constraints. **Argument:** the composition is FIPS 180-4
character-for-character (`σ0/σ1` message schedule; `Σ0/Σ1`, `Ch`, `Maj` working-state
updates; final `state[i]+working[i] mod 2^32`); every primitive is sound by §2.1–§2.5
and permutation ops can't introduce unsoundness, so the unique satisfying assignment
is FIPS 180-4 compression. **KAT:** `sha256_matches_sha2` in
`gadgets/xark-bits/tests/hashes.rs` (vs the `sha2` crate, with an exhaustive witness
search for uniqueness).

### 2.7 Keccak-f[1600]

`gadgets/xark-keccak/src/lib.rs`. 24 rounds over a 5×5 array of 64-bit lanes;
θ/ρ/π/χ/ι. **Argument:** θ reduces to three-input XOR rows (`xor3`) and χ to one `chi`
row per bit; ρ (fixed rotation), π (fixed lane permutation) emit no constraints; ι XORs
a constant into lane (0,0). Round constants are `RC[0..24]` from FIPS 202. **KAT:**
`keccak256_matches_sha3` in `gadgets/xark-bits/tests/hashes.rs` (vs the `sha3` crate).

### 2.8 Blake2s

`gadgets/xark-blake2s/src/lib.rs`. Blake2s compression (10 rounds, 32-bit lanes, G
mixing) + streaming wrapper (variable input → 32 bytes). **Argument:** same recipe as
SHA-256 — G reduces to `xor32`, `add32`/`add3`, fixed right-rotations (16, 12, 8, 7);
padding per the Blake2 spec. **KAT:** `blake2s_matches_blake2` in
`gadgets/xark-bits/tests/hashes.rs` (vs the `blake2` crate).

### 2.9 Blake3

`gadgets/xark-blake3/src/lib.rs`. Single chunk only: the message is at most 1024
bytes, a compile-time assertion (multi-chunk tree hashing is not implemented).
**Argument:** compression nearly identical to Blake2s with different mixing constants
and message permutation, per the BLAKE3 spec. **KAT:** `blake3_matches_blake3` in
`gadgets/xark-bits/tests/hashes.rs` (vs the `blake3` crate).

### 2.10 Poseidon2 permutation

`gadgets/xark-poseidon2/src/lib.rs`. Constants are the Horizen Labs reference
Poseidon2-BN254 parameter set (`poseidon2_instance_bn256.rs`), **vendored verbatim, not
re-derived.** **Relation:** `T = 3`, `R_F = 8` full rounds, `R_P = 56` partial rounds,
S-box `x^5`, external matrix `M_E = circ(2,1,1)`, internal matrix `M_I` (diagonal
`[1,1,2]` − 1, i.e. `[[2,1,1],[1,2,1],[1,1,3]]`). **Argument:** each `x^5` is three
R1CS muls (`t=x*x`, `u=t*t`, `out=u*x`), each pinning its output; round constants and
both linear layers are linear and emit no rows (240 rows in all). Field-native (no bit
decomposition), so the only soundness-relevant arithmetic is R1CS-native mul/add.
**Load-bearing:** the parameter set — if the upstream reference table has a soundness
bug, we inherit it. **KAT:** `poseidon2_perm_matches_reference_vector`,
`poseidon2_perm_zero_input`, `native_perm_matches_reference_vectors`,
`native_matches_the_circuit` (`gadgets/xark-poseidon2/tests/vec.rs`).

### 2.11 AES-128/256 encryption

`gadgets/xark-aes/src/lib.rs`. AES-128 and AES-256 blocks, CTR mode and GCM; all are
forward-only (no inverse cipher). **Relation:** per-block 10-round AES-128 or 14-round
AES-256 over GF(2^8); GCM adds a GF(2^128) multiply (`gf128_mul`) for GHASH.
**Argument (S-box):** a select over the constant 256-byte FIPS-197 table (`sbox`, 34
rows): the one-hot of the low nibble (11 rows), a binary mux over the high nibble (15
rows), and `to_bits::<8>` of the selected byte (8 rows). The input bits must be
boolean (every caller passes `to_bits` or XOR outputs); the outputs are then exactly
`SBOX[x]`'s bits. `formal/Formal/AesSbox.lean` proves the select sound over its rows
and the table equal to `affine(x⁻¹)` in GF(2^8).

ShiftRows is a pure permutation (0 constraints); MixColumns/AddRoundKey are byte-wise
XOR with `xtime`; key expansion reuses the S-box and `Rcon`. **KAT:**
`aes128_matches_fips_kat`, `aes256_matches_fips_kat`, `sbox_matches_fips_table`
(all 256 inputs), `key_schedule_matches_fips`, `gf128_mul_matches_ghash`
(`gadgets/xark-aes/tests/vec.rs`).

### 2.12 Grumpkin curve (point add + MSM)

`gadgets/xark-grumpkin/src/lib.rs`. Affine `(x, y)` on Grumpkin `y² = x³ − 17` (base
field BN254 `Fr`); there is no point at infinity. `ec_add` / `ec_double` are
**incomplete** affine formulas: the slope is hinted and pinned by a guard
`denom · inv = 1`, unsatisfiable at `x1 = x2`, so an exceptional case can't be forged,
only refused. `scalar_mul`, `wide_scalar_mul` and `multi_scalar_mul` use an **offset**
accumulator with one fused double-and-add per bit over signed digits `±P` (the MSM adds
`±(P₀ ± P₁)` from a shared table), then add a compile-time correction `corr = −2^N·O`;
the fused step's second slope needs no guard because Grumpkin has no point with
`y = 0` (`formal/Formal/DoubleAdd.lean`). Points are pinned on the curve
(`enforce_on_curve`) and `scalar_mul` pins its bits boolean. An honest prover fails
when the result is the identity, on `P₀ = ±P₁` for the MSM, and otherwise only on
inputs that need `O`'s discrete log. Each is proven sound over its exported rows
(`formal/Formal/{ScalarMul,WideScalarMul,MultiScalarMul}.lean`). **KAT:**
`scalar_mul_matches_ark_grumpkin`, `wide_scalar_mul_matches_ark_grumpkin`,
`msm_matches_reference_vectors`, and the negatives
`scalar_mul_rejects_zero_off_curve_and_offset`, `scalar_mul_rejects_a_non_boolean_bit`,
`msm_rejects_degenerate_inputs` (`gadgets/xark-grumpkin/tests/vec.rs`).

### 2.13 Merkle membership (Poseidon)

`gadgets/xark-merkle/src/lib.rs`. Folds a Poseidon 2-to-1 compression
(`xark-poseidon`) up an authentication path. **Relation:** `node₀ = leaf`,
`nodeᵢ₊₁ = hash2(cond_swap(bᵢ, nodeᵢ, sᵢ))`, `merkle_verify` asserts
`node_DEPTH == root`, with `DEPTH` a const generic. **Argument:** `cond_swap` (halo2's
one-product swap) constrains `bᵢ·bᵢ == bᵢ` itself and outputs `a' = a + b·(s − a)`,
`s' = s − b·(s − a)`; a boolean bit makes this a genuine conditional swap (no third
value reachable), so the only prover freedom is the position bit — the intended
membership freedom. Compression determinacy is Poseidon's (field-native). **FV:**
`formal/Formal/CondSwap.lean`, over `cond_swap`'s exported rows: `soundness` (no input
assumption), `completeness` (a bit selector), and `root_binds` (the levels compute
`merkleRoot H leaf path`, assuming, not proving over `hash2`'s rows, that they compute a
function `H`, and that each level emits the template's rows); bridge `merkle_matches_lean_model`. **KAT:**
`xark-merkle`'s `tests/vec.rs` (honest path accepted; wrong root, tampered sibling,
non-boolean bit, and each tampered witness value rejected).

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
R1CS matches the verifier's expected order. The circuit digest folds every row's
variable indices, so a reorder that moves a public input changes the digest. **Tests:**
the `reorder_pi` example (public inputs interleaved with a private one) proves and
verifies on chain (`gadgets/tests/tests/sbpf.rs`); `reordering_variables_breaks_the_proof`
(`crates/groth16/tests/prover.rs`) checks a key doesn't fit a renumbered circuit.

### 2.16 Hint outputs (advice)

**Where.** `hint_*` primitives (`Field::hint_inverse`, `Field::hint_bit`, …) in `crates/lang/`
(the `lang` module) and their witness-solver counterparts in `crates/ir/src/solver.rs`.
**Relation.** A hint allocates a fresh witness the prover fills, with **no constraint at
the hint itself**. **Argument.** Soundness relies on a gadget-authoring invariant: every
hint output must also be referenced by ≥1 surrounding R1CS constraint that pins its value
(canonically "supply `w = x⁻¹` as advice, then require `x·w = 1`"). **If a gadget emits a
hint output that is not subsequently constrained, that witness is free and the proof is
unsound** — an explicit out-of-scope assumption per [§1](#1-threat-model): constraining
every hint value is the author's/gadget's responsibility.

### 2.17 Witness branches and witness-only regions

**Where.** `crates/frontend/src/{interp,host,builder}.rs`; semantics in
`crates/frontend/README.md` and [subset.md](subset.md#branches-on-witness-values).
**Branches.** Both arms of a witness `if` run; an arm's requirements are emitted as
`g · (a − b) = 0` and its hints pinned to 0 where it isn't taken (Lean: `gated_sat`,
`guard_mul`, `pin_dead`, `select_taken`). A requirement inside an arm is therefore
**vacuous when the arm isn't taken** — review that every check a circuit relies on
unconditionally sits outside any witness branch. **Witness-only regions**
(`witness_begin()`/`witness_end()`) emit no constraints at all: a value computed inside is
free until pinned afterwards, and a requirement inside is not enforced. The frontend's
memo tables — the bit-decomposition cache, select and product reuse, proven booleans,
proven bounds — are **only fed by emitted rows**, so recomputing a value after the region
constrains it afresh (`witness_regions_leave_no_proven_facts` in
`crates/lang/tests/snapshot.rs`). Native integer and `bool` ops, and `Field` comparisons
(their result is a `bool` later code trusts), keep their rows inside a region
(`witness_regions_keep_field_comparisons`). Each arm of a witness branch starts in the
region state the branch was reached in: an arm that diverges inside a region is dropped with
it, and a region that would straddle a branch is refused
(`witness_regions_end_with_a_diverging_arm`, `witness_regions_dont_straddle_branches`).
Review each region's outputs for a pin.

## 3. Trusted setup

### Assumption restated

The VK contains group elements derived from the trapdoor `(τ, α, β, γ, δ)`.
**Soundness assumes the prover does not know any of these.** Knowing `τ` (phase-1)
breaks every circuit sharing the Powers-of-Tau ceremony; knowing `(γ, δ)` (phase-2,
circuit-specific) breaks only that circuit.

### Current state

| Setup mode | Randomness | `production_safe` | metadata `setup_mode` |
|---|---|---|---|
| `xark setup` (no `.ptau`) | `OsRng`, or `ChaCha20Rng(seed)` with `--deterministic-rng <seed>` | `false` | `"single-party"` (`"insecure-dev-mode"` before 0.3) |
| `xark setup --ptau-file` | snarkjs Powers-of-Tau (phase-1) + one phase-2 contribution | `true` | `"phase2-from-ptau"` |
| `xark ceremony …` | snarkjs Powers-of-Tau (phase-1) + multi-contributor phase-2 MPC | `true` | `"phase2-from-ptau+mpc[N contributors]"` |

`KeyMetadata` (`crates/backend/src/keys.rs`) includes: `setup_mode: String`;
`production_safe: bool` (`false` for a key made without a `.ptau`); `deterministic_rng_seed:
Option<u64>` (present only when the operator chose reproducibility); `ptau_source:
Option<String>`; `phase2_seed_hash: Option<String>` — SHA-256 of the seed used to derive
`(γ, δ)`; **the seed itself must be discarded immediately after setup.**

### Single-party trapdoor lifecycle

Without a `.ptau`, the trapdoor exists transiently in process memory during
`xark-groth16`'s `dev_setup`. The only durable artifacts are the proving key
(trapdoor *exponentiated into group elements*, not the scalar) and VK; recovering the
trapdoor requires solving discrete log on BN254. So an `OsRng` key is a sound single-party
setup: it rests on trusting the operator, with no public transcript to show for it. A seeded key
(`--deterministic-rng`) is different: anyone with the seed recovers the trapdoor. `xark export`
accepts any key and records which it is in the verifier crate's `SETUP`: `single-party`,
`seeded` (with a warning), `ceremony` (two or more contributors; a ceremony of one is
`single-party`), or `unknown` when there is no `metadata.json`.

### Production setup

Requires a Powers-of-Tau transcript plus a phase-2 contribution. Both **implemented**:
`ptau.rs` parses snarkjs `.ptau` (with admissibility checks), `xark-groth16`'s
`phase2_setup` derives the phase-2 keys, `ceremony.rs` drives a multi-contributor MPC (Schnorr PoKs +
δ-consistency), via `xark ceremony {init,contribute,verify,finalize}`. A key made without a
`.ptau` gets `production_safe: false`, and `xark prove` takes `--deterministic-rng` only for
such a key. See
[`docs/trusted-setup.md`](trusted-setup.md).

## 4. Known unaudited paths

* **`xark build`/`test` execute the circuit crate's code.** Compiling runs `build.rs`,
  proc-macros, and (for `xark test`) the test harness with the host toolchain — arbitrary
  code execution, like plain `cargo build`. Treat a circuit crate as trusted source; do
  not run `xark build`/`test` on an untrusted crate.
* **Lowering pipeline not formally verified end to end.** Gadget *relations* are
  mechanised in Lean (`formal/` — non-native field arithmetic, curve laws, ECDSA/EdDSA
  soundness, on-curve membership), and a proptest harness
  (`gadgets/tests/tests/it/fuzz.rs`) covers the verifier's byte inputs and the
  `circuit.xbc` decoder. But the
  Rust→xark-IR→R1CS *pipeline itself* is not proof-assistant-verified (its
  constraint-reducing rewrites and branch guards are, in `formal/Formal/Rewrites.lean`);
  it rests on unit tests, KAT cross-checks (`sha2`, `keccak`, `blake2`, `blake3`,
  `aes`, arkworks Grumpkin), adversarial forged-witness tests, a native-semantics
  fuzzer whose every verdict is an exhaustive witness search
  (`crates/lang/tests/semantics_fuzz.rs`, `xark_ir::witness_search`), and the same
  search over every example's own test inputs and mutations of them
  (`cargo xtask difftest`, on every pull request in `slow.yml`). That includes the
  AES-CTR/GCM circuits and the whole **EdDSA** circuit (about 400k rows, scalar
  multiplication included: every valid signature has exactly one witness, every
  mutated input none), since none of them needs a non-native inverse. The
  **ECDSA** circuits do (their incomplete-affine point operations hint `λ` modulo a
  256-bit prime), which search can't decide, so they are checked in pieces: every
  building block at full size against native references
  (`signature_blocks_are_sound`, `aes_blocks_are_sound` in `snapshot.rs`), and the
  inverse-based point operations over small fields for both curve shapes
  (`small_field_curve_gadgets_are_sound`) and in Lean. What no search covers is how
  the ECDSA blocks are chained in the scalar-multiplication loop (see
  [§6](#6-recommended-audit-scope)); the known-answer and tamper tests cover it.
* **Solana on-chain verifier.** `crates/verifier/` is tested in Mollusk on the real
  `alt_bn128` syscalls (`gadgets/tests/tests/sbpf.rs` — positive across every committed
  circuit plus on-chain negatives) and fuzzed (`fuzz.rs`). **Never deployed to mainnet**;
  not externally audited.
* **Poseidon2 parameters.** Vendored verbatim from the standard reference
  Poseidon2-BN254 set into `gadgets/xark-poseidon2`. **Not independently re-derived.**
* **AES S-box.** A select over the constant FIPS-197 table (§2.11), proven sound over
  its rows in Lean (`formal/Formal/AesSbox.lean`) and checked on all 256 inputs
  (`sbox_matches_fips_table`), but **not independently audited**.
* **Grumpkin embedded-curve arithmetic.** `scalar_mul`, `wide_scalar_mul` and
  `multi_scalar_mul` (`gadgets/xark-grumpkin`) use an **offset** accumulator with one
  fused incomplete double-and-add per bit (signed digits; the MSM adds `±(P₀ ± P₁)` from a
  shared table), sidestepping exceptional cases with x-guards rather than a complete-add
  selector. Each is proven sound in Lean over its exact exported rows
  (`formal/Formal/{ScalarMul,WideScalarMul,MultiScalarMul}.lean`), including the offset
  corrections and, for `scalar_mul`, the booleanity of its bits.
* **Trusted-setup ceremony.** Implemented end-to-end (ptau ingest, phase-2 derivation,
  MPC driver), but **not externally audited**; a real
  deployment's security still rests on off-chain conduct (honest participants, transcript
  integrity).
* **ECDSA-secp256k1 / -secp256r1 and EdDSA-Ed25519.** Implemented
  (`gadgets/xark-secp256k1`, `xark-secp256r1`, `xark-ed25519`) by fake GLV over
  non-native 8×32-bit limbs; each gadget is proven sound over its rows, but the
  scalar-multiplication loop as a whole is not (see [§6](#6-recommended-audit-scope)).
  **Not externally audited.**
* **Side-channel safety of the prover.** Out of scope per [§1](#1-threat-model).

## 5. Release-gating checklist

Walk through before tagging a production release of a circuit deployed via xark:

* [ ] **Keys match the circuit.** The digest `xark build` prints for the deployed
  circuit is the one the keys were made from. It doesn't depend on the rustc
  version (see the toolchain policy in [toolchain.md](toolchain.md#toolchain-policy));
  `Cargo.lock` is committed so the xark version can't drift.
* [ ] **All gadgets used have a KAT test.** Enumerate the gadget crates and
  cross-reference [§2](#2-per-gadget-soundness-sketches).
* [ ] **`circuit_hash` recorded in deployed metadata** and matches what the verifier
  (host `verify` + on-chain programs) expects.
* [ ] **The setup is one the verifier's users can trust.** The exported crate's `SETUP` is
  `ceremony`, or `single-party` where trusting whoever ran setup is acceptable; never `seeded`
  or `unknown`.
* [ ] **`deterministic_rng_seed` is `null` in production metadata.** Non-null means the
  operator chose reproducibility — dev/test only.
* [ ] **Public input order matches the verifier's.** Run end-to-end verify against the
  deployed verifier with the `instruction_data.bin` `xark export` writes (the proof
  followed by the public inputs, in the circuit's order).
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

1. **The lowering layer** — `crates/frontend/`, `crates/ir/` and `crates/prover/` (wasm → xark-IR → R1CS)
   plus every gadget crate. A bug here is a soundness break in every downstream circuit.
   Load-bearing sub-claims: [§2.2](#22-fieldto_bits-range-gadget) (253-bit
   boundary), [§2.11](#211-aes-128256-encryption) (table-select S-box),
   [§2.12](#212-grumpkin-curve-point-add--msm) (offset accumulator and guards),
   [§2.10](#210-poseidon2-permutation) (parameter-set inheritance).
2. **The serialization layer** — `crates/backend/src/serialization.rs` and
   `crates/groth16/src/solana.rs` (re-exported by `crates/backend/src/solana.rs`).
   Byte-layout drift would silently make the on-chain verifier read a different proof.
   The little-endian G2 `(c0, c1)` component order and the 32-byte LE limb encoding
   (`encode_g2_le` / `assemble_*_bytes_le`) are the easiest to get wrong; round-trip
   tests in `solana::tests` pin them.
3. **ECDSA scalar multiplication** — the secp256k1 and secp256r1 fake-GLV verify loops
   (`ecdsa_verify_packed` in `xark-secp256k1`, `ecdsa_verify` in `xark-secp256r1`:
   fused `ec_double_add_k1`/`_r1` steps and a fixed-base comb). Each block is searched
   or proven, but not the loop as a whole: review that the offset accumulator and
   correction constants keep every incomplete addition away from its exceptional
   cases (`x₁ = x₂`) for every scalar, and the fake-GLV scalars' bounds
   (`fake_glv_check_k1`/`_r1`).
4. **The on-chain verifier** — `crates/verifier/src/verifier.rs`. The instruction-data
   split (`verify_proof_only`), pairing input assembly, and the pre-negated `A`
   convention should be reviewed against a concrete proof byte-for-byte.
