# Formal verification plan

The testing we have (cross-implementation differential, fuzzing, many-witness,
completeness + binding) raises confidence but is still *finite-input*. Formal
verification is the only way to get *all-input* guarantees. This is a proposal —
scoped by leverage, with realistic tooling — not a commitment.

## The trust stack, and where proof effort pays off

A proof verifying on-chain means: *the prover knew a satisfying assignment to
**our** R1CS*. For that to mean what we want ("the prover knew a valid Noir
execution"), three layers must each be correct:

| # | Layer | Failure if wrong | Tractability |
|---|-------|------------------|--------------|
| A | On-chain verifier (Rust): parsing, canonicality, no-panic, the pairing equation | accepts an invalid proof / panics (DoS) | **High** — small, bounded |
| B | ACIR→R1CS lowering + gadgets: R1CS satisfiable **iff** ACIR satisfiable | under-constraint → forge a false statement; over-constraint → DoS valid users | **Low–Med** — the hard, high-value target |
| C | Groth16 protocol soundness over BN254 | the scheme itself is broken | Out of scope — rely on published proofs |

Layer C we do **not** re-prove: cite the Groth16 soundness results and existing
mechanizations; our job is to use the scheme correctly, which is A.

## Layer A — the on-chain verifier (highest ROI, do first)

Small, self-contained Rust over fixed-size byte buffers — a good fit for
**Kani** (Rust bounded model checker, CBMC backend) or **Creusot**/**Prusti**
(deductive verification).

Properties to prove for `verify_groth16` / `verify_proof_only` / `VerifyingKey::verify`:
1. **Totality / no panic** for *all* inputs (no OOB index, no slice panic,
 no integer overflow). Kani proves this directly over symbolic byte slices.
2. **Fail-closed**: every structural error path returns `Err`/`Ok(false)`, never
 `Ok(true)`. (The entrypoint already maps `≠ Ok(true)` → reject.)
3. **Canonicality**: `scalar_is_canonical(s) ⇔ s < r` (prove the byte comparator
 matches the integer comparison against the field order). Easy SMT lemma.
4. **Length/arity**: the accepted byte-length set is exactly
 `{448 + 64·(N+1)}` × proof(256) × inputs(32·N) with `ic_count = N+1`.

Effort: **weeks**, mostly mechanical. Tooling: Kani (best ergonomics for #1–#2),
plus a small SMT lemma for #3. This eliminates the entire "verifier code bug"
class — the part an attacker most directly touches.

The pairing-equation *math* (`e(-A,B)·e(α,β)·e(vk_x,γ)·e(C,δ)=1`) is delegated
to the `alt_bn128` syscalls; we don't re-prove the pairing, but we should prove
our *operand assembly* equals the intended equation (a rewrite check, doable in
the same framework).

## Layer B — the lowering and gadgets (the hard, valuable part)

The property that matters is **soundness of the lowering**: for every ACIR
circuit, the produced R1CS is satisfiable by an assignment *iff* the ACIR is, and
the public outputs coincide. The dangerous direction is *under-constraint* — an
R1CS that accepts assignments the ACIR would reject. This is undecidable in
general, but tractable per-gadget. Three complementary tracks, cheapest first:

1. **R1CS determinism / under-constraint analysis (automated, do next).**
 The core soundness property of a gadget's R1CS is *functional determinism*:
 given the input wires, every other wire is uniquely determined. Tools exist:
 - **Ecne** (QED²) — proves R1CS "uniquely determined" via Gröbner/propagation.
 - **Picus** (from the circom/Picus line) — SMT-based under-constraint detector.
 Plan: export each gadget's R1CS (we already extract `to_matrices()`), run a
 determinism checker, and treat "not proven deterministic" as a finding to
 audit. This is **automated** and catches the exact bug class our single-
 variable probe could only spot-check. Effort: **weeks** (mostly export +
 tool wiring); some gadgets may need manual lemmas.

2. **Per-gadget functional correctness (semi-automated).**
 For each gadget (sha256, keccak, blake, aes, ecdsa, poseidon, range, bitwise),
 prove the constrained relation equals the reference spec. Options:
 - SMT/bit-blasting for the bit-oriented gadgets (sha256/keccak/blake/aes are
 boolean circuits — well-suited to a SAT/SMT equivalence check against a
 reference boolean spec).
 - A proof assistant (**Lean 4** is the pragmatic choice given momentum and the
 `mathlib` BN254 field support, or Coq) for the field-arithmetic gadgets
 (ecdsa, curve, poseidon) where bit-blasting blows up.
 Effort: **months**, gadget-by-gadget; prioritize the ones with the largest
 constraint footprint and the most arithmetic subtlety (ecdsa, poseidon).

3. **Lowering-engine correctness (deepest).**
 Prove the ACIR-opcode → R1CS translation rules themselves sound (each opcode
 lowering preserves semantics), so correctness composes to *any* circuit, not
 just the committed gadgets. This is a mechanized proof of `acir-r1cs`'s
 translation in a proof assistant against an ACIR semantics. Effort:
 **multi-month, research-grade**; highest assurance, lowest near-term ROI.

## Recommended sequencing

1. **Now / weeks:** Kani on Layer A (totality, fail-closed, canonicality). Cheap,
 eliminates the most attacker-reachable bug class, integrates into CI.
2. **Next / weeks:** wire R1CS determinism checking (Ecne/Picus) over every
 gadget's extracted matrices — automated under-constraint coverage, the thing
 our probe can't fully do.
3. **Then / months:** per-gadget functional equivalence, bit-blasting the
 boolean hash/aes gadgets first (most automatable), proof-assistant for the
 arithmetic gadgets.
4. **Long-term:** mechanize the lowering rules for all-circuit soundness.

In parallel (engineering, not FV, but complementary): external audit, and
extend the differential + many-witness harnesses to all gadgets with computed
expected outputs.

## What this does **not** buy

Even full Layer-A+B verification leaves: the trusted setup (a ceremony concern,
not code — see `docs/trusted-setup.md`), bugs in arkworks / the `alt_bn128` syscalls /
`nargo`'s ACVM (dependencies we trust), and side channels. FV raises the floor
dramatically; it is not a substitute for the ceremony or for trusting the
underlying primitives.
