# Trusted-setup ceremony

Groth16 is only as sound as its trusted setup: whoever knows the phase-2
toxic waste (`τ`, `α`, `β`, `δ`) can forge proofs for *any* statement,
regardless of how correct the verifier is. The committed test vectors are
currently produced with `--insecure-dev-mode` (a recoverable trapdoor) and are
fine for tests, but production keys must come from a real multi-party ceremony.

xark runs the **circuit-specific phase 2** of the ceremony itself — no external
prover is in the loop:

* `xark setup --ptau-file … --phase2-seed …` derives the
  `ProvingKey`/`VerifyingKey` from a phase-1 transcript
  ([`xark_backend::ptau::setup_from_ptau`]); and
* `xark ceremony {init,contribute,verify,finalize}` drives the
  multi-contributor phase-2 MPC — each contributor applies a fresh secret `δ_i`,
  publishes a Schnorr proof of contribution, and the chain is checked with
  δ-consistency pairing checks.

The only thing you supply is the **universal phase-1 powers-of-tau transcript**,
which is circuit-*independent*. Don't roll your own — **reuse an existing,
audited public transcript** ([Perpetual Powers of Tau], Hermez); it has far more
contributors (a stronger 1-of-N honest assumption) than anything you'd run
locally. `xark setup --ptau-file` reads the standard `.ptau` format directly, so
you `wget` the file and go. (For a throwaway *test* transcript you can mint a
small one yourself — see [Reproduce](#reproduce-single-circuit-end-to-end) — but
never ship those keys.)

[Perpetual Powers of Tau]: https://github.com/privacy-scaling-explorations/perpetualpowersoftau

There is also a fully **self-contained, in-process** regression test of this
whole path — `crates/tests/tests/ceremony_e2e.rs`. It synthesizes a valid
phase-1 transcript in memory (no snarkjs, no committed `.ptau`), runs
`setup_from_ptau` → two `contribute` steps → `verify_chain`, then proves a
witness with the finalized keys and verifies it — across circuits with **1, 2,
and 16 public inputs** (`arithmetic_square`, `mixed_pi`, `large_pi`). It also
rejects a reordered contribution chain and, for each circuit, confirms **every**
public input is bound (flipping any single one fails). It runs in well under a
second, so CI exercises the ceremony pipeline on every push. Because the test
builds phase-1 itself it *knows* the toxic waste — it proves the pipeline is
**correct**, not that a real ceremony is **secret**.

## Reproduce (single circuit, end-to-end)

For a real deployment, replace phase 1 below with a downloaded public `.ptau`
(see above). The recipe mints a tiny throwaway transcript locally so a single
circuit can be run end-to-end without downloading a multi-GB file — those keys
are **not** production-safe.

```bash
# --- phase 1: a throwaway test transcript (2^12 covers small circuits) ---
# Any tool that emits the standard .ptau works; here, snarkjs:
snarkjs powersoftau new bn128 12 p0.ptau
snarkjs powersoftau contribute p0.ptau p1.ptau --name=c1 -e="<entropy>"
snarkjs powersoftau beacon p1.ptau pb.ptau 0102..1f20 10 -n=beacon
snarkjs powersoftau prepare phase2 pb.ptau final.ptau

# --- phase 2: multi-party MPC over the circuit (xark) ---
SEED=00112233... # 32-byte hex
xark ceremony init --artifact crates/tests/fixtures/arithmetic_square.json \
 --ptau-file final.ptau --phase2-seed $SEED --out ceremony/
xark ceremony contribute --ceremony-dir ceremony/ --label alice
xark ceremony contribute --ceremony-dir ceremony/ --label bob
xark ceremony verify --ceremony-dir ceremony/ # checks the chain
xark ceremony finalize --ceremony-dir ceremony/

# --- prove + verify with the finalized keys ---
xark prove --artifact … --witness … --proving-key ceremony/proving_key.bin --out proof.bin
xark verify --verifying-key ceremony/verifying_key.bin --proof proof.bin --public-inputs public_inputs.json
# => Proof verified: true
```

## Regenerating all committed test vectors

`scripts/ceremony_vectors.sh <power> [circuit …]` runs the whole pipeline and
installs the resulting `*.solana.bin` over the committed fixtures, sanity-checking
each ceremony-keyed proof with snarkjs.

`<power>` must cover the circuit's constraint count (`2^power ≥ constraints`):

| power | covers (committed circuits) |
|------:|-----------------------------|
| 12 (4 096) | arithmetic_*, range, memory_*, multi_function, nested_calls, return_values_only, brillig, mixed_pi, reorder_pi, bitwise, poseidon, large_pi |
| 15 (32 768) | + curve (21 568), blake3 (23 014) |
| 16 (65 536) | + blake2s (33 174), sha256 (54 632) |
| 17 (131 072) | + aes128 (82 704) |
| 18 (262 144) | + keccak (253 782) |

`ecdsa_basic` / `ecdsa_r1_basic` have millions of constraints and need a
correspondingly large phase-1; treat them separately.

Caveats when regenerating committed vectors:
- A full regen must be **consistent** — regenerate every artifact in a circuit's
 fixture dir from the same keys, not a mix of dev-mode + ceremony bytes.
- Update the hash pin in `crates/tests/tests/solana_format.rs`
 (`VK_SOLANA_SHA256` etc.), which intentionally locks the committed VK bytes.
- Re-run `cargo test -p xark-tests` (host + `--test sbpf`) and
 `scripts/differential_snarkjs.sh`.

## For a real production ceremony

The fixed entropy/seed/beacon in `ceremony_vectors.sh` make *test* vectors
reproducible; they are **not** secure. A production ceremony needs:
- multiple **independent** phase-1 contributors and a **public randomness
 beacon** (e.g. a future block hash / drand round) for phase 1;
- multiple independent phase-2 `contribute` participants, each publishing their
 attestation, with `xark ceremony verify` run by third parties;
- the full transcript (per-contributor attestations) published for public
 verification.
