# Trusted-setup ceremony

Groth16 is only as sound as its trusted setup: whoever knows the phase-2 toxic waste
(`τ`, `α`, `β`, `δ`) can forge proofs for *any* statement, however correct the verifier. A key
`xark setup` makes without a `.ptau` comes from OS randomness: a single-party setup, sound unless
whoever ran it kept that randomness, which xark never writes down. Everyone relying on it trusts
that one party; a **multi-party ceremony** removes that, since one honest contributor is enough.
The committed test vectors use a seeded setup (`--deterministic-rng`), whose trapdoor anyone with
the seed can recover: fine for tests, never for a deployed verifier. `xark export` exports any key
and writes how it was made into the verifier crate as `SETUP` (`seeded`, `single-party`,
`ceremony` or `unknown`). A ceremony needs two or more contributors to count as `ceremony`: one
contributor's randomness is OS randomness too, so a ceremony of one is `single-party`, with a
transcript anyone can check the key against.

xark runs the **circuit-specific phase 2** itself (no external prover in the loop):

* `xark setup --ptau-file … --phase2-seed …` derives the `ProvingKey`/`VerifyingKey` from a phase-1
  transcript ([`xark_backend::ptau::setup_from_ptau`]); and
* `xark ceremony {init,contribute,verify,finalize}` drives the multi-contributor phase-2 MPC — each
  contributor applies a fresh secret `δ_i`, publishes a Schnorr proof of contribution, and the chain
  is checked with δ-consistency pairing checks.

You supply only the **universal phase-1 powers-of-tau transcript** (circuit-*independent*). Don't
roll your own — **reuse an existing, audited public transcript** ([Perpetual Powers of Tau], Hermez),
which has far more contributors (a stronger 1-of-N honest assumption) than anything local.
`xark setup --ptau-file` reads the standard `.ptau` format directly, so `wget` and go. (For a
throwaway *test* transcript you can mint a small one yourself — see
[Reproduce](#reproduce-single-circuit-end-to-end) — but **never ship those keys.**)

[Perpetual Powers of Tau]: https://github.com/privacy-scaling-explorations/perpetualpowersoftau

The ceremony is tested at two levels. `crates/backend/src/ceremony.rs` checks the library: one and
three contributions compose and verify, and a tampered chain link, Schnorr response or δ, a zero δ,
or keys that don't match the chain are all rejected. `gadgets/tests/tests/it/ceremony_cli.rs` runs the
CLI end to end on every push: `xark build` → `ceremony init` (over a synthetic phase-1 transcript)
→ two `contribute`s → `verify` → `finalize`, then proves and verifies with the ceremony's keys and
rejects a wrong public input. Both build phase 1 themselves, so they *know* the toxic waste: they
prove the pipeline is **correct**, not that a real ceremony is **secret**.

## Reproduce (single circuit, end-to-end)

For a real deployment, replace phase 1 with a downloaded public `.ptau` (see above). This recipe
mints a tiny throwaway transcript locally so a single circuit runs end-to-end without a multi-GB
download — those keys are **not** production-safe.

```bash
# --- phase 1: a throwaway test transcript (2^12 covers small circuits) ---
# Any tool that emits the standard .ptau works; here, snarkjs:
snarkjs powersoftau new bn128 12 p0.ptau
snarkjs powersoftau contribute p0.ptau p1.ptau --name=c1 -e="<entropy>"
snarkjs powersoftau beacon p1.ptau pb.ptau 0102..1f20 10 -n=beacon
snarkjs powersoftau prepare phase2 pb.ptau final.ptau

# --- phase 2: multi-party MPC over the circuit (xark), inside the circuit crate ---
cd examples/cube && xark build
xark ceremony init --ptau-file final.ptau --out ceremony/   # reads target/xark/…/circuit.xbc
xark ceremony contribute --ceremony-dir ceremony/ --label alice
xark ceremony contribute --ceremony-dir ceremony/ --label bob
# checks the chain, and that the keys are the circuit's (from final.ptau and the
# recorded seed) with only δ changed
xark ceremony verify --ceremony-dir ceremony/ --ptau-file final.ptau
xark ceremony finalize --ceremony-dir ceremony/ --ptau-file final.ptau

# --- prove + verify with the finalized keys ---
xark prove --inputs '{"secret": "3", "result": "27"}' \
 --proving-key ceremony/proving_key.bin --out proof/
xark verify --verifying-key ceremony/verifying_key.bin --proof proof/proof.bin \
 --public-inputs proof/public_inputs.bin
# => ✅ Proof verified
```

## Regenerating all committed test vectors

Run the steps above for each circuit, then install the resulting `*.solana.bin` over the committed
fixtures. The phase-1 power must cover the circuit: `2^power` at least its constraint count plus
public inputs (`xark inspect` prints both). If the transcript is too small, `ceremony init` says
how big it needs to be. `secp256k1_ecdsa` and `secp256r1_ecdsa` (227,168 and 344,969 constraints)
need a correspondingly large phase 1; treat them separately.

Caveats when regenerating:
- A full regen must be **consistent** — regenerate every artifact in a circuit's fixture dir from the
  same keys, not a mix of single-party and ceremony bytes.
- Update the hash pin in `gadgets/tests/tests/it/solana_format.rs` (`VK_SOLANA_SHA256` etc.), which
  intentionally locks the committed VK bytes.
- Re-run `cargo test -p xark-tests` (host + `--test sbpf`).

## For a real production ceremony

Fixed entropy, seeds and beacons make *test* vectors reproducible; they are **not** secure. A production ceremony needs:
- multiple **independent** phase-1 contributors and a **public randomness beacon** (e.g. a future
  block hash / drand round) for phase 1;
- multiple independent phase-2 `contribute` participants, each publishing their attestation, with
  `xark ceremony verify` run by third parties, each from their own build of the circuit and their
  own copy of the phase-1 `.ptau`;
- the full transcript (per-contributor attestations) published for public verification.
