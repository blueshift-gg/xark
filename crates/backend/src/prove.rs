//! Groth16 proving.

use ark_bn254::{Bn254, Fr};
use ark_groth16::{Groth16, Proof, ProvingKey};
use ark_relations::gr1cs::{ConstraintSynthesizer, SynthesisError};
use ark_snark::SNARK;
use rand::{CryptoRng, RngCore};


/// Prove `circuit`, then self-check the result against `public_inputs`.
///
/// `public_inputs` must be the public portion of the circuit's witness.
pub fn prove<C: ConstraintSynthesizer<Fr>, R: RngCore + CryptoRng>(
    pk: &ProvingKey<Bn254>,
    circuit: C,
    public_inputs: &[Fr],
    rng: &mut R,
) -> Result<Proof<Bn254>, SynthesisError> {
    let proof = Groth16::<Bn254>::prove(pk, circuit, rng)?;

    // Post-prove self-check. Arkworks' `prove` does NOT verify that the witness
    // satisfied the R1CS — it will emit a proof for an unsatisfying assignment
    // that then fails verification. A lowering or witness-mapping bug would
    // therefore surface only downstream (or, in a prove-and-ship flow, ship a
    // silently-broken proof). Verifying the fresh proof against the proving
    // key's embedded `vk` is a handful of pairings — negligible next to
    // proving — so we always pay it and fail fast with `Unsatisfiable`.
    //
    // Note: this is a *correctness* guard on our own pipeline, not a soundness
    // control — the verifier rejects invalid proofs regardless.
    if !crate::verify::verify(&pk.vk, &proof, public_inputs)? {
        return Err(SynthesisError::Unsatisfiable);
    }
    Ok(proof)
}
