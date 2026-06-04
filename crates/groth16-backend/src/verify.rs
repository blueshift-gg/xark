//! Groth16 verification.

use ark_bn254::{Bn254, Fr};
use ark_groth16::{Groth16, Proof, VerifyingKey};
use ark_snark::SNARK;

pub fn verify(
    vk: &VerifyingKey<Bn254>,
    proof: &Proof<Bn254>,
    public_inputs: &[Fr],
) -> Result<bool, ark_relations::r1cs::SynthesisError> {
    Groth16::<Bn254>::verify(vk, public_inputs, proof)
}
