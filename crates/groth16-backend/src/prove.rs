//! Groth16 proving.

use ark_bn254::Bn254;
use ark_groth16::{Groth16, Proof, ProvingKey};
use ark_snark::SNARK;
use rand::{CryptoRng, RngCore};

use crate::circuit::NoirGroth16Circuit;

pub fn prove<R: RngCore + CryptoRng>(
    pk: &ProvingKey<Bn254>,
    circuit: NoirGroth16Circuit,
    rng: &mut R,
) -> Result<Proof<Bn254>, ark_relations::r1cs::SynthesisError> {
    Groth16::<Bn254>::prove(pk, circuit, rng)
}
