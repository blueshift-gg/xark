//! Groth16 setup (insecure dev mode).

use ark_bn254::{Bn254, Fr};
use ark_groth16::Groth16;
use ark_snark::SNARK;
use rand::{CryptoRng, RngCore};

use crate::keys::Groth16Keys;

/// Run Groth16 [`circuit_specific_setup`](Groth16::circuit_specific_setup) with
/// the supplied RNG. `rng` is expected to be cryptographically secure when not
/// in dev mode; the CLI guards against accidental use of insecure setup.
pub fn setup<C: ark_relations::gr1cs::ConstraintSynthesizer<Fr>, R: RngCore + CryptoRng>(
    circuit: C,
    rng: &mut R,
) -> Result<Groth16Keys, ark_relations::gr1cs::SynthesisError> {
    let (pk, vk) = Groth16::<Bn254>::circuit_specific_setup(circuit, rng)?;
    Ok(Groth16Keys {
        proving_key: pk,
        verifying_key: vk,
    })
}
