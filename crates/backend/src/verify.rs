//! Groth16 verification: the pairing check, in `xark-groth16`.

use ark_bn254::{Bn254, Fr};
use xark_groth16::{Proof, VerifyError, VerifyingKey};

/// Verify `proof` for `public_inputs` under `vk`. `Ok(false)` for a proof that
/// doesn't verify; `Err` when the public-input count doesn't match the key.
pub fn verify(
    vk: &VerifyingKey<Bn254>,
    proof: &Proof<Bn254>,
    public_inputs: &[Fr],
) -> Result<bool, VerifyError> {
    xark_groth16::verify(vk, public_inputs, proof)
}
