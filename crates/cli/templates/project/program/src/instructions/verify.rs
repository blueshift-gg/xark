use pinocchio::{ProgramResult, error::ProgramError};
use {{verifier_ident}}::{Fields, NUM_PUBLIC_INPUTS, Proof, verify};

use crate::{{Error}};

/// `proof (256 B) ‖ public inputs (32 B each, little-endian, in proof order)`.
pub struct VerifyInstructionData<'a> {
    pub proof: &'a [u8; 256],
    pub inputs: Fields,
}

impl<'a> TryFrom<&'a [u8]> for VerifyInstructionData<'a> {
    type Error = ProgramError;

    fn try_from(data: &'a [u8]) -> Result<Self, Self::Error> {
        let (proof, rest) = data
            .split_first_chunk::<256>()
            .ok_or(ProgramError::InvalidInstructionData)?;
        if rest.len() != NUM_PUBLIC_INPUTS * 32 {
            return Err(ProgramError::InvalidInstructionData);
        }
        let mut inputs = [[0u8; 32]; NUM_PUBLIC_INPUTS];
        for (input, bytes) in inputs.iter_mut().zip(rest.chunks_exact(32)) {
            input.copy_from_slice(bytes);
        }
        Ok(Self { proof, inputs })
    }
}

pub struct Verify<'a> {
    pub data: VerifyInstructionData<'a>,
}

impl<'a> TryFrom<&'a [u8]> for Verify<'a> {
    type Error = ProgramError;

    fn try_from(data: &'a [u8]) -> Result<Self, Self::Error> {
        Ok(Self {
            data: VerifyInstructionData::try_from(data)?,
        })
    }
}

impl Verify<'_> {
    pub const DISCRIMINATOR: &'static u8 = &0;

    // Out of line: inlined into the entrypoint under fat LTO, the pairing check's
    // buffers can take its frame past the SBF limit of 4 KiB, which only warns at
    // build time and corrupts the stack at run time.
    #[inline(never)]
    pub fn process(&self) -> ProgramResult {
        // The public inputs come from the instruction here, so this accepts a proof of
        // anything the circuit allows. A real program supplies them from its own state
        // (a policy, a Merkle root, the signer) as `{{verifier_ident}}::PublicInputs`.
        if !verify(&Proof::from_le_bytes(self.data.proof), self.data.inputs) {
            return Err({{Error}}::InvalidProof.into());
        }
        Ok(())
    }
}
