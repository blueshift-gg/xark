//! Arkworks [`ConstraintSynthesizer`] wrapper around a lowered ACIR circuit.

use ark_bn254::Fr;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};

use acir_r1cs::lower::LoweredAcirCircuit;
use acir_r1cs::witness::WitnessMap;

/// Wrapper that adapts a [`LoweredAcirCircuit`] to Arkworks' Groth16 API.
///
/// During setup we leave `witness` as `None` — Arkworks calls the value
/// closures only in proving mode, so we just need the shape.
#[derive(Clone)]
pub struct NoirGroth16Circuit {
    pub lowered: LoweredAcirCircuit,
    pub witness: Option<WitnessMap<Fr>>,
}

impl NoirGroth16Circuit {
    pub fn for_setup(lowered: LoweredAcirCircuit) -> Self {
        Self {
            lowered,
            witness: None,
        }
    }

    pub fn for_proving(lowered: LoweredAcirCircuit, witness: WitnessMap<Fr>) -> Self {
        Self {
            lowered,
            witness: Some(witness),
        }
    }
}

impl ConstraintSynthesizer<Fr> for NoirGroth16Circuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        self.lowered.synthesize(cs, self.witness.as_ref())
    }
}
