//! Prove from the artifacts `xark build` and `xark setup` write, in memory.
//!
//! What `xark prove` does, as a library: load `circuit.xbc` and `pk.bin` once,
//! then prove any number of witnesses with the real proving key. For embedding
//! the prover in an app or a service (mobile, server, wasm) without the CLI.
//!
//! ```ignore
//! let prover = ArtifactProver::load(&xbc, &pk)?;
//! let inputs = [("secret", "3"), ("result", "27")];
//! let (proof, public) = prover.prove(inputs, &mut rand::rngs::OsRng)?;
//! assert!(prover.verify(&proof, &public)?);
//! ```
//!
//! [`ArtifactProver::load`] reproduces the minimized R1CS the key was set up
//! against, which costs a minimization pass. When `xark setup --cache` wrote
//! `r1cs.min.wcz`, [`ArtifactProver::load_with_r1cs_cache`] reads it instead.

use std::collections::BTreeMap;

use ark_bn254::{Bn254, Fr};
use ark_groth16::{Groth16, Proof, ProvingKey, VerifyingKey};
use ark_serialize::{CanonicalDeserialize, Compress, Validate};
use ark_snark::SNARK;
use rand::{CryptoRng, RngCore};
use sha2::{Digest, Sha256};

use xark_ir::function_decode::{expand_function_blob, expand_function_blob_reduced};
use xark_ir::{CircuitProgram, R1csProgram, VarId};

use crate::{XarkCircuit, lower_witness, solver, try_fr_from_decimal};

/// A built circuit and its proving key, ready to prove.
pub struct ArtifactProver {
    /// The full circuit, witness generation intact, for the solver.
    circuit: CircuitProgram,
    /// The minimized R1CS the proving key is keyed to.
    r1cs: R1csProgram,
    by_name: BTreeMap<String, VarId>,
    pk: ProvingKey<Bn254>,
}

impl std::fmt::Debug for ArtifactProver {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ArtifactProver")
            .field("variables", &self.by_name.len())
            .field("constraints", &self.r1cs.constraints.len())
            .finish_non_exhaustive()
    }
}

impl ArtifactProver {
    /// From `circuit.xbc` and `pk.bin`. Minimizes the R1CS exactly as `xark
    /// setup` did, so the proof matches the key.
    pub fn load(circuit_xbc: &[u8], pk_bytes: &[u8]) -> Result<Self, String> {
        let reduced = expand_function_blob_reduced(circuit_xbc)
            .map_err(|e| format!("parsing circuit.xbc: {e}"))?
            .into_r1cs();
        let r1cs = XarkCircuit::for_setup(reduced).prog().clone();
        Self::assemble(circuit_xbc, r1cs, pk_bytes)
    }

    /// As [`Self::load`], with the minimized R1CS read from the `r1cs.min.wcz`
    /// that `xark setup --cache` writes, which skips the minimization. Fails if
    /// the cache was written for another `circuit.xbc`.
    pub fn load_with_r1cs_cache(
        circuit_xbc: &[u8],
        r1cs_cache: &[u8],
        pk_bytes: &[u8],
    ) -> Result<Self, String> {
        let fingerprint: String = Sha256::digest(circuit_xbc)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        let r1cs = xark_ir::r1cs_cache::deserialize_if_fingerprint(r1cs_cache, &fingerprint)
            .ok_or("r1cs.min.wcz is not for this circuit.xbc (rerun `xark setup --cache`)")?;
        Self::assemble(circuit_xbc, r1cs, pk_bytes)
    }

    fn assemble(circuit_xbc: &[u8], r1cs: R1csProgram, pk_bytes: &[u8]) -> Result<Self, String> {
        let circuit =
            expand_function_blob(circuit_xbc).map_err(|e| format!("parsing circuit.xbc: {e}"))?;
        let by_name = circuit
            .vars
            .iter()
            .map(|v| (v.name.clone(), v.id))
            .collect();
        Ok(Self {
            circuit,
            r1cs,
            by_name,
            pk: deserialize_proving_key(pk_bytes)?,
        })
    }

    /// The verifying key embedded in the proving key.
    pub fn verifying_key(&self) -> &VerifyingKey<Bn254> {
        &self.pk.vk
    }

    /// Resolve `name → decimal value` inputs (the names `xark inspect` prints,
    /// `path[0]` for array elements) to the solver's `VarId → decimal` map,
    /// validating each value as a field element.
    pub fn resolve<'a>(
        &self,
        inputs: impl IntoIterator<Item = (&'a str, &'a str)>,
    ) -> Result<BTreeMap<VarId, String>, String> {
        let mut resolved = BTreeMap::new();
        for (name, value) in inputs {
            let &id = self
                .by_name
                .get(name)
                .ok_or_else(|| format!("unknown input `{name}`"))?;
            try_fr_from_decimal(value)
                .map_err(|e| format!("invalid value for input `{name}`: {e}"))?;
            resolved.insert(id, value.to_string());
        }
        Ok(resolved)
    }

    /// Solve the witness and prove. Returns the proof and its public inputs
    /// (in the order the verifier expects). Does not self-verify; use
    /// [`Self::verify`] when needed.
    pub fn prove<'a, R: RngCore + CryptoRng>(
        &self,
        inputs: impl IntoIterator<Item = (&'a str, &'a str)>,
        rng: &mut R,
    ) -> Result<(Proof<Bn254>, Vec<Fr>), String> {
        let resolved = self.resolve(inputs)?;
        self.prove_resolved(&resolved, rng)
    }

    /// [`Self::prove`] from inputs already resolved by [`Self::resolve`].
    pub fn prove_resolved<R: RngCore + CryptoRng>(
        &self,
        inputs: &BTreeMap<VarId, String>,
        rng: &mut R,
    ) -> Result<(Proof<Bn254>, Vec<Fr>), String> {
        let assign = solver::solve_and_check_cp(&self.circuit, inputs)
            .map_err(|e| format!("witness does not satisfy the circuit: {e:?}"))?;
        let instance =
            XarkCircuit::for_proving_preminimized(self.r1cs.clone(), lower_witness(&assign));
        instance
            .validate()
            .map_err(|e| format!("malformed circuit: {e}"))?;
        let public = instance.public_inputs();
        let proof = Groth16::<Bn254>::prove(&self.pk, instance, rng)
            .map_err(|e| format!("proving: {e}"))?;
        Ok((proof, public))
    }

    /// Check a proof against this circuit's verifying key.
    pub fn verify(&self, proof: &Proof<Bn254>, public: &[Fr]) -> Result<bool, String> {
        Groth16::<Bn254>::verify(&self.pk.vk, public, proof).map_err(|e| format!("verifying: {e}"))
    }
}

/// Deserialize a `pk.bin` written by `xark setup`: the `XKPK` header (magic,
/// version, compression flag), or a bare compressed key from older setups.
pub fn deserialize_proving_key(bytes: &[u8]) -> Result<ProvingKey<Bn254>, String> {
    const PK_MAGIC: &[u8; 4] = b"XKPK";
    let (compress, body) = if bytes.len() >= 6 && &bytes[..4] == PK_MAGIC {
        let mode = if bytes[5] == 1 {
            Compress::No
        } else {
            Compress::Yes
        };
        (mode, &bytes[6..])
    } else {
        (Compress::Yes, bytes)
    };
    ProvingKey::<Bn254>::deserialize_with_mode(body, compress, Validate::Yes)
        .map_err(|e| format!("deserializing proving key: {e}"))
}
