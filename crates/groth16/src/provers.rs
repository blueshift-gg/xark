//! Groth16 provers behind one interface, so one can stand in for another: in the
//! CLI, in a benchmark that times each on the same circuit, and in the tests,
//! which hold every prover to the same proof bytes.
//!
//! A [`Prover`] holds its proving key, loaded however it likes (streamed from a
//! file, resident, uploaded to a device), and proves any witness of that key's
//! circuit. The randomness `(r, s)` is the caller's, so two provers given the
//! same `(r, s)` must return the same proof: for xark's provers and arkworks'
//! that is the libsnark reduction, byte for byte.

use ark_bn254::{Bn254, Fr};
use ark_ff::UniformRand;
use rand::RngCore;

use crate::pk::PkSource;
use crate::prover::{ProveError, ProverConfig, prove_with_randomness};
use crate::r1cs::ConstraintSource;
use crate::types::Proof;

/// A Groth16 prover with its proving key loaded.
pub trait Prover {
    /// A short name for reports and benchmarks.
    fn name(&self) -> &str;

    /// A proof that `z`, the full assignment in `src`'s
    /// [`VarLayout`](crate::r1cs::VarLayout) order (`z[0] = 1`), satisfies
    /// `src`'s rows, with randomness `(r, s)`.
    fn prove(
        &mut self,
        src: &dyn ConstraintSource,
        z: &[Fr],
        r: Fr,
        s: Fr,
    ) -> Result<Proof<Bn254>, ProveError>;
}

/// [`Prover::prove`] with `r`, then `s` drawn from `rng`, as arkworks draws them,
/// so a seeded RNG gives arkworks' proof.
pub fn prove_with_rng<R: RngCore>(
    prover: &mut dyn Prover,
    src: &dyn ConstraintSource,
    z: &[Fr],
    rng: &mut R,
) -> Result<Proof<Bn254>, ProveError> {
    let r = Fr::rand(rng);
    let s = Fr::rand(rng);
    prover.prove(src, z, r, s)
}

/// xark's prover on the CPU: the key streamed from a file ([`SerializedPk`]) or
/// resident ([`InMemoryPk`]), as `P` is.
///
/// [`SerializedPk`]: crate::SerializedPk
/// [`InMemoryPk`]: crate::InMemoryPk
pub struct Cpu<P> {
    pub pk: P,
    pub cfg: ProverConfig,
}

impl<P: PkSource> Cpu<P> {
    pub fn new(pk: P, cfg: ProverConfig) -> Self {
        Cpu { pk, cfg }
    }
}

impl<P: PkSource> Prover for Cpu<P> {
    fn name(&self) -> &str {
        "xark-groth16"
    }

    fn prove(
        &mut self,
        src: &dyn ConstraintSource,
        z: &[Fr],
        r: Fr,
        s: Fr,
    ) -> Result<Proof<Bn254>, ProveError> {
        prove_with_randomness(src, z, &mut self.pk, r, s, &self.cfg, &mut ())
    }
}
