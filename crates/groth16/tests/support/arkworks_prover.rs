//! arkworks' Groth16 as an `xark_groth16::Prover`: the baseline the benchmarks time
//! and the tests hold xark's provers to, byte for byte. It proves from the rows as
//! matrices (`create_proof_with_reduction_and_matrices`), so it takes the same
//! `ConstraintSource` the other provers do, with variables in the same order by
//! construction. Needs `ark.rs` included beside it, as `ark`.

use ark_bn254::{Bn254, Fr};
use ark_relations::utils::matrix::Matrix;
use xark_groth16::r1cs::RowChunk;
use xark_groth16::{ConstraintSource, Proof, ProveError, Prover};

pub struct Arkworks {
    pk: ark_groth16::ProvingKey<Bn254>,
}

impl Arkworks {
    /// The key as arkworks' type (the same bytes, checked as it converts).
    pub fn new(pk: &xark_groth16::ProvingKey<Bn254>) -> Self {
        Arkworks {
            pk: super::ark::convert(pk),
        }
    }
}

impl Prover for Arkworks {
    fn name(&self) -> &str {
        "arkworks"
    }

    fn prove(
        &mut self,
        src: &dyn ConstraintSource,
        z: &[Fr],
        r: Fr,
        s: Fr,
    ) -> Result<Proof<Bn254>, ProveError> {
        let m = src.num_constraints();
        let mut mats: [Matrix<Fr>; 3] = std::array::from_fn(|_| Vec::with_capacity(m));
        let mut chunk = RowChunk::default();
        for w in src.windows(1 << 14) {
            src.expand(&w, &mut chunk);
            for row in 0..chunk.rows() {
                for (k, mat) in mats.iter_mut().enumerate() {
                    let (cols, coeffs) = chunk.terms(row, k);
                    mat.push(
                        coeffs
                            .iter()
                            .copied()
                            .zip(cols.iter().map(|&c| c as usize))
                            .collect(),
                    );
                }
            }
        }
        let proof = ark_groth16::Groth16::<Bn254>::create_proof_with_reduction_and_matrices(
            &self.pk,
            r,
            s,
            &mats,
            src.layout().num_instance(),
            m,
            z,
        )
        .map_err(|e| ProveError::KeyMismatch(format!("arkworks: {e}")))?;
        Ok(super::ark::convert(&proof))
    }
}
