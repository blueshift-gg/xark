//! arkworks as a reference oracle, for tests and benchmarks only (`ark-groth16`
//! and `ark-relations` are dev-dependencies): an R1CS program as an arkworks
//! circuit, so arkworks' own Groth16 can set up and prove it, and a conversion
//! between arkworks' key/proof types and `xark-groth16`'s through their bytes —
//! which also checks, on every use, that the two serialize identically.
//!
//! Included with `#[path]` by `xark-groth16`'s tests and benchmarks and by
//! `gadgets/tests`.
#![allow(dead_code)]

use std::collections::BTreeMap;

use ark_bn254::Fr;
use ark_ff::Zero;
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, SynthesisError, Variable,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use xark_ir::{LinearCombination as IrLc, R1csProgram, VarId, Visibility};

/// An R1CS program and (for proving) its witness, as an arkworks circuit. Public
/// variables are arkworks inputs, everything else witnesses, allocated in id
/// order — the layout `xark-groth16`'s `VarLayout` reproduces.
#[derive(Clone)]
pub struct ArkCircuit {
    pub prog: R1csProgram,
    pub assign: BTreeMap<VarId, Fr>,
}

impl ArkCircuit {
    /// The same circuit as `c` (its program and assignment).
    pub fn of(c: &xark_prover::XarkCircuit) -> Self {
        ArkCircuit {
            prog: c.prog().clone(),
            assign: c.assignment().clone(),
        }
    }
}

impl ConstraintSynthesizer<Fr> for ArkCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let mut order: Vec<_> = self.prog.variables.iter().collect();
        order.sort_by_key(|v| v.id);
        let mut map: BTreeMap<VarId, Variable> = BTreeMap::new();
        for v in order {
            let val = self.assign.get(&v.id).copied().unwrap_or_else(Fr::zero);
            let av = match v.visibility {
                Visibility::Public => cs.new_input_variable(|| Ok(val))?,
                _ => cs.new_witness_variable(|| Ok(val))?,
            };
            map.insert(v.id, av);
        }
        let build = |lc: &IrLc| -> LinearCombination<Fr> {
            let mut out = LinearCombination::zero();
            let c = xark_prover::fr_from_fieldconst(&lc.constant);
            if !c.is_zero() {
                out += (c, Variable::One);
            }
            for t in &lc.terms {
                out += (xark_prover::fr_from_fieldconst(&t.coeff), map[&t.var]);
            }
            out
        };
        for con in &self.prog.constraints {
            let (a, b, c) = (build(&con.a), build(&con.b), build(&con.c));
            cs.enforce_r1cs_constraint(|| a, || b, || c)?;
        }
        Ok(())
    }
}

/// `a` as the other library's type with the same bytes (arkworks ⇄ xark-groth16).
pub fn convert<A: CanonicalSerialize, B: CanonicalSerialize + CanonicalDeserialize>(a: &A) -> B {
    let mut bytes = Vec::new();
    a.serialize_uncompressed(&mut bytes).expect("serialize");
    let b = B::deserialize_uncompressed_unchecked(&bytes[..]).expect("same layout");
    let mut again = Vec::new();
    b.serialize_uncompressed(&mut again).expect("serialize");
    assert_eq!(
        bytes, again,
        "arkworks and xark-groth16 serialize differently"
    );
    b
}
