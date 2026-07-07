//! End-to-end Groth16 prover for the xark-lang IR.
//!
//! Consumes an [`R1csProgram`] (our `a·b = c` constraint form) plus a
//! [`PrimitiveProgram`] (the witness-generation hint program), runs the
//! reference [`solver`] to produce the full witness, lowers the constraints into
//! Arkworks `gr1cs`, and runs the exact Groth16/BN254 stack the `xark` backend
//! uses (ark 0.6). This closes the loop: a Rust circuit → MIR → xark-IR → R1CS →
//! a *verified* Groth16 proof, entirely within xark's own pipeline.

use std::collections::BTreeMap;

use ark_bn254::{Bn254, Fr};
use ark_ff::{PrimeField, Zero};
use ark_groth16::{Groth16, Proof, VerifyingKey};
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, SynthesisError, Variable,
};
use ark_snark::SNARK;
use num_bigint::{BigInt, Sign};

use xark_ir::primitive::{PrimitiveProgram, Var, VarRole};
use xark_ir::solver;
use xark_ir::{LinearCombination as IrLc, R1csProgram, VarId, Visibility};

/// BN254 scalar field modulus (decimal).
const BN254_MODULUS: &[u8] =
    b"21888242871839275222246405745257275088548364400416034343698204186575808495617";

/// Parse a (possibly negative) decimal `FieldConst` into an `Fr`, reduced mod p.
///
/// Returns `Err` with a descriptive message if `s` is not a valid decimal
/// integer. Use this on any constant that originates from untrusted input
/// (e.g. a deserialized `r1cs.json`); it never panics.
pub fn try_fr_from_decimal(s: &str) -> Result<Fr, String> {
    let bi = BigInt::parse_bytes(s.as_bytes(), 10)
        .ok_or_else(|| format!("invalid decimal field constant: {s:?}"))?;
    // The modulus is a compile-time constant known to be a valid decimal.
    let modulus = BigInt::parse_bytes(BN254_MODULUS, 10).expect("BN254_MODULUS is a valid decimal");
    let mut r = bi % &modulus;
    if r.sign() == Sign::Minus {
        r += &modulus;
    }
    let (_, bytes) = r.to_bytes_le();
    Ok(Fr::from_le_bytes_mod_order(&bytes))
}

/// Infallible convenience wrapper over [`try_fr_from_decimal`] for *trusted*
/// decimals (constants this crate produced itself, e.g. solver witness output).
///
/// Panics if `s` is not a valid decimal — do not call it on untrusted input;
/// use [`try_fr_from_decimal`] there instead.
pub fn fr_from_decimal(s: &str) -> Fr {
    try_fr_from_decimal(s).expect("valid decimal")
}

/// A synthesizable circuit over the xark-lang IR: our R1CS constraints plus a
/// variable assignment. Implements Arkworks `gr1cs` [`ConstraintSynthesizer`],
/// so it drops directly into the `xark` backend's generic `setup_from_ptau` /
/// `Groth16::prove` / `verify` — a generic Groth16 over the constraint system.
/// Supports both setup mode
/// (constraint shape only) and proving mode (with the witness assignment).
#[derive(Clone)]
pub struct XarkCircuit {
    prog: R1csProgram,
    assign: BTreeMap<VarId, Fr>,
}

impl XarkCircuit {
    /// For Groth16 setup: only the constraint *shape* is needed (Arkworks calls
    /// the value closures only in proving mode), so the assignment is empty.
    pub fn for_setup(prog: R1csProgram) -> Self {
        Self {
            prog,
            assign: BTreeMap::new(),
        }
    }

    /// For proving: the constraints plus the full solved witness (`VarId → Fr`).
    pub fn for_proving(prog: R1csProgram, assign: BTreeMap<VarId, Fr>) -> Self {
        Self { prog, assign }
    }

    /// Public inputs in variable-id (allocation) order — the order Groth16
    /// verification expects.
    pub fn public_inputs(&self) -> Vec<Fr> {
        public_inputs(&self.prog, &self.assign)
    }

    /// Pre-flight validation of the program's field constants. Every constant
    /// and coefficient decimal in the R1CS is parsed; on the first malformed
    /// one this returns a descriptive `Err` instead of letting the (infallible)
    /// parse inside [`ConstraintSynthesizer::generate_constraints`] panic.
    ///
    /// Call this before handing a circuit built from *untrusted* input (e.g. a
    /// deserialized `r1cs.json`) to the Groth16 backend. [`prove_only`] runs it
    /// automatically.
    pub fn validate(&self) -> Result<(), String> {
        validate_program_constants(&self.prog)
    }
}

/// Parse every field constant / coefficient decimal in `prog`, returning a
/// descriptive error on the first malformed value. Used to fail gracefully on
/// an untrusted R1CS program before the panicking synthesis path runs.
fn validate_program_constants(prog: &R1csProgram) -> Result<(), String> {
    let check_lc = |lc: &IrLc| -> Result<(), String> {
        try_fr_from_decimal(&lc.constant.decimal)?;
        for t in &lc.terms {
            try_fr_from_decimal(&t.coeff.decimal)?;
        }
        Ok(())
    };
    for con in &prog.constraints {
        check_lc(&con.a)?;
        check_lc(&con.b)?;
        check_lc(&con.c)?;
    }
    Ok(())
}

impl ConstraintSynthesizer<Fr> for XarkCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // Allocate one arkworks variable per IR var, in id order. Public →
        // input variable, everything else → witness variable.
        let mut vars = self.prog.variables.clone();
        vars.sort_by_key(|v| v.id);
        let mut map: BTreeMap<VarId, Variable> = BTreeMap::new();
        for v in &vars {
            let val = self.assign.get(&v.id).copied().unwrap_or_else(Fr::zero);
            let av = match v.visibility {
                Visibility::Public => cs.new_input_variable(|| Ok(val))?,
                _ => cs.new_witness_variable(|| Ok(val))?,
            };
            map.insert(v.id, av);
        }

        let build = |lc: &IrLc| -> LinearCombination<Fr> {
            let mut out = LinearCombination::zero();
            let c = fr_from_decimal(&lc.constant.decimal);
            if !c.is_zero() {
                out = out + (c, Variable::One);
            }
            for t in &lc.terms {
                out = out + (fr_from_decimal(&t.coeff.decimal), map[&t.var]);
            }
            out
        };

        for con in &self.prog.constraints {
            let a = build(&con.a);
            let b = build(&con.b);
            let c = build(&con.c);
            cs.enforce_r1cs_constraint(|| a, || b, || c)?;
        }
        Ok(())
    }
}

/// Public inputs in variable-id order (the order they are allocated), which is
/// exactly the order Groth16 verification expects.
fn public_inputs(prog: &R1csProgram, assign: &BTreeMap<VarId, Fr>) -> Vec<Fr> {
    let mut vars = prog.variables.clone();
    vars.sort_by_key(|v| v.id);
    vars.iter()
        .filter(|v| v.visibility == Visibility::Public)
        .map(|v| assign.get(&v.id).copied().unwrap_or_else(Fr::zero))
        .collect()
}

/// Solve the witness, run Groth16 setup + prove, and return the verifying key,
/// proof, and public inputs (so the caller can verify — possibly against
/// tampered public inputs).
pub fn prove_only(
    r1cs: &R1csProgram,
    circuit: &PrimitiveProgram,
    inputs: &BTreeMap<VarId, String>,
) -> Result<(VerifyingKey<Bn254>, Proof<Bn254>, Vec<Fr>), String> {
    // Reject a malformed R1CS program (bad decimal constant) up front with a
    // descriptive error, rather than panicking inside Groth16 synthesis.
    validate_program_constants(r1cs)?;
    let assign_fp = solver::solve_and_check(circuit, inputs)
        .map_err(|e| format!("witness does not satisfy the circuit: {e:?}"))?;
    let assign: BTreeMap<VarId, Fr> = assign_fp
        .iter()
        .map(|(k, v)| (*k, fr_from_decimal(&v.to_decimal())))
        .collect();

    let public = public_inputs(r1cs, &assign);
    let circ = XarkCircuit::for_proving(r1cs.clone(), assign);

    use rand::SeedableRng;
    let mut rng = rand::rngs::StdRng::seed_from_u64(0);
    let (pk, vk) = Groth16::<Bn254>::circuit_specific_setup(circ.clone(), &mut rng)
        .map_err(|e| format!("setup: {e:?}"))?;
    let proof =
        Groth16::<Bn254>::prove(&pk, circ, &mut rng).map_err(|e| format!("prove: {e:?}"))?;
    Ok((vk, proof, public))
}

/// Run the full pipeline: solve the witness from `inputs`, lower to Groth16, and
/// return whether the resulting proof verifies against the public inputs.
pub fn prove_and_verify(
    r1cs: &R1csProgram,
    circuit: &PrimitiveProgram,
    inputs: &BTreeMap<VarId, String>,
) -> Result<bool, String> {
    let (vk, proof, public) = prove_only(r1cs, circuit, inputs)?;
    Groth16::<Bn254>::verify(&vk, &public, &proof).map_err(|e| format!("verify: {e:?}"))
}

// ===========================================================================
// In-crate testing API.
//
// Lets a circuit author unit-test their circuit with plain `cargo test` (via
// the `xark init` scaffold): load the built artifacts, feed positional inputs,
// and get back whether a dev-mode Groth16 proof verifies.
// ===========================================================================

/// A built circuit loaded from `target/xark/<name>/`, ready to prove against.
///
/// Obtain one with [`circuit`]; drive it with [`Circuit::prove`].
pub struct Circuit {
    r1cs: R1csProgram,
    prim: PrimitiveProgram,
}

/// Load a circuit built by `xark build` from `target/xark/<name>/`, relative to
/// the current directory (where `cargo test` runs, i.e. the crate root).
///
/// Panics with a clear message if the artifacts are missing — run `xark build`
/// first.
pub fn circuit(name: &str) -> Circuit {
    let dir = std::path::Path::new("target/xark").join(name);
    let circuit_path = dir.join("circuit.json");
    let r1cs_path = dir.join("r1cs.json");
    let cj = std::fs::read_to_string(&circuit_path).unwrap_or_else(|_| {
        panic!(
            "circuit `{name}` not built — run `xark build` first \
             (expected target/xark/{name}/circuit.json)"
        )
    });
    let rj = std::fs::read_to_string(&r1cs_path).unwrap_or_else(|_| {
        panic!(
            "circuit `{name}` not built — run `xark build` first \
             (expected target/xark/{name}/circuit.json)"
        )
    });
    let prim = xark_ir::primitive::from_json(&cj)
        .unwrap_or_else(|e| panic!("parsing {}: {e}", circuit_path.display()));
    let r1cs = xark_ir::json::from_json(&rj)
        .unwrap_or_else(|e| panic!("parsing {}: {e}", r1cs_path.display()));
    Circuit { r1cs, prim }
}

impl Circuit {
    /// Prove the circuit against `inputs`, mapped **positionally** onto the
    /// circuit's declared inputs (its `Private`/`Public` params, in declaration
    /// / variable-id order — derived internals are excluded).
    ///
    /// Each integer is reduced into the field (negatives wrap mod p). The
    /// witness is solved and checked; if it is unsatisfiable, this returns
    /// `false`. Otherwise a dev-mode Groth16 (seed 1) setup + prove + verify
    /// runs and its verification result is returned — so a valid witness yields
    /// `true`, an invalid one `false`.
    ///
    /// Panics on a length mismatch (wrong number of inputs).
    pub fn prove<T: Into<i128> + Copy>(&self, inputs: impl AsRef<[T]>) -> bool {
        let inputs = inputs.as_ref();

        // Declared inputs in variable-id (declaration) order.
        let mut input_vars: Vec<&Var> = self
            .prim
            .vars
            .iter()
            .filter(|v| matches!(v.role, VarRole::PublicInput | VarRole::PrivateInput))
            .collect();
        input_vars.sort_by_key(|v| v.id);

        if inputs.len() != input_vars.len() {
            let names: Vec<&str> = input_vars.iter().map(|v| v.name.as_str()).collect();
            panic!(
                "circuit expects {} input(s) {:?}, got {}",
                input_vars.len(),
                names,
                inputs.len()
            );
        }

        let mut id_inputs: BTreeMap<VarId, String> = BTreeMap::new();
        for (v, val) in input_vars.iter().zip(inputs) {
            let n: i128 = (*val).into();
            id_inputs.insert(v.id, n.to_string());
        }

        // Solve the witness; an unsatisfiable witness means the statement is
        // false → the proof would not verify, so report `false` directly.
        let assign_fp = match solver::solve_and_check(&self.prim, &id_inputs) {
            Ok(a) => a,
            Err(_) => return false,
        };
        let assign: BTreeMap<VarId, Fr> = assign_fp
            .iter()
            .map(|(k, v)| (*k, fr_from_decimal(&v.to_decimal())))
            .collect();

        let public = public_inputs(&self.r1cs, &assign);
        let circ = XarkCircuit::for_proving(self.r1cs.clone(), assign);

        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(1);
        let (pk, vk) = match Groth16::<Bn254>::circuit_specific_setup(circ.clone(), &mut rng) {
            Ok(x) => x,
            Err(_) => return false,
        };
        let proof = match Groth16::<Bn254>::prove(&pk, circ, &mut rng) {
            Ok(p) => p,
            Err(_) => return false,
        };
        Groth16::<Bn254>::verify(&vk, &public, &proof).unwrap_or(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use xark_ir::primitive::{Expression, MulTerm, Var, VarRole, WitnessGen};
    use xark_ir::r1cs::{DebugInfo, R1csConstraint};
    use xark_ir::{FieldConst, LinearCombination as Lc, Variable as IrVar};

    // Circuit: prove `out == a * b` for public `out`, private `a`, `b`.
    // Derived `t = a*b` (witness-gen Product), pinned by `a·b = t` and `t = out`.
    fn demo() -> (R1csProgram, PrimitiveProgram) {
        let vars_r = vec![
            IrVar {
                id: 0,
                name: "a".into(),
                visibility: Visibility::Private,
            },
            IrVar {
                id: 1,
                name: "b".into(),
                visibility: Visibility::Private,
            },
            IrVar {
                id: 2,
                name: "out".into(),
                visibility: Visibility::Public,
            },
            IrVar {
                id: 3,
                name: "t".into(),
                visibility: Visibility::Internal,
            },
        ];
        let one = FieldConst::from_i64(1);
        let neg1 = FieldConst::from_i64(-1);
        let constraints = vec![
            // a * b = t
            R1csConstraint {
                id: 0,
                a: Lc::var(0),
                b: Lc::var(1),
                c: Lc::var(3),
                debug: None::<DebugInfo>,
            },
            // (t - out) * 1 = 0
            R1csConstraint {
                id: 1,
                a: Lc {
                    constant: FieldConst::from_i64(0),
                    terms: vec![
                        xark_ir::Term {
                            coeff: one.clone(),
                            var: 3,
                        },
                        xark_ir::Term {
                            coeff: neg1.clone(),
                            var: 2,
                        },
                    ],
                },
                b: Lc::one(),
                c: Lc::zero(),
                debug: None::<DebugInfo>,
            },
        ];
        let r1cs = R1csProgram {
            field: xark_ir::FieldSpec {
                name: "bn254".into(),
                modulus_decimal: Some(String::from_utf8(BN254_MODULUS.to_vec()).unwrap()),
            },
            variables: vars_r,
            constraints,
        };
        let prim = PrimitiveProgram {
            field: xark_ir::primitive::FieldSpec::bn254(),
            vars: vec![
                Var {
                    id: 0,
                    name: "a".into(),
                    role: VarRole::PrivateInput,
                },
                Var {
                    id: 1,
                    name: "b".into(),
                    role: VarRole::PrivateInput,
                },
                Var {
                    id: 2,
                    name: "out".into(),
                    role: VarRole::PublicInput,
                },
                Var {
                    id: 3,
                    name: "t".into(),
                    role: VarRole::Derived,
                },
            ],
            constraints: vec![
                Expression {
                    mul_terms: vec![MulTerm {
                        coeff: FieldConst::from_i64(1),
                        left: 0,
                        right: 1,
                    }],
                    linear_terms: vec![xark_ir::primitive::LinearTerm {
                        coeff: FieldConst::from_i64(-1),
                        var: 3,
                    }],
                    constant: FieldConst::from_i64(0),
                    note: None,
                },
                Expression {
                    mul_terms: vec![],
                    linear_terms: vec![
                        xark_ir::primitive::LinearTerm {
                            coeff: FieldConst::from_i64(1),
                            var: 3,
                        },
                        xark_ir::primitive::LinearTerm {
                            coeff: FieldConst::from_i64(-1),
                            var: 2,
                        },
                    ],
                    constant: FieldConst::from_i64(0),
                    note: None,
                },
            ],
            witness_gen: vec![WitnessGen::Product {
                out: 3,
                left: Lc::var(0),
                right: Lc::var(1),
            }],
        };
        (r1cs, prim)
    }

    #[test]
    fn proves_and_verifies_valid_witness() {
        let (r1cs, prim) = demo();
        let mut inputs = BTreeMap::new();
        inputs.insert(0u32, "3".to_string());
        inputs.insert(1u32, "4".to_string());
        inputs.insert(2u32, "12".to_string()); // out = 3*4
        assert!(prove_and_verify(&r1cs, &prim, &inputs).unwrap());
    }

    #[test]
    fn tampered_public_input_fails_verification() {
        // Prove a valid statement (out = 3*4 = 12), then verify the proof
        // against a tampered public input (13) — must be rejected.
        let (r1cs, prim) = demo();
        let mut inputs = BTreeMap::new();
        inputs.insert(0u32, "3".to_string());
        inputs.insert(1u32, "4".to_string());
        inputs.insert(2u32, "12".to_string());
        let (vk, proof, public) = prove_only(&r1cs, &prim, &inputs).unwrap();
        assert!(Groth16::<Bn254>::verify(&vk, &public, &proof).unwrap());

        let tampered = vec![public[0] + Fr::from(1u64)];
        assert!(!Groth16::<Bn254>::verify(&vk, &tampered, &proof).unwrap());
    }

    #[test]
    fn try_fr_from_decimal_rejects_garbage() {
        assert!(try_fr_from_decimal("123").is_ok());
        assert!(try_fr_from_decimal("-7").is_ok());
        assert!(try_fr_from_decimal("not a number").is_err());
        assert!(try_fr_from_decimal("").is_err());
        assert!(try_fr_from_decimal("0x1f").is_err());
    }

    #[test]
    fn malformed_r1cs_constant_is_rejected_not_panicked() {
        // A program whose constraint carries a non-numeric coefficient must be
        // rejected with an Err from the public prove path, not a panic.
        let (mut r1cs, prim) = demo();
        // Corrupt the first constraint's `c` linear combination constant.
        r1cs.constraints[0].c.constant = FieldConst {
            decimal: "garbage".into(),
        };
        let mut inputs = BTreeMap::new();
        inputs.insert(0u32, "3".to_string());
        inputs.insert(1u32, "4".to_string());
        inputs.insert(2u32, "12".to_string());
        let err = prove_only(&r1cs, &prim, &inputs).unwrap_err();
        assert!(err.contains("invalid decimal"), "unexpected error: {err}");
    }
}
