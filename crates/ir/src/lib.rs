//! `xark-ir`: the intermediate representation ("xark-ir") and R1CS data
//! structures shared between the compiler and any downstream tooling.
//!
//! This crate is deliberately free of any `rustc` dependency so it can be
//! unit-tested on stable and reused elsewhere.

pub mod bytecode;
pub mod circuit;
pub mod diagnose;
pub mod field;
pub mod function_decode;
pub mod graph;
pub mod json;
pub mod linear_combination;
pub mod minimize;
pub mod primitive;
pub mod profile;
pub mod r1cs;
pub mod r1cs_cache;
pub mod solver;

pub use circuit::{CircuitProgram, R1csRow, expr_from_r1cs};
pub use field::FieldConst;
pub use graph::to_dot;
pub use json::to_json_pretty;
pub use linear_combination::{LinearCombination, Term, VarId};
pub use minimize::minimize;
pub use profile::{ConstraintKind, ConstraintProfile, ProfileProgram};
pub use r1cs::{DebugInfo, FieldSpec, R1csConstraint, R1csProgram, Variable, Visibility};

/// Developer-diagnostics env-flag probe. Only reads the environment when the
/// `debug` feature is enabled; a normal release build compiles this to `false`
/// so the diagnostic branches (and their `XARK_*` knobs) vanish entirely.
#[inline]
pub(crate) fn dbg_flag(name: &str) -> bool {
    #[cfg(feature = "debug")]
    {
        std::env::var(name).is_ok()
    }
    #[cfg(not(feature = "debug"))]
    {
        let _ = name;
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Manually construct the cube circuit:
    ///   a * a = t0
    ///   t0 * a = c
    fn cube_program() -> R1csProgram {
        let a = 0u32;
        let c = 1u32;
        let t0 = 2u32;

        let variables = vec![
            Variable {
                id: a,
                name: "a".into(),
                visibility: Visibility::Private,
            },
            Variable {
                id: c,
                name: "c".into(),
                visibility: Visibility::Public,
            },
            Variable {
                id: t0,
                name: "t0".into(),
                visibility: Visibility::Internal,
            },
        ];

        let constraints = vec![
            R1csConstraint::mul(
                0,
                LinearCombination::var(a),
                LinearCombination::var(a),
                t0,
                "a * a = t0",
            ),
            R1csConstraint::mul(
                1,
                LinearCombination::var(t0),
                LinearCombination::var(a),
                c,
                "t0 * a = c",
            ),
        ];

        R1csProgram {
            field: FieldSpec::unknown(),
            variables,
            constraints,
        }
    }

    #[test]
    fn cube_json_roundtrips() {
        let program = cube_program();
        let json = to_json_pretty(&program);
        assert!(json.contains("\"name\": \"a\""));
        assert!(json.contains("\"visibility\": \"Private\""));
        assert!(json.contains("\"note\": \"a * a = t0\""));
        assert_eq!(program.constraints.len(), 2);
    }

    #[test]
    fn cube_dot_has_expected_edges() {
        let program = cube_program();
        let dot = to_dot(&program);
        // a feeds both constraints; constraint0 produces t0; constraint1 produces c.
        assert!(dot.contains("v0 -> constraint0;"));
        assert!(dot.contains("constraint0 -> v2;"));
        assert!(dot.contains("v2 -> constraint1;"));
        assert!(dot.contains("constraint1 -> v1;"));
    }

    #[test]
    fn difference_of_squares_is_one_constraint() {
        // (x + y) * (x - y) = z
        let x = 0u32;
        let y = 1u32;
        let z = 2u32;

        let lhs = LinearCombination::var(x) + LinearCombination::var(y);
        let rhs = LinearCombination::var(x) - LinearCombination::var(y);

        let program = R1csProgram {
            field: FieldSpec::unknown(),
            variables: vec![
                Variable {
                    id: x,
                    name: "x".into(),
                    visibility: Visibility::Private,
                },
                Variable {
                    id: y,
                    name: "y".into(),
                    visibility: Visibility::Private,
                },
                Variable {
                    id: z,
                    name: "z".into(),
                    visibility: Visibility::Public,
                },
            ],
            constraints: vec![R1csConstraint::mul(0, lhs, rhs, z, "(x + y) * (x - y) = z")],
        };

        assert_eq!(program.constraints.len(), 1);
        // The `a` side should carry both x and y with coeff 1.
        let a = &program.constraints[0].a;
        assert_eq!(a.terms.len(), 2);
    }

    #[test]
    fn mulmod_divmod_hint_computes_big_division() {
        use crate::primitive::*;
        use crate::solver::solve;
        use num_bigint::BigUint;
        use std::collections::BTreeMap;

        // secp256k1 base field modulus, as 4 little-endian 64-bit limbs.
        let m_limbs = [
            "18446744069414583343",
            "18446744073709551615",
            "18446744073709551615",
            "18446744073709551615",
        ];
        // A, B as limb values (A, B < M).
        let a_vals = ["1", "2", "3", "4"];
        let b_vals = ["5", "6", "7", "8"];

        let mut vars = Vec::new();
        for (i, n) in ["a0", "a1", "a2", "a3", "b0", "b1", "b2", "b3"]
            .iter()
            .enumerate()
        {
            vars.push(Var {
                id: i as u32,
                name: n.to_string(),
                role: VarRole::PrivateInput,
            });
        }
        for (i, n) in ["q0", "q1", "q2", "q3", "r0", "r1", "r2", "r3"]
            .iter()
            .enumerate()
        {
            vars.push(Var {
                id: 8 + i as u32,
                name: n.to_string(),
                role: VarRole::Derived,
            });
        }
        let program = PrimitiveProgram {
            field: FieldSpec::bn254(),
            vars,
            constraints: vec![],
            witness_gen: vec![WitnessGen::MulModDivMod {
                q: vec![8, 9, 10, 11],
                r: vec![12, 13, 14, 15],
                a: (0..4).map(LinearCombination::var).collect(),
                b: (4..8).map(LinearCombination::var).collect(),
                modulus: m_limbs
                    .iter()
                    .map(|s| LinearCombination::constant(*s))
                    .collect(),
                limb_bits: 64,
            }],
        };

        let mut inputs = BTreeMap::new();
        for (i, v) in a_vals.iter().enumerate() {
            inputs.insert(i as u32, v.to_string());
        }
        for (i, v) in b_vals.iter().enumerate() {
            inputs.insert(4 + i as u32, v.to_string());
        }
        let assign = solve(&program, &inputs).unwrap();

        let recompose = |ids: &[u32]| -> BigUint {
            let mut acc = BigUint::from(0u32);
            for (i, &id) in ids.iter().enumerate() {
                let v: BigUint = assign[&id].to_decimal().parse().unwrap();
                acc += v << (64 * i);
            }
            acc
        };
        let a: BigUint = a_vals
            .iter()
            .enumerate()
            .map(|(i, s)| s.parse::<BigUint>().unwrap() << (64 * i))
            .sum();
        let b: BigUint = b_vals
            .iter()
            .enumerate()
            .map(|(i, s)| s.parse::<BigUint>().unwrap() << (64 * i))
            .sum();
        let m: BigUint = m_limbs
            .iter()
            .enumerate()
            .map(|(i, s)| s.parse::<BigUint>().unwrap() << (64 * i))
            .sum();
        let q = recompose(&[8, 9, 10, 11]);
        let r = recompose(&[12, 13, 14, 15]);

        // The division identity: A·B = q·M + r, with 0 <= r < M.
        assert_eq!(&q * &m + &r, &a * &b, "q*M + r must equal A*B");
        assert!(r < m, "remainder must be < modulus");
        assert_eq!(&r, &((&a * &b) % &m), "r must be A*B mod M");
    }

    #[test]
    fn analyzer_passes_sound_and_flags_underconstraints() {
        use crate::primitive::*;
        use crate::solver::{analyze_underconstrained, solve};
        use std::collections::BTreeMap;

        let mul_expr = |l: u32, r: u32, out: u32| Expression {
            mul_terms: vec![MulTerm {
                coeff: FieldConst::one(),
                left: l,
                right: r,
            }],
            linear_terms: vec![LinearTerm {
                coeff: FieldConst::from_i64(-1),
                var: out,
            }],
            constant: FieldConst::zero(),
            note: None,
        };

        // SOUND: t = a*b, pinned by `a*b - t = 0`.
        let sound = PrimitiveProgram {
            field: FieldSpec::bn254(),
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
                    name: "t".into(),
                    role: VarRole::Derived,
                },
            ],
            constraints: vec![mul_expr(0, 1, 2)],
            witness_gen: vec![WitnessGen::Product {
                out: 2,
                left: LinearCombination::var(0),
                right: LinearCombination::var(1),
            }],
        };
        let mut inputs = BTreeMap::new();
        inputs.insert(0u32, "3".to_string());
        inputs.insert(1u32, "4".to_string());
        let assign = solve(&sound, &inputs).unwrap();
        assert!(
            analyze_underconstrained(&sound, &assign).is_empty(),
            "a fully-pinned circuit must report no under-constraints"
        );

        // UNSOUND 1 — dangling advice: `w` is computed but no constraint pins it.
        let mut dangling = sound.clone();
        dangling.vars.push(Var {
            id: 3,
            name: "w".into(),
            role: VarRole::Derived,
        });
        dangling.witness_gen.push(WitnessGen::Inverse {
            out: 3,
            input: LinearCombination::var(0),
        });
        let assign = solve(&dangling, &inputs).unwrap();
        let flags = analyze_underconstrained(&dangling, &assign);
        assert!(
            flags.iter().any(|f| f.name == "w"),
            "dangling advice must be flagged: {flags:?}"
        );

        // UNSOUND 2 — two-valued: a bit constrained only by booleanity (b*b = b),
        // with no recomposition/pin, can be 0 or 1.
        let two_valued = PrimitiveProgram {
            field: FieldSpec::bn254(),
            vars: vec![Var {
                id: 0,
                name: "bit".into(),
                role: VarRole::Derived,
            }],
            constraints: vec![Expression {
                mul_terms: vec![MulTerm {
                    coeff: FieldConst::one(),
                    left: 0,
                    right: 0,
                }],
                linear_terms: vec![LinearTerm {
                    coeff: FieldConst::from_i64(-1),
                    var: 0,
                }],
                constant: FieldConst::zero(),
                note: None,
            }],
            witness_gen: vec![WitnessGen::Bit {
                out: 0,
                input: LinearCombination::constant("1"),
                index: 0,
            }],
        };
        let assign = solve(&two_valued, &BTreeMap::new()).unwrap();
        let flags = analyze_underconstrained(&two_valued, &assign);
        assert!(
            flags.iter().any(|f| f.name == "bit"),
            "a booleanity-only bit is two-valued and must be flagged: {flags:?}"
        );
    }

    #[test]
    fn scale_folds_and_big_constants_are_exact() {
        // 3 * (x + 2) = 3x + 6
        let x = 0u32;
        let lc = (LinearCombination::var(x) + LinearCombination::constant("2"))
            .scale(&FieldConst::from_decimal("3").unwrap());
        assert_eq!(lc.constant.decimal(), "6");
        assert_eq!(lc.terms.len(), 1);
        assert_eq!(lc.terms[0].coeff.decimal(), "3");

        // Exact arithmetic on field-sized values (no i64 overflow).
        let big = "21888242871839275222246405745257275088548364400416034343698204186575808495616";
        let a = FieldConst::from_decimal(big).unwrap();
        let sum = a.add(&FieldConst::one());
        assert_eq!(
            sum.decimal(),
            "21888242871839275222246405745257275088548364400416034343698204186575808495617"
        );
    }

    #[test]
    fn primitive_ir_bit_decompose_solves_and_checks() {
        use crate::primitive::*;
        use crate::solver::solve_and_check;
        use std::collections::BTreeMap;

        // A hand-built 8-bit decomposition circuit in the primitive IR:
        //   private input x = var 0
        //   derived bits w0..w7 = vars 1..=8
        //   witness-gen: bits = bit_decompose(x)
        //   constraints: each bit boolean (w*w - w = 0) + recomposition (Σ 2^i wi - x = 0)
        let x = 0u32;
        let bit_ids: Vec<u32> = (1..=8).collect();

        let mut vars = vec![Var {
            id: x,
            name: "x".into(),
            role: VarRole::PrivateInput,
        }];
        for (i, id) in bit_ids.iter().enumerate() {
            vars.push(Var {
                id: *id,
                name: format!("w{i}"),
                role: VarRole::Derived,
            });
        }

        let mut constraints = Vec::new();
        // Booleanity: w*w - w = 0.
        for id in &bit_ids {
            constraints.push(Expression {
                mul_terms: vec![MulTerm {
                    coeff: FieldConst::one(),
                    left: *id,
                    right: *id,
                }],
                linear_terms: vec![LinearTerm {
                    coeff: FieldConst::from_i64(-1),
                    var: *id,
                }],
                constant: FieldConst::zero(),
                note: Some(format!("w{id} boolean")),
            });
        }
        // Recomposition: Σ 2^i wi - x = 0.
        let mut linear_terms = vec![LinearTerm {
            coeff: FieldConst::from_i64(-1),
            var: x,
        }];
        for (i, id) in bit_ids.iter().enumerate() {
            linear_terms.push(LinearTerm {
                coeff: FieldConst::from_i64(1i64 << i),
                var: *id,
            });
        }
        constraints.push(Expression {
            mul_terms: vec![],
            linear_terms,
            constant: FieldConst::zero(),
            note: Some("recomposition".into()),
        });

        let program = PrimitiveProgram {
            field: FieldSpec::bn254(),
            vars,
            constraints,
            witness_gen: bit_ids
                .iter()
                .enumerate()
                .map(|(i, id)| WitnessGen::Bit {
                    out: *id,
                    input: LinearCombination::var(x),
                    index: i as u32,
                })
                .collect(),
        };

        // Solve for x = 181 = 0b10110101 and check all constraints hold.
        let mut inputs = BTreeMap::new();
        inputs.insert(x, "181".to_string());
        let assign = solve_and_check(&program, &inputs).expect("witness solves + constraints hold");

        // Verify the computed bits are the little-endian binary of 181.
        let expected = [1, 0, 1, 0, 1, 1, 0, 1]; // 181
        for (i, id) in bit_ids.iter().enumerate() {
            assert_eq!(assign[id].to_decimal(), expected[i].to_string(), "bit {i}");
        }
    }

    #[test]
    fn lc_simplification_combines_and_drops() {
        // x + x - 2x = 0  (no terms remain)
        let x = 5u32;
        let lc = LinearCombination::var(x) + LinearCombination::var(x)
            - LinearCombination {
                constant: FieldConst::zero(),
                terms: vec![Term {
                    coeff: FieldConst::from_i64(2),
                    var: x,
                }],
            };
        assert!(lc.terms.is_empty(), "2x - 2x should cancel: {lc:?}");
    }
}
