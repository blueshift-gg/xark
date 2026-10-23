//! R1CS program data structures.

use serde::{Deserialize, Serialize};

use crate::field::FieldConst;
use crate::linear_combination::{LinearCombination, VarId};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Visibility {
    Private,
    Public,
    Internal,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Variable {
    pub id: VarId,
    pub name: String,
    pub visibility: Visibility,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DebugInfo {
    pub source_span: Option<String>,
    pub note: Option<String>,
}

/// A single rank-1 constraint: `a * b = c`, where each of `a`, `b`, `c` is a
/// [`LinearCombination`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct R1csConstraint {
    pub id: u32,
    pub a: LinearCombination,
    pub b: LinearCombination,
    pub c: LinearCombination,
    pub debug: Option<DebugInfo>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FieldSpec {
    pub name: String,
    pub modulus_decimal: Option<String>,
}

impl FieldSpec {
    /// The MVP field spec: unknown field, no modulus.
    pub fn unknown() -> Self {
        FieldSpec {
            name: "unknown".to_string(),
            modulus_decimal: None,
        }
    }

    /// The BN254 scalar field (a.k.a. `Fr`), the common R1CS/Groth16 field.
    pub fn bn254() -> Self {
        FieldSpec {
            name: "bn254".to_string(),
            modulus_decimal: Some(
                "21888242871839275222246405745257275088548364400416034343698204186575808495617"
                    .to_string(),
            ),
        }
    }

    /// A field as a user names it (`xark build --field`): `bn254` (or `bn128`), or a
    /// prime modulus in decimal. Anything else is an error saying so.
    pub fn parse(s: &str) -> Result<Self, String> {
        let t = s.trim();
        if matches!(t, "bn254" | "bn128") {
            return Ok(FieldSpec::bn254());
        }
        let refuse = |why: &str| {
            Err(format!(
                "{s:?} {why}: name `bn254`, or give a prime modulus in decimal"
            ))
        };
        if t.is_empty() || !t.bytes().all(|b| b.is_ascii_digit()) {
            return refuse("isn't a field xark knows");
        }
        let p: num_bigint::BigUint = t.parse().expect("decimal digits");
        if !is_probable_prime(&p) {
            return refuse("isn't prime");
        }
        Ok(FieldSpec::named(&p.to_string()))
    }

    /// Look up a named field, or treat the name as a raw decimal modulus.
    pub fn named(name: &str) -> Self {
        match name {
            "bn254" | "bn128" => FieldSpec::bn254(),
            "unknown" => FieldSpec::unknown(),
            other => FieldSpec {
                name: "custom".to_string(),
                modulus_decimal: Some(other.to_string()),
            },
        }
    }
}

/// Miller–Rabin with the first 20 primes as bases: exact below 3.3·10^24, and for
/// larger moduli wrong with probability under 4^-20 (only ever a composite taken as
/// prime).
fn is_probable_prime(n: &num_bigint::BigUint) -> bool {
    use num_bigint::BigUint;
    use num_traits::{One, Zero};
    const BASES: [u32; 20] = [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    ];
    let two = BigUint::from(2u32);
    if *n < two {
        return false;
    }
    for b in BASES {
        let b = BigUint::from(b);
        if *n == b {
            return true;
        }
        if (n % &b).is_zero() {
            return false;
        }
    }
    let n1 = n - BigUint::one();
    let s = n1.trailing_zeros().unwrap_or(0);
    let d = &n1 >> s;
    'bases: for b in BASES {
        let mut x = BigUint::from(b).modpow(&d, n);
        if x.is_one() || x == n1 {
            continue;
        }
        for _ in 1..s {
            x = x.modpow(&two, n);
            if x == n1 {
                continue 'bases;
            }
        }
        return false;
    }
    true
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct R1csProgram {
    pub field: FieldSpec,
    pub variables: Vec<Variable>,
    pub constraints: Vec<R1csConstraint>,
}

impl R1csConstraint {
    /// Build a multiplication constraint `lhs * rhs = out_var`.
    pub fn mul(
        id: u32,
        lhs: LinearCombination,
        rhs: LinearCombination,
        out: VarId,
        note: &str,
    ) -> Self {
        R1csConstraint {
            id,
            a: lhs,
            b: rhs,
            c: LinearCombination::var(out),
            debug: Some(DebugInfo {
                source_span: None,
                note: Some(note.to_string()),
            }),
        }
    }

    /// Build a general constraint `a * b = c` from explicit linear combinations.
    pub fn general(
        id: u32,
        a: LinearCombination,
        b: LinearCombination,
        c: LinearCombination,
        note: &str,
    ) -> Self {
        R1csConstraint {
            id,
            a,
            b,
            c,
            debug: Some(DebugInfo {
                source_span: None,
                note: Some(note.to_string()),
            }),
        }
    }

    /// Build an equality constraint `(lhs - rhs) * 1 = 0`.
    pub fn equal(id: u32, lhs: LinearCombination, rhs: LinearCombination, note: &str) -> Self {
        R1csConstraint {
            id,
            a: lhs - rhs,
            b: LinearCombination::one(),
            c: LinearCombination {
                constant: FieldConst::zero(),
                terms: Vec::new(),
            },
            debug: Some(DebugInfo {
                source_span: None,
                note: Some(note.to_string()),
            }),
        }
    }
}

#[cfg(test)]
mod field_parse_tests {
    use super::FieldSpec;

    #[test]
    fn a_field_is_bn254_or_a_prime() {
        assert_eq!(FieldSpec::parse("bn254").unwrap(), FieldSpec::bn254());
        assert_eq!(FieldSpec::parse("bn128").unwrap(), FieldSpec::bn254());
        assert_eq!(
            FieldSpec::parse("7").unwrap().modulus_decimal.as_deref(),
            Some("7")
        );
        // The Grumpkin/BN254 base field, and a Mersenne prime past 2^64.
        for p in [
            "21888242871839275222246405745257275088696311157297823662689037894645226208583",
            "170141183460469231731687303715884105727",
        ] {
            assert!(FieldSpec::parse(p).is_ok(), "{p}");
        }
        for (s, why) in [
            ("banana", "isn't a field xark knows"),
            ("", "isn't a field xark knows"),
            ("-7", "isn't a field xark knows"),
            ("0x07", "isn't a field xark knows"),
            ("1", "isn't prime"),
            ("9", "isn't prime"),
            ("3215031751", "isn't prime"), // a strong pseudoprime to bases 2, 3, 5, 7
        ] {
            let e = FieldSpec::parse(s).unwrap_err();
            assert!(e.contains(why), "{s}: {e}");
        }
    }
}
