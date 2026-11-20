//! The domain-separated modes (`commit`, `nullifier`) and the Fiat–Shamir
//! `challenge`, against `poseidon2_ref.py` (which writes them from their
//! definitions), in a circuit and natively. A circuit must accept the reference
//! values and refuse a changed one.

use std::collections::BTreeMap;

use ark_ff::PrimeField;
use xark_ir::primitive::PrimitiveProgram;
use xark_ir::solver;
use xark_poseidon2::native::{self, Fr};

fn compile(name: &str, src: &str) -> PrimitiveProgram {
    let c = xark_test_harness::compile_source(name, src, "bn254");
    assert!(c.status_success, "compile failed for {name}: {}", c.stderr);
    c.program()
}

fn fr(s: &str) -> Fr {
    s.parse().unwrap()
}

fn dec(x: Fr) -> String {
    x.into_bigint().to_string()
}

/// Solve `p` with the named inputs; `Ok` only if every row holds, and then no
/// variable is left free (the analyzer finds none under-constrained).
fn check(p: &PrimitiveProgram, inputs: &[(&str, String)]) -> Result<(), String> {
    let ids: BTreeMap<u32, String> = inputs
        .iter()
        .map(|(n, v)| {
            let id = p
                .vars
                .iter()
                .find(|x| x.name == *n)
                .unwrap_or_else(|| panic!("no input {n}"))
                .id;
            (id, v.clone())
        })
        .collect();
    let assign = solver::solve_and_check(p, &ids).map_err(|e| e.to_string())?;
    let holes = solver::analyze_underconstrained(p, &assign);
    assert!(holes.is_empty(), "under-constrained: {holes:?}");
    Ok(())
}

/// Whether any witness at all satisfies `p` with these inputs, by exhaustive
/// search (the adversary, not the honest solver): `true` when exactly one does,
/// `false` when none does; panics on two, or when the search can't decide.
fn any_witness(p: &PrimitiveProgram, inputs: &[(&str, String)]) -> bool {
    use xark_ir::witness_search::{WitnessSearch, search_witnesses};
    let ids: BTreeMap<u32, String> = inputs
        .iter()
        .map(|(n, v)| (p.vars.iter().find(|x| x.name == *n).unwrap().id, v.clone()))
        .collect();
    match search_witnesses(p, &ids, 1 << 14).unwrap() {
        WitnessSearch::Unique(_) => true,
        WitnessSearch::None => false,
        other => panic!("{inputs:?}: {other:?}"),
    }
}

/// `inputs` with `name` set to `value`.
fn with(inputs: &[(&'static str, String)], name: &str, value: Fr) -> Vec<(&'static str, String)> {
    let mut out = inputs.to_vec();
    out.iter_mut().find(|(n, _)| *n == name).unwrap().1 = dec(value);
    out
}

// `poseidon2_ref.py`'s vectors.
const COMMIT_123: &str =
    "17634564540255296520186148110660714497980376341407394513010947673015055999934";
const NULLIFIER_123: &str =
    "1583281705540343901485297543298824336757279061095191133038142125609155856497";
const HASH_123: &str =
    "8643882004926979398976878054694415684746477902129629285229035462626682758314";
const COMMIT_7: &str =
    "15950498345642247832949867160514133476228944591577742485896208174270673760689";
/// `challenge([1, …, 14], 128)`: the low 128 bits of `hash([1, …, 14])`.
const CHALLENGE_14: &str = "199900922183828828745530948332741639722";

fn small<const N: usize>(from: u64) -> [Fr; N] {
    core::array::from_fn(|i| Fr::from(from + i as u64))
}

#[test]
fn native_modes_match_the_reference() {
    let x = small::<3>(1);
    assert_eq!(native::commit(x), fr(COMMIT_123));
    assert_eq!(native::commit_slice(&x), fr(COMMIT_123));
    assert_eq!(native::nullifier(x), fr(NULLIFIER_123));
    assert_eq!(native::nullifier_slice(&x), fr(NULLIFIER_123));
    assert_eq!(native::hash(x), fr(HASH_123));
    assert_eq!(native::commit([Fr::from(7u64)]), fr(COMMIT_7));

    assert_eq!(
        native::challenge::<14, 128>(small::<14>(1)),
        fr(CHALLENGE_14)
    );
}

/// A commitment is no nullifier, hash or Merkle node of the same inputs: each
/// starts its sponge from another capacity value.
#[test]
fn domains_are_separate() {
    let (a, b) = (Fr::from(5u64), Fr::from(6u64));
    let values = [
        native::commit([a, b]),
        native::nullifier([a, b]),
        native::hash([a, b]),
        native::hash2(a, b),
    ];
    for i in 0..values.len() {
        for j in 0..i {
            assert_ne!(values[i], values[j], "modes {i} and {j} agree");
        }
    }
    // The length is in the domain too: a trailing zero changes the commitment.
    assert_ne!(native::commit([a]), native::commit([a, Fr::from(0u64)]));
}

#[test]
fn commit_and_nullifier_in_a_circuit() {
    let p = compile(
        "p2_commit_nullifier",
        "#![no_std]\n\
         use xark::{require_eq, Field, Private, Public};\n\
         use xark_poseidon2::{commit, nullifier};\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>, c: Private<Field>,\n\
           cm: Public<Field>, nf: Public<Field>) {\n\
           require_eq(commit([a, b, c]), cm);\n\
           require_eq(nullifier([a, b, c]), nf);\n\
         }\n",
    );
    eprintln!(
        "commit::<3> + nullifier::<3>: {} constraints",
        p.constraints.len()
    );
    let ok: Vec<(&str, String)> = vec![
        ("a", "1".into()),
        ("b", "2".into()),
        ("c", "3".into()),
        ("cm", COMMIT_123.into()),
        ("nf", NULLIFIER_123.into()),
    ];
    check(&p, &ok).expect("the reference commitment and nullifier");
    assert!(any_witness(&p, &ok));
    // Swapped, or the plain hash in either place: refused.
    for (name, v) in [("cm", NULLIFIER_123), ("nf", COMMIT_123), ("cm", HASH_123)] {
        assert!(check(&p, &with(&ok, name, fr(v))).is_err(), "{name} = {v}");
        assert!(!any_witness(&p, &with(&ok, name, fr(v))), "{name} = {v}");
    }
    assert!(check(&p, &with(&ok, "c", Fr::from(4u64))).is_err());
}

#[test]
fn challenge_in_a_circuit() {
    let p = compile(
        "p2_challenge",
        "#![no_std]\n\
         use xark::{require_eq, Field, Private, Public};\n\
         use xark_poseidon2::challenge;\n\
         pub fn circuit(t: Private<[Field; 14]>, c: Public<Field>) {\n\
           require_eq(Field::from_bits::<128>(challenge::<14, 128>(t)), c);\n\
         }\n",
    );
    eprintln!("challenge::<14, 128>: {} constraints", p.constraints.len());
    let mut ok: Vec<(&str, String)> = vec![("c", CHALLENGE_14.into())];
    const NAMES: [&str; 14] = [
        "t[0]", "t[1]", "t[2]", "t[3]", "t[4]", "t[5]", "t[6]", "t[7]", "t[8]", "t[9]", "t[10]",
        "t[11]", "t[12]", "t[13]",
    ];
    for (i, name) in NAMES.into_iter().enumerate() {
        ok.push((name, (i + 1).to_string()));
    }
    check(&p, &ok).expect("the reference challenge");
    assert!(check(&p, &with(&ok, "c", fr(CHALLENGE_14) + Fr::from(1u64))).is_err());
    assert!(check(&p, &with(&ok, "t[13]", Fr::from(0u64))).is_err());
}
