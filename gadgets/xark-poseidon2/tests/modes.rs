//! The domain-separated modes (`commit`, `nullifier`, `encrypt`/`decrypt`) and the
//! Fiat–Shamir `challenge`, against `poseidon2_ref.py` (which writes them from their
//! definitions, the encryption with the paper's zero padding), in a circuit and
//! natively. A circuit must accept the reference values and refuse a changed one:
//! for `decrypt`, a wrong key or nonce, a changed ciphertext element or tag.

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
const KEY: u64 = 123_456_789;
const NONCE: u64 = 42;
/// `encrypt(KEY, NONCE, [10, 11, 12])`: the ciphertext, then the tag.
const ENC_3: [&str; 4] = [
    "542663946192589838133460107101816892738666137983613942915370787155408987833",
    "4154875339721954462662900302236641642615963054759252672359497994734470297905",
    "14618528529411687673436746933590505467544694387242946331906959716917406637884",
    "14505114595764655204677295775782525172158035260596553999717939141079569455416",
];
/// `encrypt(KEY, NONCE, [10, 11, 12, 13])`: the ciphertext, then the tag.
const ENC_4: [&str; 5] = [
    "7483010542729630065628704629882151903886681536576636019129150314612051460250",
    "3056175669403028990714533086233321216331118890850405067376741716094899005478",
    "20994353557070844132196980424448524388708856688660407639757157595599757168864",
    "8523067983216076462757073926334744511702913378497658240991081220955401410403",
    "4343177215445392565198508265123717181454445132937978959968376953971657733266",
];
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

    let (key, nonce) = (Fr::from(KEY), Fr::from(NONCE));
    let (ct, tag) = native::encrypt(key, nonce, small::<3>(10));
    assert_eq!(ct.map(dec), ENC_3[..3]);
    assert_eq!(dec(tag), ENC_3[3]);
    let (ct, tag) = native::encrypt_slice(key, nonce, &small::<4>(10));
    assert_eq!(ct.into_iter().map(dec).collect::<Vec<_>>(), ENC_4[..4]);
    assert_eq!(dec(tag), ENC_4[4]);

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
fn native_decrypt_round_trips_and_refuses_tampering() {
    let (key, nonce) = (Fr::from(KEY), Fr::from(NONCE));
    for n in 1..=5usize {
        let msg: Vec<Fr> = (0..n as u64).map(|i| Fr::from(1000 + i)).collect();
        let (ct, tag) = native::encrypt_slice(key, nonce, &msg);
        // The keystream hides the message.
        assert!(ct.iter().zip(&msg).all(|(c, m)| c != m));
        assert_eq!(native::decrypt_slice(key, nonce, &ct, tag), Some(msg));
        let one = Fr::from(1u64);
        assert_eq!(native::decrypt_slice(key + one, nonce, &ct, tag), None);
        assert_eq!(native::decrypt_slice(key, nonce + one, &ct, tag), None);
        assert_eq!(native::decrypt_slice(key, nonce, &ct, tag + one), None);
        for i in 0..n {
            let mut bad = ct.clone();
            bad[i] += one;
            assert_eq!(
                native::decrypt_slice(key, nonce, &bad, tag),
                None,
                "{n}: {i}"
            );
        }
        // A prefix or an extension is another length, so another domain.
        assert_eq!(native::decrypt_slice(key, nonce, &ct[..n - 1], tag), None);
    }
    let (ct, tag) = native::encrypt(key, nonce, small::<3>(10));
    assert_eq!(native::decrypt(key, nonce, ct, tag), Some(small::<3>(10)));
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

const DECRYPT_SRC: &str = "#![no_std]\n\
     use xark::{require_eq, Field, Private, Public};\n\
     use xark_poseidon2::decrypt;\n\
     pub fn circuit(key: Private<Field>, nonce: Public<Field>,\n\
       c0: Public<Field>, c1: Public<Field>, c2: Public<Field>, tag: Public<Field>,\n\
       m0: Public<Field>, m1: Public<Field>, m2: Public<Field>) {\n\
       require_eq(decrypt(key, nonce, [c0, c1, c2], tag), [m0, m1, m2]);\n\
     }\n";

fn decrypt_inputs() -> Vec<(&'static str, String)> {
    vec![
        ("key", KEY.to_string()),
        ("nonce", NONCE.to_string()),
        ("c0", ENC_3[0].into()),
        ("c1", ENC_3[1].into()),
        ("c2", ENC_3[2].into()),
        ("tag", ENC_3[3].into()),
        ("m0", "10".into()),
        ("m1", "11".into()),
        ("m2", "12".into()),
    ]
}

#[test]
fn decrypt_in_a_circuit() {
    let p = compile("p2_decrypt", DECRYPT_SRC);
    eprintln!("decrypt::<3>: {} constraints", p.constraints.len());
    let ok = decrypt_inputs();
    check(&p, &ok).expect("the reference ciphertext decrypts");
    let bump = |name: &str| {
        let v = fr(&ok.iter().find(|(n, _)| *n == name).unwrap().1);
        with(&ok, name, v + Fr::from(1u64))
    };
    for name in ["key", "nonce", "c0", "c1", "c2", "tag", "m0", "m2"] {
        assert!(check(&p, &bump(name)).is_err(), "{name} changed, accepted");
    }
}

/// Only the tag refuses here: the message isn't compared with anything, so a
/// wrong key, nonce or ciphertext is caught by the tag's row alone.
#[test]
fn decrypt_constrains_the_tag() {
    let p = compile(
        "p2_decrypt_tag",
        "#![no_std]\n\
         use xark::{Field, Private, Public};\n\
         use xark_poseidon2::decrypt;\n\
         pub fn circuit(key: Private<Field>, nonce: Public<Field>,\n\
           c0: Public<Field>, c1: Public<Field>, c2: Public<Field>, tag: Public<Field>) {\n\
           let _ = decrypt(key, nonce, [c0, c1, c2], tag);\n\
         }\n",
    );
    let ok: Vec<_> = decrypt_inputs().into_iter().take(6).collect();
    check(&p, &ok).expect("the reference ciphertext decrypts");
    assert!(any_witness(&p, &ok));
    for name in ["key", "nonce", "c0", "c1", "c2", "tag"] {
        let v = fr(&ok.iter().find(|(n, _)| *n == name).unwrap().1);
        let bad = with(&ok, name, v + Fr::from(1u64));
        assert!(check(&p, &bad).is_err(), "{name} changed, accepted");
        assert!(
            !any_witness(&p, &bad),
            "{name} changed: some witness proves it"
        );
    }
}

#[test]
fn encrypt_in_a_circuit() {
    let p = compile(
        "p2_encrypt",
        "#![no_std]\n\
         use xark::{require_eq, Field, Private, Public};\n\
         use xark_poseidon2::encrypt;\n\
         pub fn circuit(key: Private<Field>, nonce: Public<Field>,\n\
           m0: Private<Field>, m1: Private<Field>, m2: Private<Field>, m3: Private<Field>,\n\
           c0: Public<Field>, c1: Public<Field>, c2: Public<Field>, c3: Public<Field>,\n\
           tag: Public<Field>) {\n\
           let (ct, t) = encrypt(key, nonce, [m0, m1, m2, m3]);\n\
           require_eq(ct, [c0, c1, c2, c3]);\n\
           require_eq(t, tag);\n\
         }\n",
    );
    eprintln!("encrypt::<4>: {} constraints", p.constraints.len());
    let mut ok: Vec<(&str, String)> = vec![("key", KEY.to_string()), ("nonce", NONCE.to_string())];
    for (i, name) in ["m0", "m1", "m2", "m3"].into_iter().enumerate() {
        ok.push((name, (10 + i).to_string()));
    }
    for (i, name) in ["c0", "c1", "c2", "c3", "tag"].into_iter().enumerate() {
        ok.push((name, ENC_4[i].into()));
    }
    check(&p, &ok).expect("the reference encryption");
    for name in ["key", "nonce", "m1", "c3", "tag"] {
        let v = fr(&ok.iter().find(|(n, _)| *n == name).unwrap().1);
        assert!(
            check(&p, &with(&ok, name, v + Fr::from(1u64))).is_err(),
            "{name}"
        );
    }
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
