//! The generic comparison and multiplication gadgets end to end: compile a circuit,
//! solve it, and check the result against `num-bigint`.
//!
//! * KATs: `require_lt` accepts exactly the `x ≤ m − 1` (0, 1, m − 1, values that
//!   differ from m − 1 only below the top limb) and rejects m, m + 1 and the
//!   all-max-limbs value; `mod_mul` returns `a·b mod m` (0, 1, m − 1, (m − 1)²,
//!   random), at 3 × 86 (secp256r1 p, variable modulus) and 4 × 64 (secp256k1 n,
//!   64-bit hints; run in release mode, bug-checklist item 14).
//! * Forged hints: on every accepted witness, every derived variable (each hint
//!   output: comparison bits, quotient and remainder limbs, carry bits, products)
//!   tampered on its own makes some row fail, and the under-constraint analysis
//!   finds no free variable (bug-checklist items 4, 7, 8).

use std::collections::BTreeMap;

use num_bigint::BigUint;
use xark_ir::primitive::{PrimitiveProgram, VarRole};
use xark_ir::solver;

const P256: &str = "115792089210356748548787541520818768451331658744611719806431386787614765031433";
const K1N: &str = "115792089237316195423570985008687907852837564279074904382605163141518161494337";

fn big(s: &str) -> BigUint {
    BigUint::parse_bytes(s.as_bytes(), 10).unwrap()
}

fn limbs(v: &BigUint, n: usize, bits: u32) -> Vec<String> {
    let mask = (BigUint::from(1u8) << bits) - 1u8;
    (0..n)
        .map(|i| ((v >> (bits * i as u32)) & &mask).to_string())
        .collect()
}

fn compile(name: &str, body: &str) -> PrimitiveProgram {
    let src = format!("#![no_std]\nuse xark::prelude::*;\nuse xark_bignum::*;\n{body}");
    let c = xark_test_harness::compile_source(name, &src, "bn254");
    assert!(c.status_success, "{name}: {}", c.stderr);
    c.program()
}

fn inputs(p: &PrimitiveProgram, vals: &[(&str, Vec<String>)]) -> BTreeMap<u32, String> {
    let mut m = BTreeMap::new();
    for (name, ls) in vals {
        for (i, l) in ls.iter().enumerate() {
            let id = p
                .vars
                .iter()
                .find(|v| v.name == format!("{name}[{i}]"))
                .unwrap_or_else(|| panic!("no input {name}[{i}]"))
                .id;
            m.insert(id, l.clone());
        }
    }
    m
}

/// The witness for `ins` is accepted, nothing in it is free, and each derived
/// variable, bumped by one on its own, makes a row fail.
fn accepts_and_rejects_forgeries(p: &PrimitiveProgram, ins: &BTreeMap<u32, String>, what: &str) {
    let assign = solver::solve_and_check(p, ins).unwrap_or_else(|e| panic!("{what}: {e:?}"));
    let holes = solver::analyze_underconstrained(p, &assign);
    assert!(holes.is_empty(), "{what}: under-constrained {holes:?}");
    let mut forged = 0;
    for v in p.vars.iter().filter(|v| v.role == VarRole::Derived) {
        let Some(val) = assign.get(&v.id) else {
            continue;
        };
        let mut bad = assign.clone();
        let bumped = big(&val.to_decimal()) + 1u8;
        bad.insert(v.id, solver::fp_from_decimal(&bumped.to_string(), p));
        assert!(
            solver::check(p, &bad).is_err(),
            "{what}: tampering {} still satisfies every row",
            v.name
        );
        forged += 1;
    }
    assert!(forged > 0, "{what}: no derived variables");
}

#[test]
fn require_lt_accepts_exactly_below_the_modulus() {
    let p = compile(
        "forged_require_lt",
        "#[circuit]\npub fn circuit(x: Private<[Field; 3]>, m1: Public<[Field; 3]>) {\n\
         \x20   xark_bignum::require_lt::<3, 86>(x, m1);\n}\n",
    );
    let m = big(P256);
    let m1 = &m - 1u8;
    let top = BigUint::from(1u8) << 172;
    let ok = [
        BigUint::from(0u8),
        BigUint::from(1u8),
        m1.clone(),
        &m1 - 1u8,
        // equal top limb, smaller middle limb, larger low limb
        (&m1 / &top) * &top + ((BigUint::from(1u8) << 86) - 1u8),
    ];
    for x in &ok {
        let ins = inputs(&p, &[("x", limbs(x, 3, 86)), ("m1", limbs(&m1, 3, 86))]);
        accepts_and_rejects_forgeries(&p, &ins, &format!("require_lt({x})"));
    }
    let all_max = (BigUint::from(1u8) << 258) - 1u8;
    for x in [
        m.clone(),
        &m + 1u8,
        all_max,
        &m1 + (BigUint::from(1u8) << 86),
    ] {
        let ins = inputs(&p, &[("x", limbs(&x, 3, 86)), ("m1", limbs(&m1, 3, 86))]);
        assert!(
            solver::solve_and_check(&p, &ins).is_err(),
            "require_lt({x}) must be rejected"
        );
    }
}

fn mod_mul_kats(p: &PrimitiveProgram, n: usize, bits: u32, m: &BigUint, var_m: bool) {
    let mut seed = 0x2545_f491_4f6c_dd1du64;
    let mut rnd = || {
        let mut v = BigUint::from(0u8);
        for _ in 0..5 {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            v = (v << 64) + seed;
        }
        v % m
    };
    let m1 = m - 1u8;
    let cases = [
        (BigUint::from(0u8), m1.clone()),
        (BigUint::from(1u8), m1.clone()),
        (m1.clone(), m1.clone()),
        (rnd(), rnd()),
        (rnd(), rnd()),
    ];
    for (a, b) in cases {
        let want = (&a * &b) % m;
        let mut vals = vec![
            ("a", limbs(&a, n, bits)),
            ("b", limbs(&b, n, bits)),
            ("o", limbs(&want, n, bits)),
        ];
        if var_m {
            vals.push(("m", limbs(m, n, bits)));
        }
        let ins = inputs(p, &vals);
        accepts_and_rejects_forgeries(p, &ins, &format!("mod_mul({a}, {b})"));
        // a wrong claimed product (the remainder plus m, and plus one) is rejected
        for wrong in [&want + m, &want + 1u8] {
            let mut ins = ins.clone();
            let w = inputs(p, &[("o", limbs(&wrong, n, bits))]);
            ins.extend(w);
            assert!(
                solver::solve_and_check(p, &ins).is_err(),
                "mod_mul({a}, {b}) = {wrong} must be rejected"
            );
        }
    }
}

#[test]
fn mod_mul_3x86_variable_modulus_matches_num_bigint() {
    let p = compile(
        "forged_mod_mul_3x86",
        "#[circuit]\npub fn circuit(a: Private<[Field; 3]>, b: Private<[Field; 3]>, \
         m: Public<[Field; 3]>, o: Public<[Field; 3]>) {\n\
         \x20   range_check_limbs::<3, 86>(a);\n\x20   range_check_limbs::<3, 86>(b);\n\
         \x20   range_check_limbs::<3, 86>(m);\n\
         \x20   let r = mod_mul::<3, 86>(a, b, m);\n\
         \x20   let mut i = 0;\n\x20   while i < 3 { require_eq(r[i], o[i]); i += 1; }\n}\n",
    );
    mod_mul_kats(&p, 3, 86, &big(P256), true);
}

#[test]
fn mod_mul_4x64_constant_modulus_matches_num_bigint() {
    let p = compile(
        "forged_mod_mul_4x64",
        &format!(
            "const N: [Field; 4] = modulus_limbs::<4, 64>(\"{K1N}\");\n\
             #[circuit]\npub fn circuit(a: Private<[Field; 4]>, b: Private<[Field; 4]>, \
             o: Public<[Field; 4]>) {{\n\
             \x20   range_check_limbs::<4, 64>(a);\n\x20   range_check_limbs::<4, 64>(b);\n\
             \x20   let r = mod_mul::<4, 64>(a, b, N);\n\
             \x20   let mut i = 0;\n\x20   while i < 4 {{ require_eq(r[i], o[i]); i += 1; }}\n}}\n"
        ),
    );
    mod_mul_kats(&p, 4, 64, &big(K1N), false);
}
