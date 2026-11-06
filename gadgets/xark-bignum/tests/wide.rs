//! `mod_mul` at 24×86-bit limbs (RSA-2048 width) against
//! `examples/bignum_wide`: honest products solve for extreme operands (every
//! limb at its maximum, a single top limb, zero), the circuit is
//! analyzer-clean, and a wrong product is rejected.

use std::collections::BTreeMap;

use num_bigint::BigUint;
use xark_ir::{primitive, solver};

fn load() -> primitive::PrimitiveProgram {
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/bignum_wide/src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "bignum_wide", "bn254");
    assert!(
        c.status_success,
        "compiling examples/bignum_wide failed: {}",
        c.stderr
    );
    c.program()
}

fn limbs(x: &BigUint) -> Vec<String> {
    let mask = (BigUint::from(1u8) << 86u32) - 1u8;
    (0..24)
        .map(|i| ((x >> (86u32 * i)) & &mask).to_string())
        .collect()
}

fn inputs(
    p: &primitive::PrimitiveProgram,
    a: &BigUint,
    b: &BigUint,
    m: &BigUint,
    c: &BigUint,
) -> BTreeMap<u32, String> {
    let id = |n: &str| {
        p.vars
            .iter()
            .find(|v| v.name == n)
            .unwrap_or_else(|| panic!("missing `{n}`"))
            .id
    };
    let mut out = BTreeMap::new();
    for (name, value) in [("a", a), ("b", b), ("m", m), ("c", c)] {
        for (i, l) in limbs(value).into_iter().enumerate() {
            out.insert(id(&format!("{name}[{i}]")), l);
        }
    }
    out
}

#[test]
fn rsa_width_products_solve_and_are_sound() {
    let p = load();
    let one = BigUint::from(1u8);
    // An odd 2048-bit modulus with every limb near 2^86.
    let m = (&one << 2048u32) - BigUint::from(159u8);
    let max = &m - &one;
    let cases = [
        (max.clone(), max.clone()),        // (−1)² = 1: the largest columns
        (max.clone(), BigUint::from(2u8)), // −2
        ((&one << 2047u32) + &one, max.clone()),
        (BigUint::from(0u8), max.clone()),
    ];
    for (a, b) in &cases {
        let c = (a * b) % &m;
        let assign = solver::solve_and_check(&p, &inputs(&p, a, b, &m, &c))
            .unwrap_or_else(|e| panic!("honest product must solve: {e:?}"));
        let holes = solver::analyze_underconstrained(&p, &assign);
        assert!(holes.is_empty(), "under-constrained: {holes:?}");
    }
    // Operands with only their top limb set: the low columns of `a·b` are
    // empty while `q·m` fills them, so the carries run negative.
    let top = &one << 2047u32;
    let c = (&top * &top) % &m;
    let assign = solver::solve_and_check(&p, &inputs(&p, &top, &top, &m, &c))
        .unwrap_or_else(|e| panic!("worst-case carries must solve: {e:?}"));
    assert!(solver::analyze_underconstrained(&p, &assign).is_empty());

    let c = (&max * &max) % &m + &one;
    assert!(
        solver::solve_and_check(&p, &inputs(&p, &max, &max, &m, &c)).is_err(),
        "a wrong product must be rejected"
    );
}
