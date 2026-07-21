//! Solve-and-check the Merkle membership gadget against `examples/merkle`
//! (`merkle_verify(leaf, siblings, index_bits, root)`, depth 4, Poseidon
//! compression). Confirms: (1) an honest path to the correct root is accepted and
//! the circuit is analyzer-clean (every mux/booleanity/hash var is pinned — the
//! soundness smoke test), (2) a wrong root is rejected, and (3) a tampered
//! sibling (with the honest root) is rejected.
//!
//! The correct root is *derived*, not hardcoded: `xark::Field` does no real field
//! arithmetic on the host, so we can't fold Poseidon here. Instead we run the
//! witness generator once with a dummy root (which computes the true root into
//! the equality's internal var) and read that value back.

use num_bigint::BigUint;
use std::collections::BTreeMap;
use xark_ir::{primitive, solver};

const DEPTH: usize = 4;

fn load() -> primitive::PrimitiveProgram {
    let src =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/merkle/src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "merkle", "bn254");
    assert!(
        c.status_success,
        "compiling examples/merkle failed: {}",
        c.stderr
    );
    c.program()
}

fn id(p: &primitive::PrimitiveProgram, name: &str) -> u32 {
    p.vars
        .iter()
        .find(|v| v.name == name)
        .unwrap_or_else(|| panic!("missing circuit var `{name}`"))
        .id
}

/// The leaf/path/position inputs (everything except `root`), as decimal strings.
fn path_inputs(
    p: &primitive::PrimitiveProgram,
    leaf: &str,
    siblings: [&str; DEPTH],
    index_bits: [&str; DEPTH],
) -> BTreeMap<u32, String> {
    let mut m = BTreeMap::new();
    m.insert(id(p, "leaf"), leaf.to_string());
    for i in 0..DEPTH {
        m.insert(id(p, &format!("siblings[{i}]")), siblings[i].to_string());
        m.insert(
            id(p, &format!("index_bits[{i}]")),
            index_bits[i].to_string(),
        );
    }
    m
}

/// Reduce a signed decimal string into `[0, p)`.
fn fp(dec: &str, p: &BigUint) -> BigUint {
    match dec.strip_prefix('-') {
        Some(m) => (p - (BigUint::parse_bytes(m.as_bytes(), 10).unwrap() % p)) % p,
        None => BigUint::parse_bytes(dec.as_bytes(), 10).unwrap() % p,
    }
}

/// Fold a path to its true root without hardcoding it (`xark::Field` does no real
/// arithmetic on the host, so we can't run Poseidon here). Run witness generation
/// once with a placeholder root — the fold is independent of `root`, which only
/// appears in the final `require_eq(fold, root)` *constraint* — then solve that
/// (linear) constraint for `root` at the witness assignment.
fn honest_root(
    p: &primitive::PrimitiveProgram,
    leaf: &str,
    siblings: [&str; DEPTH],
    index_bits: [&str; DEPTH],
) -> String {
    let modulus = BigUint::parse_bytes(p.field.modulus_decimal.as_bytes(), 10).unwrap();
    let root_id = id(p, "root");

    let mut probe = path_inputs(p, leaf, siblings, index_bits);
    probe.insert(root_id, "0".to_string());
    let assign = solver::solve(p, &probe).expect("witness generation must succeed");
    let val = |v: u32| {
        fp(
            &assign.get(&v).expect("var assigned").to_decimal(),
            &modulus,
        )
    };

    // The unique constraint referencing `root` is `Σ cᵢ·vᵢ + const == 0` with a
    // `root` term (the equality against the folded root). Evaluate every other
    // term at the honest witness, then solve `c_root·root ≡ −rest` for `root`.
    let e = p
        .constraints
        .iter()
        .find(|e| e.linear_terms.iter().any(|t| t.var == root_id))
        .expect("constraint referencing `root`");

    let mut rest = fp(&e.constant.decimal(), &modulus);
    for mt in &e.mul_terms {
        let term =
            fp(&mt.coeff.decimal(), &modulus) * val(mt.left) % &modulus * val(mt.right) % &modulus;
        rest = (rest + term) % &modulus;
    }
    let mut c_root = BigUint::from(0u8);
    for lt in &e.linear_terms {
        if lt.var == root_id {
            c_root = fp(&lt.coeff.decimal(), &modulus);
        } else {
            rest = (rest + fp(&lt.coeff.decimal(), &modulus) * val(lt.var)) % &modulus;
        }
    }
    // root = −rest · c_root⁻¹  (Fermat inverse; c_root is ±1 for an equality).
    let neg_rest = (&modulus - &rest % &modulus) % &modulus;
    let inv = c_root.modpow(&(&modulus - BigUint::from(2u8)), &modulus);
    (neg_rest * inv % &modulus).to_str_radix(10)
}

#[test]
fn merkle_membership_accepts_valid_rejects_forgery() {
    let p = load();

    // A concrete leaf, authentication path, and LSB-first position (0b0101 = left,
    // right, left, right up the tree). Values are arbitrary field elements.
    let leaf = "7";
    let siblings = ["11", "22", "33", "44"];
    let index_bits = ["1", "0", "1", "0"];

    let root = honest_root(&p, leaf, siblings, index_bits);
    assert_ne!(root, "0", "sanity: a real Poseidon root is not zero");

    // (1) The honest membership proof is accepted and fully constrained.
    let mut ok = path_inputs(&p, leaf, siblings, index_bits);
    ok.insert(id(&p, "root"), root.clone());
    let assign = solver::solve_and_check(&p, &ok)
        .unwrap_or_else(|e| panic!("valid membership must accept: {e:?}"));
    let holes = solver::analyze_underconstrained(&p, &assign);
    assert!(
        holes.is_empty(),
        "merkle circuit under-constrained: {holes:?}"
    );

    // (2) A wrong root is rejected.
    let mut bad_root = path_inputs(&p, leaf, siblings, index_bits);
    bad_root.insert(id(&p, "root"), "12345".to_string());
    assert!(
        solver::solve_and_check(&p, &bad_root).is_err(),
        "a wrong root must be rejected"
    );

    // (3) A tampered sibling (with the honest root) is rejected — the fold no
    // longer reaches `root`.
    let mut bad_path = path_inputs(&p, leaf, ["99", "22", "33", "44"], index_bits);
    bad_path.insert(id(&p, "root"), root.clone());
    assert!(
        solver::solve_and_check(&p, &bad_path).is_err(),
        "a tampered authentication path must be rejected"
    );
}

#[test]
fn merkle_position_bit_is_boolean_constrained() {
    // A non-boolean index bit must be rejected: the gadget pins each direction bit
    // with `b·b == b`, so `index_bits[0] = 2` (with an otherwise honest witness)
    // cannot satisfy the circuit — this is what stops a prover forging a different
    // fold via an out-of-range selector.
    let p = load();
    let leaf = "7";
    let siblings = ["11", "22", "33", "44"];
    let honest = honest_root(&p, leaf, siblings, ["1", "0", "1", "0"]);

    let mut m = path_inputs(&p, leaf, siblings, ["2", "0", "1", "0"]);
    m.insert(id(&p, "root"), honest);
    assert!(
        solver::solve_and_check(&p, &m).is_err(),
        "a non-boolean index bit must be rejected"
    );
}
