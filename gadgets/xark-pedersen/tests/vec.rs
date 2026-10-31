//! `examples/pedersen` compiled and solved: known answers from `ark-grumpkin`, the
//! inputs the circuit must reject, and every witness value forged one at a time.
//!
//! The vectors are `cargo run --release --bin pedersen_tables -- kat` in
//! `examples/grumpkin_reference`: `[m0, m1, x, y]` with `(x, y) = m0·G0 + m1·G1`.
//! `formal/Formal/PedersenHash.lean` proves the same over the exported rows for every
//! input; these tests pin the generators, tables and offsets to the reference.

use std::collections::BTreeMap;
use std::sync::OnceLock;

use xark_ir::primitive::{PrimitiveProgram, VarRole};
use xark_ir::solver;
use xark_test_harness::{Compiled, bignum::LeafInput};

const REFERENCE: [&str; 4] = [
    "1512366075204170929049582354406559215",
    "338770000845734292534325025077361652240",
    "56611582869820574239993287487223071380142614942819473392064448158736499405",
    "14972036576598595980490710075994278492926559370076661242801210938371392582550",
];
const ONES: [&str; 4] = [
    "1",
    "1",
    "19671674398228500651706557933242527548436605331496461961903273047758392280239",
    "17620170737165873087442543514163024136714048209365181912517840174969631489007",
];
/// Every 3-bit window `7` (bits 0..126 set), the last window `0`.
const ALL_SEVENS: [&str; 4] = [
    "85070591730234615865843651857942052863",
    "85070591730234615865843651857942052863",
    "19908774353981899316944240951219067652301983329342255815852999029586069240494",
    "5755749691061052079796673410368203914048689669054019165200816728125511023524",
];
const MAX: [&str; 4] = [
    "340282366920938463463374607431768211455",
    "340282366920938463463374607431768211455",
    "5384239599840144312046318412526603177505597282546180216039495638803333927415",
    "8359617016740833248148167783314014035825979635629125806694904412547353473870",
];
const TOP_BIT: [&str; 4] = [
    "170141183460469231731687303715884105728",
    "1",
    "52195377207259411757094064367286654357304483852713722782778990834026459553",
    "21555482485990245012991925707655460815707904547888828462692378819476925751191",
];

fn compiled() -> &'static Compiled {
    static C: OnceLock<Compiled> = OnceLock::new();
    C.get_or_init(|| {
        let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../examples/pedersen/src/lib.rs");
        let c = xark_test_harness::compile_file(&src, "pedersen", "bn254");
        assert!(
            c.status_success,
            "compiling examples/pedersen failed: {}",
            c.stderr
        );
        c
    })
}

fn program() -> &'static PrimitiveProgram {
    static P: OnceLock<PrimitiveProgram> = OnceLock::new();
    P.get_or_init(|| compiled().program())
}

/// A decimal for a `Field` parameter.
struct Dec<'a>(&'a str);

impl LeafInput for Dec<'_> {
    fn leaves(&self, prefix: &str) -> Vec<(String, String)> {
        vec![(prefix.to_string(), self.0.to_string())]
    }
}

/// Solve, check every row and run the under-constraint analysis.
fn check(v: [&str; 4]) -> Result<(), String> {
    let [m0, m1, hx, hy] = v.map(Dec);
    compiled().check(&[("m0", &m0), ("m1", &m1), ("hx", &hx), ("hy", &hy)])
}

#[test]
fn hashes_match_ark_grumpkin() {
    for v in [REFERENCE, ONES, ALL_SEVENS, MAX, TOP_BIT] {
        check(v).unwrap_or_else(|e| panic!("{v:?}: {e}"));
    }
}

#[test]
fn rejects_a_wrong_hash() {
    let [m0, m1, hx, hy] = REFERENCE;
    assert!(check([m0, m1, "123", hy]).is_err());
    assert!(check([m0, m1, hx, ONES[3]]).is_err());
}

/// `m = 0` is the offsets' one exceptional input: the correction add would meet its
/// own negation. Any claimed hash is rejected, including `0·G0 + m1·G1`'s.
#[test]
fn rejects_scalar_zero() {
    // 0·G0 + 1·G1 = G1.
    let g1 = [
        "6702321717701145156728393535503061021609887341049508944231879352606054294317",
        "6805153572597533704290353269906054575543118937636820472181004119224603304535",
    ];
    assert!(check(["0", "1", g1[0], g1[1]]).is_err());
    assert!(check(["1", "0", ONES[2], ONES[3]]).is_err());
}

#[test]
fn rejects_scalars_from_2_pow_128() {
    let two_128 = "340282366920938463463374607431768211456";
    assert!(check([two_128, "1", ONES[2], ONES[3]]).is_err());
}

/// The honest witness of `REFERENCE`, with its variables' ids by name.
fn honest() -> BTreeMap<u32, solver::Fp> {
    let p = program();
    let id = |name: &str| p.vars.iter().find(|v| v.name == name).unwrap().id;
    let inputs: BTreeMap<u32, String> = ["m0", "m1", "hx", "hy"]
        .iter()
        .zip(REFERENCE)
        .map(|(n, v)| (id(n), v.to_string()))
        .collect();
    solver::solve_and_check(p, &inputs).expect("the reference vector solves")
}

/// The variables a row reads.
fn row_vars(c: &xark_ir::primitive::Expression) -> Vec<u32> {
    let mut vs: Vec<u32> = c.mul_terms.iter().flat_map(|t| [t.left, t.right]).collect();
    vs.extend(c.linear_terms.iter().map(|t| t.var));
    vs
}

/// Forged hints: every derived value a row reads (bits, lookup products, slopes,
/// coordinates, the final add's inverse), changed alone, breaks a row; and every row
/// is broken by changing one of the values it reads, so no row is vacuous.
#[test]
fn every_forged_witness_value_is_rejected() {
    let p = program();
    let assign = honest();
    let derived: std::collections::BTreeSet<u32> = p
        .vars
        .iter()
        .filter(|v| matches!(v.role, VarRole::Derived))
        .map(|v| v.id)
        .collect();
    // A different value, not a bit: `2`, or `3` where the honest value is `2`.
    let forged = |v: u32| {
        let mut a = assign.clone();
        let other = if a[&v].to_decimal() == "2" { "3" } else { "2" };
        a.insert(v, solver::fp_from_decimal(other, p));
        a
    };
    let read: std::collections::BTreeSet<u32> = p
        .constraints
        .iter()
        .flat_map(row_vars)
        .filter(|v| derived.contains(v))
        .collect();
    assert!(read.len() > 700, "{} derived values read", read.len());
    for &v in &read {
        assert!(
            solver::check(p, &forged(v)).is_err(),
            "forging v{v} is accepted"
        );
    }
    for (i, c) in p.constraints.iter().enumerate() {
        let row = PrimitiveProgram {
            field: p.field.clone(),
            vars: Vec::new(),
            constraints: vec![c.clone()],
            witness_gen: Vec::new(),
        };
        let broken = row_vars(c)
            .into_iter()
            .filter(|v| derived.contains(v))
            .any(|v| solver::check(&row, &forged(v)).is_err());
        assert!(broken, "row {i} holds whatever its derived values are");
    }
}
