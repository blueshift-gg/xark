//! Verify the complete (identity-safe) Grumpkin addition against ark-grumpkin
//! across all exceptional cases: P+∞, ∞+Q, P+(−P)=∞, P+P (doubling), generic
//! P+Q, and ∞+∞=∞. Each case must solve; a wrong sum must be rejected.

use std::collections::BTreeMap;
use std::path::Path;
use xark_ir::{primitive, solver};

fn load() -> primitive::PrimitiveProgram {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "grumpkin_complete_add", "bn254");
    assert!(c.status_success, "compile failed:\n{}", c.stderr);
    c.program()
}

// ark-grumpkin reference (scratchpad `cadd.rs`), P=7·G, Q=9·G.
type Pt = (&'static str, &'static str, &'static str);
const P: Pt = ("6502298228793251914218452601347199200336821300374732886528232462753193470018", "9407677376110273038006540221648729284102344671467345386528008239979586131147", "0");
const Q: Pt = ("7426331349063244596250713317947873730792793474529352435198059581717112405878", "7484184379535064294143018645362320921270470834230314099936005646196658438893", "0");
const NEG_P: Pt = ("6502298228793251914218452601347199200336821300374732886528232462753193470018", "12480565495729002184239865523608545804446019728948688957170195946596222364470", "0");
const ZERO: Pt = ("0", "0", "1");
const P_PLUS_P: Pt = ("12129716857924429340218542075908212533496677097166424713975580824254252046442", "11162489639683440471287028718798944516272846750856846865789391746548932089300", "0");
const P_PLUS_Q: Pt = ("10048396645591090210938223153773661969273778423700515767537776857572940140693", "11191650190137620699484062530470068897361843000224931459139859184792496975033", "0");

fn ids(program: &primitive::PrimitiveProgram) -> impl Fn(&str) -> u32 + '_ {
    move |name: &str| {
        program.vars.iter().find(|v| v.name == name).unwrap_or_else(|| panic!("no var {name}")).id
    }
}

fn inputs(program: &primitive::PrimitiveProgram, p: Pt, q: Pt, r: Pt) -> BTreeMap<u32, String> {
    let id = ids(program);
    let mut m = BTreeMap::new();
    for (n, v) in [
        ("px", p.0), ("py", p.1), ("pinf", p.2),
        ("qx", q.0), ("qy", q.1), ("qinf", q.2),
        ("rx", r.0), ("ry", r.1), ("rinf", r.2),
    ] {
        m.insert(id(n), v.to_string());
    }
    m
}

#[test]
fn complete_add_all_cases() {
    let program = load();
    let cases: [(&str, Pt, Pt, Pt); 6] = [
        ("P + 0 = P", P, ZERO, P),
        ("0 + Q = Q", ZERO, Q, Q),
        ("P + (-P) = inf", P, NEG_P, ZERO),
        ("P + P = 2P", P, P, P_PLUS_P),
        ("P + Q", P, Q, P_PLUS_Q),
        ("0 + 0 = inf", ZERO, ZERO, ZERO),
    ];
    for (name, p, q, r) in cases {
        let m = inputs(&program, p, q, r);
        let assign = solver::solve_and_check(&program, &m)
            .unwrap_or_else(|e| panic!("case `{name}` must verify: {e:?}"));
        let holes = solver::analyze_underconstrained(&program, &assign);
        assert!(holes.is_empty(), "case `{name}` under-constrained: {holes:?}");
    }

    // a wrong sum is rejected.
    let program2 = &program;
    let mut bad = inputs(program2, P, Q, P_PLUS_P); // claim P+Q == 2P
    let _ = &mut bad;
    assert!(
        solver::solve_and_check(program2, &bad).is_err(),
        "wrong sum must be rejected"
    );
}

#[test]
fn report_constraint_count() {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "grumpkin_complete_add", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    println!("grumpkin_complete_add: {} minimized R1CS constraints", c.minimized_r1cs_len());
}
