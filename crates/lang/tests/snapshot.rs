//! Integration tests: compile the workspace examples and compare their emitted
//! `r1cs.json` / `graph.dot` against committed snapshots. Also exercises the
//! rejection diagnostics for unsupported inputs.
//!
//! Set `UPDATE_SNAPSHOTS=1` to overwrite the snapshot files with fresh output.

use std::path::{Path, PathBuf};

use xark_test_harness::Compiled;

fn workspace_root() -> PathBuf {
    // CARGO_MANIFEST_DIR = <root>/crates/lang
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("workspace root")
        .to_path_buf()
}

fn compile(src: &Path, out_name: &str) -> Compiled {
    compile_with_field(src, out_name, "unknown")
}

fn compile_with_field(src: &Path, out_name: &str, field: &str) -> Compiled {
    // The snapshot suite reads `r1cs.json` / `circuit.json` / `graph.dot`
    // directly, so it opts into `--emit-json` (a normal build writes only the
    // compact `circuit.xbc`).
    xark_test_harness::compile_file_json(src, out_name, field)
}

/// Whether the compiled circuit accepts the named inputs (solve + check every row).
fn accepts(c: &xark_test_harness::Compiled, inputs: &[(&str, &str)]) -> bool {
    let program = xark_ir::primitive::from_json(
        &std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap(),
    )
    .expect("valid circuit.json");
    let ids = inputs
        .iter()
        .map(|(n, v)| {
            let id = program.vars.iter().find(|x| x.name == *n).unwrap().id;
            (id, v.to_string())
        })
        .collect();
    xark_ir::solver::solve_and_check(&program, &ids).is_ok()
}

/// Whether *any* witness proves these inputs, decided by exhaustive witness search
/// (the adversary, not the honest solver): `true` when exactly one does, `false`
/// when none does. Panics when two witnesses exist (an under-constrained circuit),
/// the search can't decide, or the honest solver can't find the one witness.
fn accepts_exactly(c: &xark_test_harness::Compiled, inputs: &[(&str, &str)]) -> bool {
    use xark_ir::witness_search::{WitnessSearch, search_witnesses};
    let program = c.program();
    let ids: std::collections::BTreeMap<_, _> = inputs
        .iter()
        .map(|(n, v)| {
            let id = program.vars.iter().find(|x| x.name == *n).unwrap().id;
            (id, v.to_string())
        })
        .collect();
    match search_witnesses(&program, &ids, 1 << 14).unwrap() {
        WitnessSearch::Unique(_) => {
            if let Err(e) = xark_ir::solver::solve_and_check(&program, &ids) {
                panic!("{inputs:?}: a witness exists, but the hint program fails: {e}");
            }
            true
        }
        WitnessSearch::None => {
            // A witness the hint program computes and every row checks would
            // contradict `None` (the search pruned a real witness).
            if xark_ir::solver::solve_and_check(&program, &ids).is_ok() {
                panic!("{inputs:?}: the search found no witness, but the hint program's checks");
            }
            false
        }
        other => panic!("{inputs:?}: {other:?}"),
    }
}

/// [`accepts_exactly`] without the honest-solver cross-check, for circuits whose
/// witness the hint program doesn't fully compute (bare `advice`).
fn accepts_exactly_constraints(c: &xark_test_harness::Compiled, inputs: &[(&str, &str)]) -> bool {
    use xark_ir::witness_search::{WitnessSearch, search_witnesses};
    let program = c.program();
    let ids: std::collections::BTreeMap<_, _> = inputs
        .iter()
        .map(|(n, v)| {
            let id = program.vars.iter().find(|x| x.name == *n).unwrap().id;
            (id, v.to_string())
        })
        .collect();
    match search_witnesses(&program, &ids, 1 << 14).unwrap() {
        WitnessSearch::Unique(_) => true,
        WitnessSearch::None => false,
        other => panic!("{inputs:?}: {other:?}"),
    }
}

/// [`accepts_exactly`] where the search decides, else the honest solver plus the
/// local under-constraint analyzer (non-native arithmetic, whose modular identities
/// the search's interval reasoning can't always pin).
fn accepts_best_effort(c: &xark_test_harness::Compiled, inputs: &[(&str, &str)]) -> bool {
    use xark_ir::solver;
    use xark_ir::witness_search::{WitnessSearch, search_witnesses};
    let program = c.program();
    let ids: std::collections::BTreeMap<_, _> = inputs
        .iter()
        .map(|(n, v)| {
            let id = program.vars.iter().find(|x| x.name == *n).unwrap().id;
            (id, v.to_string())
        })
        .collect();
    let honest = solver::solve_and_check(&program, &ids);
    match search_witnesses(&program, &ids, 1 << 12).unwrap() {
        WitnessSearch::Unique(_) => {
            assert!(
                honest.is_ok(),
                "{inputs:?}: a witness exists, but the hint program fails"
            );
            true
        }
        WitnessSearch::None => {
            assert!(
                honest.is_err(),
                "{inputs:?}: the search found no witness, but the hint program's checks"
            );
            false
        }
        WitnessSearch::Multiple { name, .. } => panic!("{inputs:?}: two witnesses (`{name}`)"),
        WitnessSearch::Inconclusive(_) => match honest {
            Ok(assign) => {
                let holes: Vec<_> = solver::analyze_underconstrained(&program, &assign)
                    .into_iter()
                    .filter(|u| u.reason != "no constraint references this variable")
                    .collect();
                assert!(holes.is_empty(), "{inputs:?}: under-constrained {holes:?}");
                true
            }
            Err(_) => false,
        },
    }
}

fn check_snapshot(snapshot_rel: &str, actual: &str) {
    let root = workspace_root();
    let path = root.join("tests/snapshots").join(snapshot_rel);
    if std::env::var("UPDATE_SNAPSHOTS").is_ok() {
        std::fs::write(&path, actual).expect("write snapshot");
        return;
    }
    let expected =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("missing snapshot {path:?}: {e}"));
    assert_eq!(
        expected, actual,
        "snapshot mismatch for {snapshot_rel}; run with UPDATE_SNAPSHOTS=1 to refresh"
    );
}

fn example(name: &str) -> PathBuf {
    workspace_root()
        .join("examples")
        .join(name)
        .join("src/lib.rs")
}

/// Assert a `for`-loop circuit lowers byte-for-byte identically to its `while`
/// counterpart, in both emitted views (`r1cs.json` and `circuit.json`).
fn assert_for_equals_while(for_c: &Compiled, while_c: &Compiled, what: &str) {
    for f in ["r1cs.json", "circuit.json"] {
        let for_j = std::fs::read_to_string(for_c.out_dir.join(f)).unwrap();
        let while_j = std::fs::read_to_string(while_c.out_dir.join(f)).unwrap();
        assert_eq!(for_j, while_j, "{what}: `for` must equal `while` in `{f}`");
    }
}

#[test]
fn cube_matches_snapshot() {
    let c = compile(&example("cube"), "cube");
    assert!(c.status_success, "cube failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    let dot = std::fs::read_to_string(c.out_dir.join("graph.dot")).unwrap();
    check_snapshot("cube.r1cs.json", &json);
    check_snapshot("cube.graph.dot", &dot);
    // Acceptance: cube emits exactly 2 constraints.
    assert_eq!(json.matches("\"source_span\"").count(), 2);
}

#[test]
fn difference_of_squares_matches_snapshot() {
    let c = compile(&example("difference_of_squares"), "difference_of_squares");
    assert!(c.status_success, "dos failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    let dot = std::fs::read_to_string(c.out_dir.join("graph.dot")).unwrap();
    check_snapshot("difference_of_squares.r1cs.json", &json);
    check_snapshot("difference_of_squares.graph.dot", &dot);
    // Acceptance: exactly 1 constraint.
    assert_eq!(json.matches("\"source_span\"").count(), 1);
}

#[test]
fn linear_folds_scalar_muls() {
    let c = compile(&example("linear"), "linear");
    assert!(c.status_success, "linear failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    let dot = std::fs::read_to_string(c.out_dir.join("graph.dot")).unwrap();
    check_snapshot("linear.r1cs.json", &json);
    check_snapshot("linear.graph.dot", &dot);
    // Constant*variable folds into coefficients: purely linear → exactly one
    // equality constraint and NO multiplication gates (no internal `t` vars).
    assert_eq!(json.matches("\"source_span\"").count(), 1);
    assert!(
        !json.contains("\"name\": \"t0\""),
        "unexpected mul gate in linear circuit"
    );
}

#[test]
fn mimc_matches_snapshot() {
    let c = compile_with_field(&example("mimc"), "mimc", "bn254");
    assert!(c.status_success, "mimc failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    let dot = std::fs::read_to_string(c.out_dir.join("graph.dot")).unwrap();
    check_snapshot("mimc.r1cs.json", &json);
    check_snapshot("mimc.graph.dot", &dot);
    // 3 rounds * 2 gates per `^3` + 1 finalizing equality = 7 constraints.
    assert_eq!(json.matches("\"source_span\"").count(), 7);
    // Big field-sized round constant survived as an exact decimal.
    assert!(
        json.contains(
            "7120861356467033611736373842526102177239622603558704633600844922174959859415"
        )
    );
    // bn254 modulus recorded.
    assert!(
        json.contains(
            "21888242871839275222246405745257275088548364400416034343698204186575808495617"
        )
    );
}

/// The real `xark-mimc` gadget crate (a port of `noir-lang/mimc`: MiMC-p/p,
/// exponent 7, 91 rounds) is inlined across the crate boundary and lowers to a
/// stable R1CS. Compiles a two-input MiMC-BN254 Feistel hash preimage
/// `mimc_bn254([x, k]) == h` (inline source: the canonical mimc examples are the
/// hand-written `mimc`/`mimc_loop`; this bridges to the library gadget). The
/// all-constant-input KAT is covered by `xark-mimc`'s own `vec` test.
#[test]
fn mimc_gadget_matches_snapshot() {
    let src = "#![no_std]\n\
        use xark_mimc::prelude::*;\n\
        pub fn circuit(x: Private<Field>, k: Private<Field>, h: Public<Field>) {\n\
        require_eq(mimc_bn254([x, k]), h);\n\
        }\n";
    let c = compile_with_field(&write_case("mimc_gadget", src), "mimc_gadget", "bn254");
    assert!(c.status_success, "mimc_gadget failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    let dot = std::fs::read_to_string(c.out_dir.join("graph.dot")).unwrap();
    check_snapshot("mimc_gadget.r1cs.json", &json);
    check_snapshot("mimc_gadget.graph.dot", &dot);
}

/// The advice primitive: an inverse gadget introduces a fresh private witness
/// `w0` and verifies `x * w0 == 1` — no forward computation of `1/x`.
#[test]
fn inverse_advice_gadget() {
    let c = compile_with_field(&example("inverse"), "inverse", "bn254");
    assert!(c.status_success, "inverse failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    let dot = std::fs::read_to_string(c.out_dir.join("graph.dot")).unwrap();
    check_snapshot("inverse.r1cs.json", &json);
    check_snapshot("inverse.graph.dot", &dot);
    // The advice variable is a fresh *private* witness, and the inverse check
    // merged the constant `1` into the multiplication's output.
    assert!(
        json.contains("\"name\": \"w0\""),
        "missing advice var: {json}"
    );
    assert!(
        json.contains("\"note\": \"x * w0 = 1\""),
        "unexpected R1CS: {json}"
    );
    assert_eq!(json.matches("\"source_span\"").count(), 2);
}

/// `require_ne(a, b)` is the nonzero gadget over `a - b`: it reuses `inv()` to
/// pin `(a-b)·w == 1`, which solves iff `a != b` and is unsatisfiable when they
/// are equal — with the inverse advice `w` fully pinned (analyzer-clean). This is
/// the soundness-meaningful test: an honest distinct pair proves, and no witness
/// can satisfy an equal pair (`0·w = 1` has no solution in the field).
#[test]
fn require_ne_solves_iff_distinct() {
    use xark_ir::solver;
    let src = "#![no_std]\n\
        use xark::prelude::*;\n\
        pub fn circuit(a: Private<Field>, b: Public<Field>) {\n\
        require_ne(a, b);\n\
        }\n";
    let c = compile_with_field(&write_case("require_ne", src), "require_ne", "bn254");
    assert!(c.status_success, "require_ne failed: {}", c.stderr);
    let p = c.program();

    let id = |n: &str| {
        p.vars
            .iter()
            .find(|v| v.name == n)
            .unwrap_or_else(|| panic!("missing circuit var `{n}`"))
            .id
    };
    let inputs = |a: &str, b: &str| {
        let mut m = std::collections::BTreeMap::new();
        m.insert(id("a"), a.to_string());
        m.insert(id("b"), b.to_string());
        m
    };

    // Distinct inputs solve, and the inverse advice is fully pinned.
    let assign =
        solver::solve_and_check(&p, &inputs("3", "7")).expect("require_ne(3, 7) must solve");
    assert!(
        solver::analyze_underconstrained(&p, &assign).is_empty(),
        "require_ne must be fully constrained (inverse advice pinned)"
    );
    // A difference that is nonzero only mod p still solves.
    solver::solve_and_check(&p, &inputs("0", "1")).expect("require_ne(0, 1) must solve");

    // Equal inputs are unsatisfiable: a - b == 0 has no inverse, so 0·w == 1 fails.
    assert!(
        solver::solve_and_check(&p, &inputs("5", "5")).is_err(),
        "require_ne(5, 5) must be rejected (equal ⇒ no solution)"
    );
}

/// Native `u64` as a first-class circuit witness: a `Private<u64>` input is range-checked
/// to 64 bits on entry, and the *native* `<` operator lowers to the field comparison
/// gadget — no wrapper type, no `::<64>`. A true ordering solves (analyzer-clean), a false
/// one is rejected, and an input `>= 2^64` fails the entry range check.
#[test]
fn native_u64_comparison() {
    use xark_ir::solver;
    let src = "#![no_std]\n\
        use xark::prelude::*;\n\
        pub fn circuit(a: Private<u64>, b: Private<u64>) {\n\
        require(a < b);\n\
        }\n";
    let c = compile_with_field(
        &write_case("native_u64_cmp", src),
        "native_u64_cmp",
        "bn254",
    );
    assert!(c.status_success, "native u64 compare failed: {}", c.stderr);
    let p = c.program();

    let id = |n: &str| {
        p.vars
            .iter()
            .find(|v| v.name == n)
            .unwrap_or_else(|| panic!("missing circuit var `{n}`"))
            .id
    };
    let inputs = |a: &str, b: &str| {
        let mut m = std::collections::BTreeMap::new();
        m.insert(id("a"), a.to_string());
        m.insert(id("b"), b.to_string());
        m
    };

    // 3 < 7 holds → require(true) solves, fully constrained.
    let assign =
        solver::solve_and_check(&p, &inputs("3", "7")).expect("native u64 3 < 7 must solve");
    assert!(
        solver::analyze_underconstrained(&p, &assign).is_empty(),
        "native u64 compare must be fully constrained"
    );
    // 7 < 3 is false → require rejects it.
    assert!(
        solver::solve_and_check(&p, &inputs("7", "3")).is_err(),
        "native u64 7 < 3 must be rejected"
    );
    // 2^64 is not a valid u64: the entry range check on `a` is unsatisfiable.
    assert!(
        solver::solve_and_check(&p, &inputs("18446744073709551616", "0")).is_err(),
        "a native u64 input >= 2^64 must fail the entry range check"
    );
}

/// Native `u64` through the `#[circuit]` macro (not just bare source): the macro maps
/// a `Private<u64>` param to a native-`u64` circuit input + a `u64` host-input field,
/// and the driver lowers the comparison. Confirms macro + driver compose end-to-end.
#[test]
fn native_u64_via_circuit_macro() {
    use xark_ir::solver;
    let src = "#![no_std]\n\
        use xark::prelude::*;\n\
        #[circuit]\n\
        pub fn cmp(a: Private<u64>, b: Private<u64>) {\n\
        require(a < b);\n\
        }\n";
    let c = compile_with_field(&write_case("u64_macro", src), "u64_macro", "bn254");
    assert!(
        c.status_success,
        "native u64 via #[circuit] failed: {}",
        c.stderr
    );
    let p = c.program();
    let id = |n: &str| p.vars.iter().find(|v| v.name == n).unwrap().id;
    let mut ok = std::collections::BTreeMap::new();
    ok.insert(id("a"), "3".to_string());
    ok.insert(id("b"), "7".to_string());
    solver::solve_and_check(&p, &ok).expect("#[circuit] native u64 3 < 7 must solve");
    let mut bad = std::collections::BTreeMap::new();
    bad.insert(id("a"), "7".to_string());
    bad.insert(id("b"), "3".to_string());
    assert!(
        solver::solve_and_check(&p, &bad).is_err(),
        "#[circuit] native u64 7 < 3 must be rejected"
    );
}

/// Native `u64` **wrapping arithmetic**: `wrapping_add`/`wrapping_sub` lower to the
/// mod-2⁶⁴ gadget (carry/borrow + range check). The defining property is wraparound —
/// `(2⁶⁴−1) + 1 == 0` and `5 − 7 == 2⁶⁴−2` — which must solve, while a wrong result is
/// rejected. Compiles via `wrapping_*` being recognized as a call (not inlined).
#[test]
fn native_u64_wrapping_arithmetic() {
    use xark_ir::solver;
    const MAX: &str = "18446744073709551615"; // 2^64 - 1
    let check = |op: &str, a: &str, b: &str, c: &str| -> Result<(), ()> {
        let src = format!(
            "#![no_std]\nuse xark::prelude::*;\n\
             pub fn circuit(a: Private<u64>, b: Private<u64>, c: Public<u64>) {{\n\
             require(a.{op}(b) == c);\n\
             }}\n"
        );
        let comp = compile_with_field(&write_case("u64_wrap", &src), "u64_wrap", "bn254");
        assert!(
            comp.status_success,
            "{op} failed to compile: {}",
            comp.stderr
        );
        let p = comp.program();
        let id = |n: &str| p.vars.iter().find(|v| v.name == n).unwrap().id;
        let mut m = std::collections::BTreeMap::new();
        m.insert(id("a"), a.to_string());
        m.insert(id("b"), b.to_string());
        m.insert(id("c"), c.to_string());
        solver::solve_and_check(&p, &m).map(|_| ()).map_err(|_| ())
    };

    // wrapping_add: normal, and the wraparound (2^64-1) + 1 == 0.
    assert!(check("wrapping_add", "5", "7", "12").is_ok(), "5 + 7 == 12");
    assert!(
        check("wrapping_add", MAX, "1", "0").is_ok(),
        "(2^64-1) + 1 wraps to 0"
    );
    assert!(
        check("wrapping_add", "5", "7", "13").is_err(),
        "5 + 7 != 13 rejected"
    );

    // wrapping_sub: normal, and the borrow wraparound 5 - 7 == 2^64 - 2.
    assert!(check("wrapping_sub", "7", "5", "2").is_ok(), "7 - 5 == 2");
    assert!(
        check("wrapping_sub", "5", "7", "18446744073709551614").is_ok(),
        "5 - 7 wraps to 2^64 - 2"
    );
    assert!(
        check("wrapping_sub", "7", "5", "3").is_err(),
        "7 - 5 != 3 rejected"
    );

    // wrapping_mul: normal, and the wraparound 2^32 · 2^32 == 2^64 ≡ 0 (mod 2^64).
    assert!(check("wrapping_mul", "5", "7", "35").is_ok(), "5 * 7 == 35");
    assert!(
        check("wrapping_mul", "4294967296", "4294967296", "0").is_ok(),
        "2^32 * 2^32 wraps to 0"
    );
    assert!(
        check("wrapping_mul", "5", "7", "36").is_err(),
        "5 * 7 != 36 rejected"
    );
}

/// Native `u64` **checked arithmetic**: the default `+ - *` (overflow-checked, like debug
/// Rust) lower to `*WithOverflow` + a range check that makes the op **unsatisfiable on
/// overflow** — the opposite of wrapping. A valid result solves; an overflowing/underflowing
/// operation is rejected for *every* claimed result.
#[test]
fn native_u64_checked_arithmetic() {
    use xark_ir::solver;
    const MAX: &str = "18446744073709551615"; // 2^64 - 1
    let check = |expr: &str, name: &str, a: &str, b: &str, c: &str| -> Result<(), ()> {
        let src = format!(
            "#![no_std]\nuse xark::prelude::*;\n\
             pub fn circuit(a: Private<u64>, b: Private<u64>, c: Public<u64>) {{\n\
             require({expr} == c);\n\
             }}\n"
        );
        let comp = compile_with_field(&write_case(name, &src), name, "bn254");
        assert!(
            comp.status_success,
            "{expr} failed to compile: {}",
            comp.stderr
        );
        let p = comp.program();
        let id = |n: &str| p.vars.iter().find(|v| v.name == n).unwrap().id;
        let mut m = std::collections::BTreeMap::new();
        m.insert(id("a"), a.to_string());
        m.insert(id("b"), b.to_string());
        m.insert(id("c"), c.to_string());
        solver::solve_and_check(&p, &m).map(|_| ()).map_err(|_| ())
    };

    // + : valid solves; overflow is rejected even for the wrapped value (unlike wrapping).
    assert!(
        check("a + b", "chk_add", "5", "7", "12").is_ok(),
        "5 + 7 == 12"
    );
    assert!(
        check("a + b", "chk_add", MAX, "1", "0").is_err(),
        "(2^64-1) + 1 overflows → rejected"
    );
    assert!(
        check("a + b", "chk_add", "5", "7", "13").is_err(),
        "5 + 7 != 13"
    );

    // - : valid solves; underflow (a < b) is rejected.
    assert!(
        check("a - b", "chk_sub", "7", "5", "2").is_ok(),
        "7 - 5 == 2"
    );
    assert!(
        check("a - b", "chk_sub", "5", "7", "0").is_err(),
        "5 - 7 underflows → rejected"
    );

    // * : valid solves; overflow is rejected.
    assert!(
        check("a * b", "chk_mul", "5", "7", "35").is_ok(),
        "5 * 7 == 35"
    );
    assert!(
        check("a * b", "chk_mul", "4294967296", "4294967296", "0").is_err(),
        "2^32 * 2^32 = 2^64 overflows → rejected"
    );
}

/// Native `u8` **bitwise ops + shifts + not**: `& | ^` decompose both operands and apply
/// the per-bit gate; `<< >>` by a constant re-index the bits (mod 2⁸); `!a = 255 − a`.
/// Checked against the real integer results, with a wrong result rejected.
#[test]
fn native_u8_bitwise_ops() {
    use xark_ir::solver;
    // `expr` uses `a` (and `b` for binary ops); `c` is the expected result.
    let ok = |expr: &str, name: &str, a: u8, b: u8, c: u8| {
        let src = format!(
            "#![no_std]\nuse xark::prelude::*;\n\
             pub fn circuit(a: Private<u8>, b: Private<u8>, c: Public<u8>) {{\n\
             require(({expr}) == c);\n\
             }}\n"
        );
        let comp = compile_with_field(&write_case(name, &src), name, "bn254");
        assert!(
            comp.status_success,
            "{expr} failed to compile: {}",
            comp.stderr
        );
        let p = comp.program();
        let id = |n: &str| p.vars.iter().find(|v| v.name == n).unwrap().id;
        let solve = |cv: u8| {
            let mut m = std::collections::BTreeMap::new();
            m.insert(id("a"), a.to_string());
            m.insert(id("b"), b.to_string());
            m.insert(id("c"), cv.to_string());
            solver::solve_and_check(&p, &m).is_ok()
        };
        assert!(solve(c), "{expr} with a={a} b={b} must give {c}");
        assert!(!solve(c ^ 0xFF), "{expr} must reject a wrong result");
    };

    ok("a & b", "u8_and", 0b1100, 0b1010, 0b1000);
    ok("a | b", "u8_or", 0b1100, 0b1010, 0b1110);
    ok("a ^ b", "u8_xor", 0b1100, 0b1010, 0b0110);
    ok("!a", "u8_not", 12, 0, 243); // 255 - 12
    ok("a << 2", "u8_shl", 0b1100, 0, 0b110000); // 12 << 2 = 48
    ok("a >> 2", "u8_shr", 0b1100, 0, 0b11); // 12 >> 2 = 3
    ok("a << 2", "u8_shl_ovf", 200, 0, 32); // (200 << 2) mod 256 = 32 (top bits dropped)
}

/// MiMC written with a `while` loop over an array of round constants lowers to
/// exactly the same R1CS as the hand-unrolled version — arrays + bounded loops +
/// inlining compose.
#[test]
fn mimc_loop_equals_unrolled() {
    let c = compile_with_field(&example("mimc_loop"), "mimc_loop", "bn254");
    assert!(c.status_success, "mimc_loop failed: {}", c.stderr);
    let looped = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();

    let inline = compile_with_field(&example("mimc"), "mimc_cmp2", "bn254");
    let unrolled = std::fs::read_to_string(inline.out_dir.join("r1cs.json")).unwrap();

    // The loop form caches the `round` helper (called 3×) while the hand-unrolled
    // form inlines it; cache-all emits no debug `note`s on cached-function bodies,
    // so the two differ *only* in cosmetic debug annotations. The R1CS math
    // (variables + every a·b=c row) is still byte-identical — compare with the
    // debug field stripped to require that structural equivalence.
    let strip = |s: &str| {
        let mut p = xark_ir::json::from_json(s).unwrap();
        for k in &mut p.constraints {
            k.debug = None;
        }
        xark_ir::json::to_json_pretty(&p)
    };
    assert_eq!(
        strip(&looped),
        strip(&unrolled),
        "loop+array MiMC must match the hand-unrolled version (R1CS math)"
    );
    // 3 rounds * 2 gates per `^3` + 1 finalizing equality = 7 constraints.
    assert_eq!(
        xark_ir::json::from_json(&looped).unwrap().constraints.len(),
        7
    );
}

/// Bit-decomposition gadget (`xark-bits`): 8 advice bits, 8 booleanity gates,
/// and a gate-free recomposition `Σ bits[i]·2^i == x`.
#[test]
fn bit_decompose_gadget() {
    let c = compile_with_field(&example("bit_decompose"), "bit_decompose", "bn254");
    assert!(c.status_success, "bit_decompose failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    let dot = std::fs::read_to_string(c.out_dir.join("graph.dot")).unwrap();
    check_snapshot("bit_decompose.r1cs.json", &json);
    check_snapshot("bit_decompose.graph.dot", &dot);
    // 8 distinct private advice bits.
    for i in 0..8 {
        assert!(
            json.contains(&format!("\"name\": \"w{i}\"")),
            "missing advice bit w{i}"
        );
    }
    // 8 booleanity gates + 1 recomposition + 2 demo equalities.
    assert_eq!(json.matches("\"source_span\"").count(), 11);
    // Recomposition folds bits into a linear combination (no gate): the note is a
    // `(...) * 1 = 0` equality carrying all 8 power-of-two coefficients.
    assert!(
        json.contains("128*w7"),
        "recomposition coefficients missing: {json}"
    );
}

/// Poseidon permutation gadget (`xark-poseidon`, t=3, α=5): the S-boxes are the
/// only multiplication gates; ARK (constant adds) and MDS (constant-matrix mix)
/// fold into linear combinations for free.
#[test]
fn poseidon_gadget() {
    let c = compile_with_field(&example("poseidon"), "poseidon", "bn254");
    assert!(c.status_success, "poseidon failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    let dot = std::fs::read_to_string(c.out_dir.join("graph.dot")).unwrap();
    check_snapshot("poseidon.r1cs.json", &json);
    check_snapshot("poseidon.graph.dot", &dot);

    // Real HorizenLabs BN256 instance: R_F=8 full (3 S-boxes each) + R_P=56 partial
    // (1 S-box each) = 80 S-boxes × 3 gates (`x^2, x^4, x^5`) = 240 S-box gates,
    // plus 1 final `require_eq` equality = 241 constraints. ARK/MDS fold for free.
    // 3 fewer — `hash2` seeds the capacity lane with the constant
    // 0, so the first round's lane-0 S-box is `rc⁵`, a constant (folded).
    let sbox = 237;
    let r1cs = xark_ir::json::from_json(&json).unwrap();
    assert_eq!(r1cs.constraints.len(), sbox + 1);
    // The only equality is the `(out) * 1 = 0` output binding; ARK/MDS are free.
    let equalities = r1cs
        .constraints
        .iter()
        .filter(|k| k.b.terms.is_empty() && k.c.terms.is_empty() && k.c.constant.is_zero())
        .count();
    assert_eq!(
        equalities, 1,
        "only the output binding should be an equality; ARK/MDS are free"
    );
    assert_eq!(
        r1cs.constraints.len() - equalities,
        sbox,
        "expected exactly {sbox} S-box multiplication gates"
    );
}

/// Merkle membership (`xark-merkle`): a depth-4 Poseidon path fold. Each level is
/// one `hash2` (240 S-box gates) plus one booleanity gate for the direction bit
/// and two sibling muxes (each a single mul); the direction bits let the sibling
/// ordering fold as free linear combinations. The whole path is proven against
/// the public root with a single final equality.
#[test]
fn merkle_membership_gadget() {
    let c = compile_with_field(&example("merkle"), "merkle", "bn254");
    assert!(c.status_success, "merkle failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    let r1cs = xark_ir::json::from_json(&json).unwrap();

    // 4 levels × (241 Poseidon `hash2` gates [240 S-box + 1 output binding] + 1
    // booleanity + 2 sibling muxes) + 1 final root equality = 4×244 + 1 = 977.
    // (No `r1cs.json` snapshot: Poseidon's full-field round-constant coefficients
    // make it ~40 MB — the count + nonzero pins below catch a lowering change, and
    // `xark-merkle`'s `vec` KAT covers the values. The gadget's cost is linear in
    // depth: exactly 4× the single-`hash2` `poseidon` circuit, no LC blow-up.)
    //
    // 961 = 977 − 16. Per level, Poseidon's constant capacity lane
    // folds its first S-box (3 rows: `rc⁵` is a constant) and the `hash2` output
    // binding stays an inline sum (1 row); see `merkle_matches_lean_model`.
    let (want, want_nz) = (961, 25_254);
    assert_eq!(r1cs.constraints.len(), want);
    let nonzeros: usize = r1cs
        .constraints
        .iter()
        .map(|k| k.a.terms.len() + k.b.terms.len() + k.c.terms.len())
        .sum();
    assert_eq!(nonzeros, want_nz, "depth-4 Poseidon Merkle nonzero count");
}

/// **R1CS ↔ Lean bridge (Merkle membership).**
///
/// `formal/Formal/Merkle.lean` proves the soundness fact a Merkle fold adds over
/// the Poseidon compression: `merkle_level_swap_sound` shows that with the
/// position bit constrained boolean (`b·b = b`), each level's `(left, right)` is
/// exactly the input pair `(node, sib)` in one of its two orders — a genuine
/// conditional swap, no third value reachable, so the only prover freedom is the
/// position bit itself. Poseidon's own determinacy is `poseidon_permutation_determined`
/// (`Formal/Poseidon.lean`); the full root is their composition.
///
/// This is the bridge to the actual `xark-merkle` gadget: it pins the per-level
/// multiplication shape the Lean model is stated over — one Poseidon `hash2`
/// (240 S-box muls) + one booleanity gate (`b·b`) + two select muxes (`b·(t−f)`)
/// — across the depth-4 path: 4 × (240 + 1 + 2) = 972. Any drift in the fold's
/// mux/booleanity shape or the compression changes this and fails here.
#[test]
fn merkle_matches_lean_model() {
    let c = xark_test_harness::compile_file(&example("merkle"), "merkle_lean_bridge", "bn254");
    assert!(c.status_success, "merkle gadget compiles: {}", c.stderr);
    // Mult-gate count, streamed from `circuit.xbc` (no r1cs.json materialization).
    let mul_gates = c.mul_gate_count();

    // 4 levels × (240 Poseidon S-box muls + 1 booleanity + 2 select muxes) = 972.
    // The shape `merkle_level_swap_sound` + `poseidon_permutation_determined` are
    // stated over. If this fails, reconcile the gadget with the Lean model.
    //
    // 4 × (237 + 1 + 2) = 960. `hash2` seeds the capacity lane
    // with the constant 0, so the first round's lane-0 S-box is `rc⁵` — a constant,
    // folded (`Xark.R1cs.const_mul_sound`) instead of emitted as 3 rows whose
    // operands are all constants. The 79 S-boxes on witness values and the
    // swap/booleanity rows are exactly the modelled ones.
    let want = 960;
    assert_eq!(
        mul_gates, want,
        "depth-4 Merkle must emit {want} multiplication gates (matches \
         Xark.merkle_level_swap_sound ∘ poseidon compression); got {mul_gates}"
    );
}

/// 32-bit word gadget layer (`xark-bits`): xor/and/rotr/add32. Rotations are
/// free re-wiring; the mul gates come only from bitwise ops + bit-decompositions.
#[test]
fn word32_ops() {
    let c = compile_with_field(&example("word_ops"), "word_ops", "bn254");
    assert!(c.status_success, "word_ops failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    check_snapshot("word_ops.r1cs.json", &json);
    // 32+32 booleanity (two to_bits32) + 32 xor + 32 and + 33 (add32 decomp) = 161 gates,
    // + 4 equalities (2 recompositions + add32 recomposition + final) = 165 constraints.
    // Counted from the parsed R1CS (note-robust): cache-all drops debug notes on
    // cached-function bodies, but the R1CS math is unchanged (same 165 constraints).
    assert_eq!(
        xark_ir::json::from_json(&json).unwrap().constraints.len(),
        165
    );
    // add32's carry decomposition uses 33 bits; two inputs use 32 each → 97 advice.
    assert_eq!(
        json.matches("\"visibility\": \"Private\"").count() - 2, /*a,b inputs*/
        97
    );
}

/// Nested arrays `[[Field; N]; M]` work, including as function arguments.
#[test]
fn nested_arrays() {
    let src = write_case(
        "nested",
        "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
         fn get(m: [[Field; 2]; 2], i: usize, j: usize) -> Field { m[i][j] }\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>, c: Public<Field>) {\n\
             let m = [[a, b], [b, a]];\n\
             require_eq(get(m, 0, 0) + m[1][1], c);\n\
         }\n",
    );
    let c = compile(&src, "nested");
    assert!(c.status_success, "nested arrays failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    assert!(json.contains("\"note\": \"(2*a - c) * 1 = 0\""), "{json}");
}

// ---------------------------------------------------------------------------
// Hash FV / vector / stress harnesses.
//
// The user-facing `examples/{sha256,keccak256,blake2s,blake3}` are now ergonomic
// `#[circuit]` bodies with `[u8; N]` message + `[u8; 32]` digest (a 2-field
// `Hash`). The soundness bridges below need to (a) inject specific per-word
// witness values and (b) pin exact gate counts against the Lean model, so they
// compile *inline* sources that reproduce the former limb-shaped circuits. This
// keeps the FV pins stable and fully decoupled from the demo examples.
// ---------------------------------------------------------------------------

/// SHA-256 single-block compression: 2-word preimage → 8-word digest via
/// `sha256_block`.
fn sha256_block_src() -> String {
    String::from(
        r#"#![no_std]
use xark_sha256::prelude::*;
pub fn circuit(m: Private<[Field; 2]>, d: Public<[Field; 8]>) {
    let zero = [Field::constant("0"); 32];
    let mut w = [zero; 16];
    let b0 = m[0].to_bits::<32>();
    let mut j = 0usize;
    while j < 32usize { w[0][j] = b0[j]; j += 1; }
    let b1 = m[1].to_bits::<32>();
    let mut j = 0usize;
    while j < 32usize { w[1][j] = b1[j]; j += 1; }
    let hash = sha256_block(w);
    let mut i = 0usize;
    while i < 8usize {
        let mut word = zero;
        let mut j = 0usize;
        while j < 32usize { word[j] = hash[i][j]; j += 1; }
        require_eq(Field::from_bits::<32>(word), d[i]);
        i += 1;
    }
}
"#,
    )
}

/// Keccak-256 single (already-padded) rate block: 17-lane block → 4-lane digest
/// via `keccak256_block`.
fn keccak_block_src() -> String {
    String::from(
        r#"#![no_std]
use xark_bits::{from_bits64, to_bits64};
use xark_keccak::prelude::*;
pub fn circuit(words: Private<[Field; 17]>, d: Public<[Field; 4]>) {
    let zero = [Field::constant("0"); 64];
    let mut block = [zero; 17];
    let mut i = 0usize;
    while i < 17usize {
        let lane = to_bits64(words[i]);
        let mut j = 0usize;
        while j < 64usize { block[i][j] = lane[j]; j += 1; }
        i += 1;
    }
    let digest = keccak256_block(block);
    let mut i = 0usize;
    while i < 4usize {
        let mut lane = zero;
        let mut j = 0usize;
        while j < 64usize { lane[j] = digest[i][j]; j += 1; }
        require_eq(from_bits64(lane), d[i]);
        i += 1;
    }
}
"#,
    )
}

/// Variable-length Keccak-256 sponge over a 200-byte message (2 rate blocks) →
/// 4-lane digest.
fn keccak256_varlen_src() -> String {
    String::from(
        r#"#![no_std]
use xark_bits::from_bits64;
use xark_keccak::prelude::*;
pub fn circuit(msg: Private<[Field; 200]>, d: Public<[Field; 4]>) {
    let digest = keccak256::<200>(msg);
    let zero = [Field::from(0u8); 64];
    let mut i = 0usize;
    while i < 4usize {
        let mut lane = zero;
        let mut j = 0usize;
        while j < 64usize { lane[j] = digest[i][j]; j += 1; }
        require_eq(from_bits64(lane), d[i]);
        i += 1;
    }
}
"#,
    )
}

/// BLAKE3 single-block root over a 16-word message + length → 8-word digest via
/// `blake3_hash_one_block`, for the Lean bridge.
fn blake3_block_src() -> String {
    String::from(
        r#"#![no_std]
use xark_blake3::prelude::*;
pub fn circuit(m: Private<[Field; 16]>, len: Public<Field>, d: Public<[Field; 8]>) {
    let zero = [Field::constant("0"); 32];
    let mut w = [zero; 16];
    let mut i = 0usize;
    while i < 16usize {
        let bits = m[i].to_bits::<32>();
        let mut j = 0usize;
        while j < 32usize { w[i][j] = bits[j]; j += 1; }
        i += 1;
    }
    let hash = blake3_hash_one_block(w, len);
    let mut i = 0usize;
    while i < 8usize {
        let mut word = zero;
        let mut j = 0usize;
        while j < 32usize { word[j] = hash[i][j]; j += 1; }
        require_eq(Field::from_bits::<32>(word), d[i]);
        i += 1;
    }
}
"#,
    )
}

/// Byte-oriented BLAKE3 over an `n`-byte message → 8-word digest via
/// `blake3::<n>`, for the multi-block vector.
fn blake3_bytes_src(n: usize) -> String {
    format!(
        r#"#![no_std]
use xark_blake3::prelude::*;
pub fn circuit(msg: Private<[Field; {n}]>, d: Public<[Field; 8]>) {{
    let hash = blake3::<{n}>(msg);
    let zero = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 8usize {{
        let mut word = zero;
        let mut j = 0usize;
        while j < 32usize {{ word[j] = hash[i][j]; j += 1; }}
        require_eq(Field::from_bits::<32>(word), d[i]);
        i += 1;
    }}
}}
"#
    )
}

/// Unkeyed BLAKE2s single-block over a 16-word message → 8-word digest.
fn blake2s_block_src() -> String {
    String::from(
        r#"#![no_std]
use xark_blake2s::prelude::*;
pub fn circuit(m: Private<[Field; 16]>, len: Public<Field>, d: Public<[Field; 8]>) {
    let zero = [Field::constant("0"); 32];
    let mut w = [zero; 16];
    let mut i = 0usize;
    while i < 16usize {
        let bits = m[i].to_bits::<32>();
        let mut j = 0usize;
        while j < 32usize { w[i][j] = bits[j]; j += 1; }
        i += 1;
    }
    let hash = blake2s_hash_one_block(w, len);
    let mut i = 0usize;
    while i < 8usize {
        let mut word = zero;
        let mut j = 0usize;
        while j < 32usize { word[j] = hash[i][j]; j += 1; }
        require_eq(Field::from_bits::<32>(word), d[i]);
        i += 1;
    }
}
"#,
    )
}

/// Byte-oriented SHA-256 over an `n`-byte message → 8-word digest (the former
/// `examples/sha256_hash`), for the multi-block real-vector bridge.
fn sha256_bytes_src(n: usize) -> String {
    format!(
        r#"#![no_std]
use xark_sha256::prelude::*;
pub fn circuit(msg: Private<[Field; {n}]>, d: Public<[Field; 8]>) {{
    let hash = sha256::<{n}>(msg);
    let zero = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 8usize {{
        let mut word = zero;
        let mut j = 0usize;
        while j < 32usize {{ word[j] = hash[i][j]; j += 1; }}
        require_eq(Field::from_bits::<32>(word), d[i]);
        i += 1;
    }}
}}
"#
    )
}

/// Byte-oriented unkeyed BLAKE2s over an `n`-byte message → 8-word digest, for the
/// multi-block real-vector bridge.
fn blake2s_bytes_src(n: usize) -> String {
    format!(
        r#"#![no_std]
use xark_blake2s::prelude::*;
pub fn circuit(msg: Private<[Field; {n}]>, d: Public<[Field; 8]>) {{
    let hash = blake2s::<{n}>(msg);
    let zero = [Field::from(0u8); 32];
    let mut i = 0usize;
    while i < 8usize {{
        let mut word = zero;
        let mut j = 0usize;
        while j < 32usize {{ word[j] = hash[i][j]; j += 1; }}
        require_eq(Field::from_bits::<32>(word), d[i]);
        i += 1;
    }}
}}
"#
    )
}

/// Full SHA-256 single-block compression (`xark-sha256`): 64 rounds + message
/// schedule fully unrolled. This is a large circuit (~37k constraints) and the
/// main stress test for the compiler's inlining/unrolling performance — it
/// should compile in seconds, not minutes.
#[test]
fn sha256_compiles() {
    let c = compile_with_field(
        &write_case("sha256_stress", &sha256_block_src()),
        "sha256",
        "bn254",
    );
    assert!(c.status_success, "sha256 failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    // Count constraints from the parsed R1CS (note-robust): cache-all emits no
    // debug `source_span`/`note` on cached-function bodies, so the old
    // `"source_span"`-string proxy no longer tracks the constraint count.
    let constraints = xark_ir::json::from_json(&json).unwrap().constraints.len();
    // Deterministic circuit; exact counts guard against accidental changes.
    // `reduce::<N>` uses the tight per-site bit-width (schedule 34, e/a 36,
    // output 33) instead of a blanket 40, saving 856 carry-booleanity gates.
    // cache-all flat value; minimized/proving mul = 34934 (== the 37066-era
    // inlined optimum, so this is flat-only and proving-neutral). TODO:
    // nested-DAG plug-materialization sharing recovers the 37066 inlined flat.
    //
    // the 1952 `Maj` ANDs
    // reuse the previous round's `a ∧ b` rows (see `sha256_matches_lean_model`).
    let (want, want_w) = (35114, 6568);
    assert_eq!(constraints, want, "SHA-256 constraint count changed");
    assert_eq!(
        json.matches("\"name\": \"w").count(),
        want_w,
        "advice bit count changed"
    );
}

/// End-to-end: compile a gadget to the primitive IR (`circuit.json`), then run
/// its witness-generation hint program through the reference solver and check
/// the constraints hold. Proves the IR is self-contained (backend can resolve
/// everything from primitives) and semantically correct.
#[test]
fn primitive_ir_solves_bit_decompose() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};

    let c = compile_with_field(&example("bit_decompose"), "bits_solve", "bn254");
    assert!(c.status_success, "bit_decompose failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap();
    let program = primitive::from_json(&json).expect("valid circuit.json");

    let id_of = |name: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == name)
            .map(|v| v.id)
            .unwrap()
    };

    // Valid witness: x = 181 = 0b10110101, so bit 0 = 1 and bit 7 = 1.
    let mut inputs = BTreeMap::new();
    inputs.insert(id_of("x"), "181".to_string());
    inputs.insert(id_of("bit0"), "1".to_string());
    inputs.insert(id_of("bit7"), "1".to_string());
    let assign = solver::solve_and_check(&program, &inputs)
        .expect("valid witness should solve and satisfy all constraints");

    // Soundness smoke-test: every advice bit is uniquely pinned (booleanity +
    // recomposition), so none is a free / two-valued variable.
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(
        holes.is_empty(),
        "bit_decompose under-constrained: {holes:?}"
    );

    // Tampered public input: claim bit 0 is 0 (it's 1) — must fail.
    inputs.insert(id_of("bit0"), "0".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "a wrong public bit must violate a constraint"
    );
}

/// **Aggregate circuit inputs.** A `Private<[Field; 3]>` param collapses to `n`
/// `Field` input vars named by access path (`a[0]`/`a[1]`/`a[2]`), while a bare
/// `Field` stays a scalar. Confirms the flattened names, that it solves, and that
/// a wrong public output is rejected. (Struct inputs are covered byte-identically
/// by `ec_incomplete_matches_lean_model`, whose example takes `Private<Point>`.)
#[test]
fn aggregate_array_input_flattens_and_solves() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};

    let c = compile_with_field(&example("agg_input"), "agg_input", "bn254");
    assert!(c.status_success, "agg_input failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .expect("valid circuit.json");

    // The `Private<[Field;3]>` param `a` flattened to a[0]/a[1]/a[2]; `b` is scalar.
    let names: Vec<&str> = program.vars.iter().map(|v| v.name.as_str()).collect();
    for want in ["a[0]", "a[1]", "a[2]", "b"] {
        assert!(
            names.contains(&want),
            "missing flattened input `{want}`; got {names:?}"
        );
    }

    let id_of = |name: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == name)
            .map(|v| v.id)
            .unwrap()
    };
    let mut inputs = BTreeMap::new();
    inputs.insert(id_of("a[0]"), "2".to_string());
    inputs.insert(id_of("a[1]"), "3".to_string());
    inputs.insert(id_of("a[2]"), "5".to_string());
    inputs.insert(id_of("b"), "10".to_string()); // 2 + 3 + 5
    solver::solve_and_check(&program, &inputs).expect("2+3+5 == 10 must solve");

    // A wrong public sum is rejected.
    inputs.insert(id_of("b"), "11".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "wrong aggregate sum must violate a constraint"
    );
}

/// **`Field` op native-integer operators.** `a * 3 + 5` (`Mul<u64>` then
/// `Add<u64>`) — the int-RHS operators forward to the recognized `Field`-`Field`
/// ops with a constant, so they lower identically. Solve: `a=4 → 4*3+5 == 17`.
#[test]
fn field_int_operators_lower_and_solve() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};

    let c = compile_with_field(&example("field_int_ops"), "field_int_ops", "bn254");
    assert!(c.status_success, "field_int_ops failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .expect("valid circuit.json");
    let id_of = |name: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == name)
            .map(|v| v.id)
            .unwrap()
    };

    let mut inputs = BTreeMap::new();
    inputs.insert(id_of("a"), "4".to_string());
    inputs.insert(id_of("out"), "17".to_string()); // 4*3 + 5
    solver::solve_and_check(&program, &inputs).expect("a*3+5 with a=4 must equal 17");

    inputs.insert(id_of("out"), "18".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "wrong output must be rejected"
    );
}

/// Correctness against a real test vector: compile a SHA-256 single-block
/// compression, run its witness-gen hint program through the solver on the
/// SHA-256("abc") block (from xark's `sha256_basic`), and confirm it
/// produces the known digest and satisfies every constraint. `#[ignore]` because
/// the SHA-256 circuit takes ~15s to compile; run with `--ignored`.
#[test]
#[ignore]
fn sha256_matches_abc_vector() {
    use std::collections::BTreeMap;
    use std::fmt::Write as _;

    // Build the 16-block-word + 8-output-word validation circuit.
    let mut src = String::from(
        "#![no_std]\n\
         use xark::{require_eq, Field, Private, Public};\n\
         use xark_sha256::sha256_block;\npub fn circuit(\n",
    );
    for i in 0..16 {
        let _ = writeln!(src, "  b{i}: Private<Field>,");
    }
    for i in 0..8 {
        let _ = writeln!(src, "  o{i}: Public<Field>,");
    }
    src.push_str(") {\n  let zero = [Field::constant(\"0\"); 32];\n  let words = [");
    for i in 0..16 {
        let _ = write!(src, "b{i},");
    }
    src.push_str(
        "];\n  let mut w = [zero; 16];\n  let mut k = 0usize;\n\
        while k < 16usize { let bits = words[k].to_bits::<32>(); let mut j = 0usize; \
        while j < 32usize { w[k][j] = bits[j]; j += 1; } k += 1; }\n\
        let hash = sha256_block(w);\n  let o = [",
    );
    for i in 0..8 {
        let _ = write!(src, "o{i},");
    }
    src.push_str(
        "];\n  let mut i = 0usize;\n\
        while i < 8usize { let mut word = zero; let mut j = 0usize; \
        while j < 32usize { word[j] = hash[i][j]; j += 1; } \
        require_eq(Field::from_bits::<32>(word), o[i]); i += 1; }\n}\n",
    );

    let path = write_case("sha256_abc", &src);
    // Streamed correctness KAT: no `--emit-json`, no materialized flat program —
    // `check_named` solves + checks + analyzes straight from `circuit.xbc`.
    let c = xark_test_harness::compile_file(&path, "sha256_abc", "bn254");
    assert!(c.status_success, "sha256_abc failed: {}", c.stderr);

    let block = [
        "1633837952",
        "0",
        "0",
        "0",
        "0",
        "0",
        "0",
        "0",
        "0",
        "0",
        "0",
        "0",
        "0",
        "0",
        "0",
        "24",
    ];
    let out = [
        "3128432319",
        "2399260650",
        "1094795486",
        "1571693091",
        "2953011619",
        "2518121116",
        "3021012833",
        "4060091821",
    ];
    let mut inputs: BTreeMap<String, String> = BTreeMap::new();
    for (i, v) in block.iter().enumerate() {
        inputs.insert(format!("b{i}"), v.to_string());
    }
    for (i, v) in out.iter().enumerate() {
        inputs.insert(format!("o{i}"), v.to_string());
    }

    // The gadget computes real SHA-256("abc"): all constraints hold and no derived
    // variable is under-constrained (both checked, streamed, by `check_named`).
    c.check_named(&inputs)
        .expect("SHA-256(\"abc\") must verify and be fully constrained");

    // Negative control: a wrong digest word must violate a constraint.
    inputs.insert("o0".to_string(), "123456".to_string());
    assert!(
        c.check_named(&inputs).is_err(),
        "a wrong SHA-256 digest word must be rejected"
    );
}

/// Correctness against a real vector: compile the Keccak-256 gadget and solve
/// its hint program on the empty-message padded block; the output must be the
/// known Ethereum `keccak256("")` digest. `#[ignore]` (large circuit, ~20s+).
#[test]
#[ignore]
fn keccak_matches_empty_vector() {
    use std::collections::BTreeMap;

    let c = xark_test_harness::compile_file(
        &write_case("keccak_empty", &keccak_block_src()),
        "keccak",
        "bn254",
    );
    assert!(c.status_success, "keccak failed: {}", c.stderr);

    // Empty-message padded block (little-endian lanes): words[0]=1, words[16]=2^63.
    let mut inputs: BTreeMap<String, String> = BTreeMap::new();
    for i in 0..17 {
        inputs.insert(format!("words[{i}]"), "0".to_string());
    }
    inputs.insert("words[0]".to_string(), "1".to_string());
    inputs.insert("words[16]".to_string(), "9223372036854775808".to_string());
    // keccak256("") = c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
    let digest = [
        "4333579421379646149",
        "13836122230913597074",
        "4262519377828905189",
        "8116759062988257915",
    ];
    for (i, v) in digest.iter().enumerate() {
        inputs.insert(format!("d[{i}]"), v.to_string());
    }
    // Correctness + soundness (every fused-XOR output and advice bit uniquely
    // pinned), streamed from `circuit.xbc`.
    c.check_named(&inputs)
        .expect("keccak256(\"\") must verify and be fully constrained");

    inputs.insert("d[0]".to_string(), "42".to_string());
    assert!(
        c.check_named(&inputs).is_err(),
        "a wrong keccak digest word must be rejected"
    );
}

/// Variable-length Keccak-256 sponge against a REAL 2-block reference vector.
///
/// Hashes the 200-byte message `bytes(0..200)` (spans 2 rate blocks, padded to
/// 272 bytes) and constrains the digest to the genuine Ethereum `keccak256`
/// output, computed independently via `cast keccak`:
///   keccak256(bytes(0..200)) =
///     0xbfb0aa97863e797943cf7c33bb7e880bb4543f3d2703c0923c6901c2af57b890
/// Checks (1) correctness by solving the hint program, (2) soundness via the
/// under-constrained analyzer, and (3) a negative control (a wrong digit is
/// rejected). Large circuit (~2× keccak_f), so `#[ignore]` by default; run with
/// `cargo test --test snapshot -- --ignored keccak256`.
#[test]
#[ignore]
fn keccak256_varlen_matches_real_vector() {
    use std::collections::BTreeMap;

    let c = xark_test_harness::compile_file(
        &write_case("keccak256_varlen", &keccak256_varlen_src()),
        "keccak256",
        "bn254",
    );
    assert!(c.status_success, "keccak256 varlen failed: {}", c.stderr);

    // Private message = bytes 0..200.
    let mut inputs: BTreeMap<String, String> = BTreeMap::new();
    for i in 0..200usize {
        inputs.insert(format!("msg[{i}]"), i.to_string());
    }
    // Public digest, little-endian 64-bit lanes of
    // 0xbfb0aa97863e797943cf7c33bb7e880bb4543f3d2703c0923c6901c2af57b890.
    let digest = [
        "8753096098562355391",
        "831053473737658179",
        "10574455392132093108",
        "10428181349562149180",
    ];
    for (i, v) in digest.iter().enumerate() {
        inputs.insert(format!("d[{i}]"), v.to_string());
    }

    // Correctness (reproduces the genuine keccak256 digest) + soundness (no
    // under-constrained var), streamed from `circuit.xbc`.
    c.check_named(&inputs)
        .expect("keccak256(bytes(0..200)) must verify and be fully constrained");

    // Negative control: a wrong digest word must violate a constraint.
    inputs.insert("d[0]".to_string(), "42".to_string());
    assert!(
        c.check_named(&inputs).is_err(),
        "a wrong keccak digest word must be rejected"
    );
}

/// Fused subtract `(a-b-c) mod p`: correctness, analyzer, forgery rejection, and
/// an adversarial internal-carry inflation test.
#[test]
fn sub2_matches_vector_and_rejects_forgery() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};

    let comp = compile_with_field(&example("sub2"), "sub2", "bn254");
    assert!(comp.status_success, "sub2 failed: {}", comp.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(comp.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |name: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == name)
            .map(|v| v.id)
            .unwrap()
    };
    let set = |m: &mut BTreeMap<u32, String>, pre: &str, v: [&str; 3]| {
        for (i, vi) in v.iter().enumerate() {
            m.insert(id(&format!("{pre}[{i}]")), vi.to_string());
        }
    };
    // a < b+c so qabs = 1 (borrow path exercised).
    let mut inputs = BTreeMap::new();
    set(
        &mut inputs,
        "a",
        [
            "20632333988089671248318737",
            "5158083497022417812079684",
            "5037190915060954894609",
        ],
    );
    set(
        &mut inputs,
        "b",
        [
            "30948500982134506872478105",
            "46422751473201760308717158",
            "45334718235548594051481",
        ],
    );
    set(
        &mut inputs,
        "c",
        [
            "10316166994044835624159368",
            "41264667976179342496637474",
            "40297527320487639156872",
        ],
    );
    set(
        &mut inputs,
        "r",
        [
            "56738918467246591637908255",
            "72213168958313849369115579",
            "19262218059193091516985070",
        ],
    );

    // (1) correctness + (2) analyzer-clean.
    let assign = solver::solve_and_check(&program, &inputs).expect("(a-b-c) mod p must verify");
    assert!(
        solver::analyze_underconstrained(&program, &assign).is_empty(),
        "sub2 under-constrained"
    );

    // (3) forgery: claim a wrong result → rejected.
    let mut bad = inputs.clone();
    bad.insert(id("r[0]"), "12345".to_string());
    assert!(
        solver::solve_and_check(&program, &bad).is_err(),
        "wrong result must be rejected"
    );

    // (4) adversarial: inflate an internal carry (a derived var with a small honest
    // value in [2,7] is a biased carry; bits are 0/1 and result limbs are ~2^85).
    // Pushing it out of its 3-bit range must make the constraints reject it.
    let carry = program
        .vars
        .iter()
        .find(|v| {
            matches!(v.role, primitive::VarRole::Derived)
                && assign
                    .get(&v.id)
                    .map(|x| {
                        let d = x.to_decimal();
                        d.parse::<u64>()
                            .map(|n| (2..=7).contains(&n))
                            .unwrap_or(false)
                    })
                    .unwrap_or(false)
        })
        .expect("a biased carry variable should exist");
    let mut forged = assign.clone();
    let infl = forged
        .get(&carry.id)
        .unwrap()
        .to_decimal()
        .parse::<u64>()
        .unwrap()
        + 8;
    forged.insert(
        carry.id,
        solver::fp_from_decimal(&infl.to_string(), &program),
    );
    assert!(
        solver::check(&program, &forged).is_err(),
        "out-of-range carry must be rejected"
    );
}

/// Validate the 3-limb secp256r1 (a=-3) incomplete EC ops: `2G`/`3G` from `G`.
#[test]
#[ignore]
fn ec_incomplete_r1_matches_vectors() {
    use std::collections::BTreeMap;

    let c =
        xark_test_harness::compile_file(&example("ec_incomplete_r1"), "ec_incomplete_r1", "bn254");
    assert!(c.status_success, "ec_incomplete_r1 failed: {}", c.stderr);
    let set = |m: &mut BTreeMap<String, String>, pre: &str, v: [&str; 3]| {
        for (i, vi) in v.iter().enumerate() {
            m.insert(format!("{pre}[{i}]"), vi.to_string());
        }
    };
    let mut inputs: BTreeMap<String, String> = BTreeMap::new();
    set(
        &mut inputs,
        "g.x.limbs",
        [
            "52227620040540588600771222",
            "33347259622618539004134583",
            "8091721874918813684698062",
        ],
    );
    set(
        &mut inputs,
        "g.y.limbs",
        [
            "59685082318776612195095029",
            "54599710628478995760242092",
            "6036146923926000695307902",
        ],
    );
    set(
        &mut inputs,
        "two_g.x.limbs",
        [
            "60574784517941929169033592",
            "38742641973200156549941727",
            "9440742814978962916680995",
        ],
    );
    set(
        &mut inputs,
        "two_g.y.limbs",
        [
            "50180633949907515547874257",
            "52108912657982010475124979",
            "564125721045731681407961",
        ],
    );
    set(
        &mut inputs,
        "three_g.x.limbs",
        [
            "55202213340089332766604652",
            "75352241312048865668270014",
            "7162618025266537839759230",
        ],
    );
    set(
        &mut inputs,
        "three_g.y.limbs",
        [
            "19003939109578686433415218",
            "32907397120494406415210721",
            "10215774641556159746766000",
        ],
    );

    c.check_named(&inputs)
        .expect("r1 3-limb 2G/3G must verify and be fully constrained");
    inputs.insert("two_g.y.limbs[0]".to_string(), "7".to_string());
    assert!(
        c.check_named(&inputs).is_err(),
        "a wrong EC output limb must be rejected"
    );
}

/// Validate the 3-limb (86-bit) incomplete EC ops: `2G` and `3G` from `G`.
/// Exercises the whole 3-limb field stack (add/sub/mul/inverse), analyzer-clean.
#[test]
#[ignore]
fn ec_incomplete_matches_vectors() {
    use std::collections::BTreeMap;

    let c = xark_test_harness::compile_file(&example("ec_incomplete"), "ec_incomplete", "bn254");
    assert!(c.status_success, "ec_incomplete failed: {}", c.stderr);
    let set = |m: &mut BTreeMap<String, String>, pre: &str, v: [&str; 3]| {
        for (i, vi) in v.iter().enumerate() {
            m.insert(format!("{pre}[{i}]"), vi.to_string());
        }
    };
    let mut inputs: BTreeMap<String, String> = BTreeMap::new();
    set(
        &mut inputs,
        "g.x.limbs",
        [
            "17117865558768631194064792",
            "12501176021340589225372855",
            "9198697782662356105779718",
        ],
    );
    set(
        &mut inputs,
        "g.y.limbs",
        [
            "6441780312434748884571320",
            "57953919405111227542741658",
            "5457536640262350763842127",
        ],
    );
    set(
        &mut inputs,
        "two_g.x.limbs",
        [
            "57105948487393027623526117",
            "2088890992725950981549619",
            "14961784698075395646489684",
        ],
    );
    set(
        &mut inputs,
        "two_g.y.limbs",
        [
            "46925586441427271765976362",
            "19820246243853867596485833",
            "2031033786214458435714136",
        ],
    );
    set(
        &mut inputs,
        "three_g.x.limbs",
        [
            "57545291876987742944507641",
            "75066192660561802595210765",
            "18828234277447069677687620",
        ],
    );
    set(
        &mut inputs,
        "three_g.y.limbs",
        [
            "2583640362791394057184882",
            "38197615293098406611150035",
            "4273588397735691711217203",
        ],
    );

    c.check_named(&inputs)
        .expect("3-limb 2G/3G must verify and be fully constrained");
    inputs.insert("two_g.x.limbs[0]".to_string(), "1".to_string());
    assert!(
        c.check_named(&inputs).is_err(),
        "a wrong EC output limb must be rejected"
    );
}

/// Prototype: validate the 3×86-bit `mod_mul` computes `a·b mod p` correctly
/// and is analyzer-clean (confirms the limb-size optimization is sound).
#[test]
fn fp_mul_matches_vector() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};

    let c = compile_with_field(&example("fp_mul"), "fp_mul", "bn254");
    assert!(c.status_success, "fp_mul failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |name: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == name)
            .map(|v| v.id)
            .unwrap()
    };

    // a·b ≡ c (mod p) with 3×86-bit limbs.
    let a = [
        "67135996574970214581469201",
        "51946031311641451697362329",
        "16825126466515450054094827",
    ];
    let b = [
        "24414941800469763390285221",
        "15797894945784124056166873",
        "85968058283706962481699",
    ];
    let cc = [
        "3097648669108091694378015",
        "51742203992647403024604737",
        "1775314877412124564790042",
    ];
    let mut inputs = BTreeMap::new();
    for i in 0..3 {
        inputs.insert(id(&format!("a[{i}]")), a[i].to_string());
        inputs.insert(id(&format!("b[{i}]")), b[i].to_string());
        inputs.insert(id(&format!("c[{i}]")), cc[i].to_string());
    }
    let assign = solver::solve_and_check(&program, &inputs).expect("3-limb a·b mod p must verify");
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "mod_mul under-constrained: {holes:?}");

    inputs.insert(id("c[0]"), "123".to_string());
    assert!(solver::solve_and_check(&program, &inputs).is_err());
}

/// Deterministic output: compiling twice yields byte-identical JSON.
#[test]
fn output_is_deterministic() {
    let a = compile(&example("cube"), "cube_det_a");
    let b = compile(&example("cube"), "cube_det_b");
    let ja = std::fs::read_to_string(a.out_dir.join("r1cs.json")).unwrap();
    let jb = std::fs::read_to_string(b.out_dir.join("r1cs.json")).unwrap();
    assert_eq!(ja, jb);
}

// --- rejection cases -------------------------------------------------------

fn write_case(name: &str, body: &str) -> PathBuf {
    let dir = workspace_root().join("target/test-cases");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{name}.rs"));
    std::fs::write(&path, body).unwrap();
    path
}

#[test]
fn rejects_native_u64_param() {
    let src = write_case(
        "u64",
        "#![no_std]\nuse xark::{Field, Public};\n\
         pub fn circuit(a: u64, c: Public<Field>) { let _ = (a, c); }\n",
    );
    let c = compile(&src, "reject_u64");
    assert!(!c.status_success);
    assert!(
        c.stderr
            .contains("unsupported circuit parameter type `u64`"),
        "{}",
        c.stderr
    );
}

/// A compile-time-constant branch (`if true`) is resolved at lowering — the
/// taken branch is emitted, the other is dropped. (Witness-dependent branches
/// can't even be written: `Field` isn't comparable.)
#[test]
fn constant_branch_is_resolved() {
    let src = write_case(
        "ctrl",
        "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, c: Public<Field>) { if true { require_eq(a, c); } }\n",
    );
    let c = compile(&src, "const_branch");
    assert!(c.status_success, "if true failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    assert_eq!(json.matches("\"source_span\"").count(), 1);
}

/// A `while` loop with a compile-time bound is unrolled: `acc *= a` twice gives
/// `a^3`, and indexing an array by the loop counter resolves per iteration.
#[test]
fn while_loop_unrolls() {
    let src = write_case(
        "whileloop",
        "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, c: Public<Field>) {\n\
             let mut acc = a; let mut i = 0u64;\n\
             while i < 2 { acc = acc * a; i += 1; }\n\
             require_eq(acc, c);\n\
         }\n",
    );
    let c = compile(&src, "while_loop");
    assert!(c.status_success, "while loop failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    // Unrolled to a^3: a*a=t0, t0*a=c.
    assert_eq!(json.matches("\"source_span\"").count(), 2);
    assert!(json.contains("\"note\": \"a * a = t0\""), "{json}");
    assert!(json.contains("\"note\": \"t0 * a = c\""), "{json}");
}

/// A `for i in a..b` loop over a constant integer range lowers **byte-for-byte
/// identically** to the hand-written `let mut i = a; while i < b { .. i += 1; }`.
/// This is the core correctness gate for `for`-range support: the desugared
/// iterator calls (`into_iter`/`next`) are modeled at compile time so the loop
/// unrolls into the exact same R1CS. Checked for a value use (`acc * a`), an
/// array index (`arr[i]`), and an inclusive range (`a..=b` ≡ `while i <= b`),
/// across both `circuit.json` and `r1cs.json`.
#[test]
fn for_range_equals_while() {
    // (1) cube via `for _ in 0..2` ≡ `while i < 2`.
    let cf = compile(&example("for_cube"), "for_cube");
    assert!(cf.status_success, "for_cube failed: {}", cf.stderr);
    let cw = compile(
        &write_case(
            "for_cube_while",
            "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
             pub fn circuit(a: Private<Field>, c: Public<Field>) {\n\
                 let mut acc = a; let mut i = 0u64;\n\
                 while i < 2u64 { acc = acc * a; i += 1; }\n\
                 require_eq(acc, c);\n\
             }\n",
        ),
        "for_cube_while",
    );
    assert!(cw.status_success, "for_cube while failed: {}", cw.stderr);
    assert_for_equals_while(&cf, &cw, "for_cube");
    // a^3: a*a=t0, t0*a=c → 2 constraints.
    let json = std::fs::read_to_string(cf.out_dir.join("r1cs.json")).unwrap();
    assert_eq!(json.matches("\"source_span\"").count(), 2);

    // (2) array indexed by the loop counter: `for i in 0..3 { acc += arr[i]; }`.
    let idxf = compile(&example("for_index"), "for_index");
    assert!(idxf.status_success, "for_index failed: {}", idxf.stderr);
    let idxw = compile(
        &write_case(
            "for_index_while",
            "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
             pub fn circuit(a: Private<Field>, b: Private<Field>, c: Public<Field>) {\n\
                 let arr = [a, b, a];\n\
                 let mut acc = Field::constant(\"0\"); let mut i = 0usize;\n\
                 while i < 3 { acc = acc + arr[i]; i += 1; }\n\
                 require_eq(acc, c);\n\
             }\n",
        ),
        "for_index_while",
    );
    assert!(
        idxw.status_success,
        "for_index while failed: {}",
        idxw.stderr
    );
    assert_for_equals_while(&idxf, &idxw, "for_index");

    // (3) inclusive `for i in 0..=2` ≡ `while i <= 2` (a^4).
    let incf = compile(
        &write_case(
            "for_incl",
            "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
             pub fn circuit(a: Private<Field>, c: Public<Field>) {\n\
                 let mut acc = a;\n\
                 for _i in 0..=2u64 { acc = acc * a; }\n\
                 require_eq(acc, c);\n\
             }\n",
        ),
        "for_incl",
    );
    assert!(incf.status_success, "for_incl failed: {}", incf.stderr);
    let incw = compile(
        &write_case(
            "for_incl_while",
            "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
             pub fn circuit(a: Private<Field>, c: Public<Field>) {\n\
                 let mut acc = a; let mut i = 0u64;\n\
                 while i <= 2u64 { acc = acc * a; i += 1; }\n\
                 require_eq(acc, c);\n\
             }\n",
        ),
        "for_incl_while",
    );
    assert!(
        incw.status_success,
        "for_incl while failed: {}",
        incw.stderr
    );
    assert_for_equals_while(&incf, &incw, "for_incl (a..=b)");
}

/// Iterating a **fixed-size array** — by value (`for x in arr`) and by reference
/// (`for x in &arr`) — lowers byte-for-byte identically to the counter-indexed
/// `while i < N { let x = arr[i]; .. }`. The array's element values are captured
/// at compile time (references are transparent in the value model), so the two
/// desugared iterators (`array::IntoIter` / `slice::Iter`) unroll to identical
/// R1CS.
#[test]
fn for_array_equals_while() {
    let byval = compile(&example("for_array"), "for_array");
    assert!(byval.status_success, "for_array failed: {}", byval.stderr);
    let byref = compile(
        &write_case(
            "for_array_ref",
            "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
             pub fn circuit(a: Private<Field>, b: Private<Field>, c: Public<Field>) {\n\
                 let arr = [a, b, a];\n\
                 let mut acc = Field::constant(\"0\");\n\
                 for x in &arr { acc = acc + *x; }\n\
                 require_eq(acc, c);\n\
             }\n",
        ),
        "for_array_ref",
    );
    assert!(
        byref.status_success,
        "for_array ref failed: {}",
        byref.stderr
    );
    let whilev = compile(
        &write_case(
            "for_array_while",
            "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
             pub fn circuit(a: Private<Field>, b: Private<Field>, c: Public<Field>) {\n\
                 let arr = [a, b, a];\n\
                 let mut acc = Field::constant(\"0\"); let mut i = 0usize;\n\
                 while i < 3 { acc = acc + arr[i]; i += 1; }\n\
                 require_eq(acc, c);\n\
             }\n",
        ),
        "for_array_while",
    );
    assert!(
        whilev.status_success,
        "for_array while failed: {}",
        whilev.stderr
    );
    assert_for_equals_while(&byval, &whilev, "for x in arr");
    assert_for_equals_while(&byref, &whilev, "for x in &arr");
}

/// Iterator adapters over concrete ranges and slices (`.rev()`, `.iter()`) run as
/// ordinary code and compute what Rust says.
#[test]
fn for_over_iterator_adapters() {
    let mk = |name: &str, body: &str| {
        write_case(
            name,
            &format!(
                "#![no_std]\nuse xark::{{require_eq, Field, Private, Public}};\n\
                 pub fn circuit(a: Private<Field>, c: Public<Field>) {{\n\
                     let arr = [a, a];\n\
                     let mut acc = a;\n\
                     {body}\n\
                     require_eq(acc, c);\n\
                 }}\n"
            ),
        )
    };

    let rev = compile_with_field(
        &mk(
            "for_reject_rev",
            "for _i in (0..2).rev() { acc = acc * a; }",
        ),
        "for_reject_rev",
        "bn254",
    );
    assert!(rev.status_success, "{}", rev.stderr);
    assert!(accepts(&rev, &[("a", "2"), ("c", "8")]));
    assert!(!accepts(&rev, &[("a", "2"), ("c", "9")]));
    let it = compile_with_field(
        &mk("for_reject_iter", "for x in arr.iter() { acc = acc + *x; }"),
        "for_reject_iter",
        "bn254",
    );
    assert!(it.status_success, "{}", it.stderr);
    assert!(accepts(&it, &[("a", "5"), ("c", "15")]));
    assert!(!accepts(&it, &[("a", "5"), ("c", "10")]));
}

/// A helper function is inlined, and a multiplication inside it still merges
/// into the following `require_eq` — proving the gadget-as-library model.
#[test]
fn inlines_helper_function() {
    let src = write_case(
        "square",
        "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
         fn square(x: Field) -> Field { x * x }\n\
         pub fn circuit(a: Private<Field>, c: Public<Field>) { require_eq(square(a), c); }\n",
    );
    let c = compile(&src, "inline_square");
    assert!(c.status_success, "square failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    // Inlined `a*a` merges with `== c` into a single `a * a = c` constraint,
    // with no leftover internal variable.
    assert_eq!(json.matches("\"source_span\"").count(), 1);
    assert!(
        json.contains("\"note\": \"a * a = c\""),
        "unexpected R1CS: {json}"
    );
    assert!(
        !json.contains("\"name\": \"t0\""),
        "mul gate should have merged away"
    );
}

/// A recursive helper is rejected rather than looping forever.
#[test]
fn rejects_recursion() {
    let src = write_case(
        "recurse",
        "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
         fn rec(x: Field) -> Field { rec(x) }\n\
         pub fn circuit(a: Private<Field>, c: Public<Field>) { require_eq(rec(a), c); }\n",
    );
    let c = compile(&src, "reject_recurse");
    assert!(!c.status_success);
    assert!(
        c.stderr.contains("recursion is not supported"),
        "{}",
        c.stderr
    );
}

/// **R1CS ↔ Lean bridge (Poseidon2, t = 3).**
///
/// The Lean theorem `Xark.poseidon2_bn254_t3_determined`
/// (`formal/Formal/Poseidon2Bn254T3.lean`) proves the BN254 / t = 3 Poseidon2
/// permutation — built from 80 `x⁵` S-boxes (8 full rounds × 3 cells + 56
/// partial × 1 cell), each `x⁵` expanded as 3 multiplications (`x²`, `x⁴`, `x⁵`)
/// — is a deterministic function of its input (no prover freedom).
///
/// That proof is about the *abstract* permutation; this test is the bridge to
/// the *actual* `xark-poseidon2` gadget: it compiles the gadget and pins the
/// number of genuine multiplication gates (both operands variable) to the 240
/// the Lean model assumes. Any drift in the gadget's S-box expansion or round
/// schedule changes this count and fails here, forcing the proof to be
/// re-checked against the new shape.
#[test]
fn poseidon2_matches_lean_t3_model() {
    let c =
        xark_test_harness::compile_file(&example("poseidon2"), "poseidon2_lean_bridge", "bn254");
    assert!(c.status_success, "poseidon2 gadget compiles: {}", c.stderr);
    // Mult-gate count, streamed from `circuit.xbc` (no r1cs.json materialization).
    let mul_gates = c.mul_gate_count();

    // 80 S-boxes × 3 multiplications — the shape `poseidon2_bn254_t3_determined`
    // is stated over. If this fails, reconcile the gadget with the Lean model.
    assert_eq!(
        mul_gates, 240,
        "Poseidon2 t=3 must emit 240 S-box multiplications (matches \
         Xark.poseidon2_bn254_t3_determined); got {mul_gates}"
    );
}

/// **R1CS ↔ Lean bridge (SHA-256).**
///
/// `formal/Formal/Sha256.lean` proves each SHA-256 primitive gadget is `BitOf`
/// its spec bit — `rotr_sound`, `shr_sound`, `not32_sound`, `and32_sound`,
/// `xor32_sound`, the composite `Ch_bit_sound` / `Maj_bit_sound`, the Σ/σ
/// identities and `MessageScheduleStep` (the gadget builds on the same
/// `xark-bits` primitives). This test pins the *Rust* gadget to that model: the
/// number of genuine multiplication gates (bit-AND products + carry booleanity)
/// is fixed, so any drift in the gadget forces the bit-soundness proof to be
/// re-checked against the new shape.
#[test]
fn sha256_matches_lean_model() {
    let c = xark_test_harness::compile_file(
        &write_case("sha256_lean", &sha256_block_src()),
        "sha256_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "sha256 gadget compiles: {}", c.stderr);
    // Mult-gate count, streamed from `circuit.xbc` (no r1cs.json materialization).
    let mul = c.mul_gate_count();
    // The Lean model proves the bit *primitives* (and32/xor32/rotr/Ch/Maj/Σ/σ
    // and MessageScheduleStep); the wrapping-add carry is discharged separately
    // (Bitwise/Arith.lean). Tightening `reduce::<N>` to each site's true bound
    // (40→34/36/33) removes 856 carry-booleanity gates without touching any
    // primitive Lean proves, so the bit-soundness model is unaffected.
    // cache-all flat value; minimized/proving mul = 34934 (unchanged — the
    // cached bit-gadgets re-decompose their outputs in the flat R1CS, but that
    // booleanity is folded away by the minimizer the prover runs, so what is
    // proven still matches the Sha256.lean model). TODO: nested-DAG plug-
    // materialization sharing recovers the 34934 inlined flat.
    //
    // 34934 (the flat value above) − 1952 = 32982. Each round's
    // `Maj(a, b, c)` ANDs `b ∧ c`, which is the previous round's `a ∧ b` on the same
    // bit wires (the state shifts `a → b → c`): 61 rounds × 32 bits reuse that row
    // (`Xark.R1cs.cse_sound`) instead of re-emitting `bᵢ · cᵢ = t`. The reused
    // output satisfies the very `and_sound` row the model is stated over.
    let want = 32982;
    assert_eq!(
        mul, want,
        "SHA-256 multiplication-gate count pins the Sha256.lean bit-soundness model; got {mul}"
    );
}

/// **R1CS ↔ Lean bridge (BLAKE3).**
/// `formal/Formal/Blake.lean` proves the BLAKE G-mixing is bit-sound —
/// `addMod32_bit_sound` (wrapping-add carry), `xor32_bit_sound`,
/// `rotr_bit_sound`, and `blake3_round_compose_bit` (7-round schedule, message
/// permutation `[2,6,3,10,7,0,4,13,…]`). Pins the Rust gadget's mult-gate count.
#[test]
fn blake3_matches_lean_model() {
    let c = xark_test_harness::compile_file(
        &write_case("blake3_lean", &blake3_block_src()),
        "blake3_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "blake3 gadget compiles: {}", c.stderr);
    // Mult-gate count, streamed from `circuit.xbc` (no r1cs.json materialization).
    let mul = c.mul_gate_count();
    // The `g` mixing's `a + b + m` steps use a single 34-bit `add3` range-check
    // (Blake.lean `add3Mod32_bit_sound`, bridged to the nested-`addMod32` spec by
    // `add3Mod32_eq_nested`) instead of two chained `add32`s — 2 fewer carry
    // decompositions per `g`, so the mult-gate count drops from 18832 to 15248.
    assert_eq!(
        mul, 15248,
        "BLAKE3 mult-gate count pins blake3_round_compose_bit; got {mul}"
    );
}

/// **R1CS ↔ Lean bridge (BLAKE2s).**
/// Same `Blake.lean` G-mixing soundness, via `blake2s_round_compose_bit`
/// (10-round schedule, the 10 SIGMA rows). Pins the Rust gadget's mult-gate count.
#[test]
fn blake2s_matches_lean_model() {
    let c = xark_test_harness::compile_file(
        &write_case("blake2s_lean", &blake2s_block_src()),
        "blake2s_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "blake2s gadget compiles: {}", c.stderr);
    // Mult-gate count, streamed from `circuit.xbc` (no r1cs.json materialization).
    let mul = c.mul_gate_count();
    // Same `add3` (34-bit) mixing tightening as BLAKE3 (Blake.lean
    // `add3Mod32_bit_sound`): 26720 → 21600 mult-gates.
    assert_eq!(
        mul, 21600,
        "BLAKE2s mult-gate count pins blake2s_round_compose_bit; got {mul}"
    );
}

/// **R1CS ↔ Lean bridge (Keccak-f[1600]).** `#[ignore]` — 156k constraints.
/// `formal/Formal/Keccak.lean` proves per-bit soundness of one round
/// `ι∘χ∘π∘ρ∘θ` (`keccakRoundStep_bit_sound`). The ρ·π
/// permutation index in the Lean model was corrected to `(X+3Y)%5` to match this
/// (KAT-verified) gadget exactly across all 25 lanes. This test pins the count.
#[test]
#[ignore]
fn keccak_matches_lean_model() {
    let c = xark_test_harness::compile_file(
        &write_case("keccak_lean", &keccak_block_src()),
        "keccak_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "keccak gadget compiles: {}", c.stderr);
    // Mult-gate count, streamed from `circuit.xbc` (no r1cs.json materialization).
    let mul = c.mul_gate_count();
    assert_eq!(mul, 153664, "Keccak mult-gate count; got {mul}");
}

/// **R1CS ↔ Lean bridge (AES-128).** `#[ignore]` — 158k constraints.
/// `formal/Formal/Aes.lean` proves the linear layers + S-box soundness. NOTE:
/// the Lean S-box is modeled as a *table lookup* while this gadget computes it
/// *algebraically* (`affine(b^254)`, Itoh–Tsujii); `GF256.lean`'s
/// `aesSbox_algebraic_eq_table` is the link that must be threaded to make the
/// proof cover this gadget. This test pins the Rust gadget's mult-gate count.
#[test]
#[ignore]
fn aes_matches_lean_model() {
    let c = xark_test_harness::compile_file(&example("aes"), "aes_lean_bridge", "bn254");
    assert!(c.status_success, "aes gadget compiles: {}", c.stderr);
    // Mult-gate count, streamed from `circuit.xbc` (no r1cs.json materialization).
    let mul = c.mul_gate_count();
    // 145816 for the block + 384 booleanity rows range-checking the example's 48
    // `u8` inputs (8 bits each; the inputs became `[u8; 16]` in c0b63cd).
    assert_eq!(mul, 146200, "AES-128 mult-gate count; got {mul}");
}

/// **R1CS ↔ Lean bridge (AES-256).** The AES-256 block reuses the exact round-step
/// (`SubBytes → ShiftRows → MixColumns → AddRoundKey`) proven bit-sound in
/// `formal/Formal/Aes.lean` (`aesRoundStep_bit_sound`, key-size-independent) — just
/// 14 rounds instead of 10. The 256-bit key schedule (`Nk = 8`, 60 words, with the
/// extra `SubWord` at `i % 8 == 4`) is proven sound in `formal/Formal/Aes256.lean`:
/// `aes256KeyExpansion_from_witness` shows a byte trace satisfying the FIPS-197
/// recurrence equals the expanded key (via strong-induction `wordBytes_eq`), reusing
/// the AES-128 S-box/`xor8` primitives. This pins the Rust gadget's mult-gate count.
/// `#[ignore]` — ~200k.
#[test]
#[ignore]
fn aes256_matches_lean_model() {
    let src = "#![no_std]\n\
        use xark::{Field, Private, Public};\n\
        use xark_aes::aes256_constrain;\n\
        pub fn circuit(pt: Private<[Field; 16]>, key: Private<[Field; 32]>, ct: Public<[Field; 16]>) {\n\
        aes256_constrain(pt, key, ct);\n\
        }\n";
    let c = xark_test_harness::compile_file(
        &write_case("aes256_lean", src),
        "aes256_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "aes256 gadget compiles: {}", c.stderr);
    // Mult-gate count, streamed from `circuit.xbc` (no r1cs.json materialization).
    let mul = c.mul_gate_count();
    assert_eq!(mul, 201484, "AES-256 mult-gate count; got {mul}");
}

/// **R1CS ↔ Lean bridge (GHASH GF(2¹²⁸) multiply).** `formal/Formal/GF128.lean`
/// models the GCM binary field `GF(2¹²⁸) = GF(2)[x]/(x¹²⁸+x⁷+x²+x+1)` — the
/// carryless product + reduction spec, and the bit-serial (NIST SP 800-38D
/// Algorithm 1) recurrence the gadget implements (`gf128_timesX` / `gf128_xpow`) —
/// and **proves soundness end-to-end**: `gf128_bitserial_eq_mul` shows the gadget's
/// bit-serial multiply equals the GF(2¹²⁸) field product (axiom-clean), via the
/// reduction-step linearity `gf128_timesX_bit`, the running-value invariant
/// `gf128_V_bit`, and digit extraction `gf128_mul_bit`; the multiply is also
/// well-defined (`gf128_mul_lt_two128`). Pins the mult-gate count of one `gf128_mul`
/// (the GHASH core). `#[ignore]` — ~34k.
#[test]
#[ignore]
fn gf128_mul_matches_lean_model() {
    let src = "#![no_std]\n\
        use xark::{require_eq, Field, Private, Public};\n\
        use xark_aes::{gf128_mul, bytes_to_gf128, gf128_to_bytes};\n\
        pub fn circuit(x: Private<[Field; 16]>, y: Private<[Field; 16]>, z: Public<[Field; 16]>) {\n\
        let p = gf128_to_bytes(gf128_mul(bytes_to_gf128(x), bytes_to_gf128(y)));\n\
        let mut i = 0usize;\n  while i < 16usize { require_eq(p[i], z[i]); i += 1; }\n}\n";
    let c = xark_test_harness::compile_file(
        &write_case("gf128_lean", src),
        "gf128_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "gf128_mul gadget compiles: {}", c.stderr);
    // Mult-gate count, streamed from `circuit.xbc` (no r1cs.json materialization).
    let mul = c.mul_gate_count();
    assert_eq!(mul, 33280, "GF(2^128) multiply mult-gate count; got {mul}");
}

/// **R1CS ↔ Lean bridge (AES-128-GCM composition).** The full AEAD composes the
/// proven pieces: the hash subkey `H = AES_enc(key, 0¹²⁸)` and `E(J0)` reuse the
/// `Aes.lean` block soundness; confidentiality is CTR (AES rounds + XOR); the tag is
/// `GHASH_H(A ‖ C ‖ [len]) ⊕ E(J0)` where each GHASH step is a `GF128.lean`
/// `gf128_mul` (well-defined by `gf128_mul_lt_two128`). This pins the whole-mode
/// mult-gate count of `examples/aes_gcm` (13-byte AAD + 20-byte message).
/// `#[ignore]` — ~765k constraints.
#[test]
#[ignore]
fn aes_gcm_matches_lean_model() {
    let c = xark_test_harness::compile_file(&example("aes_gcm"), "aes_gcm_lean_bridge", "bn254");
    assert!(c.status_success, "aes_gcm gadget compiles: {}", c.stderr);
    // Mult-gate count, streamed from `circuit.xbc` (no r1cs.json materialization).
    let mul = c.mul_gate_count();
    // Flat (no templates). 160 fewer than before AND outputs (products of pinned
    // bits) were known boolean: a `to_bits` of a sum of them now reuses those bits
    // (the bit-sum shortcut) instead of re-decomposing.
    let want = 715824;
    assert_eq!(mul, want, "AES-128-GCM mult-gate count; got {mul}");
}

/// **R1CS ↔ Lean bridge (secp256k1 non-native field multiply).**
/// `NonNative.lean`'s `mul_mod_via_Fr_limbwise_constraints_3` proves the 3-limb
/// 86-bit modular-product constraints sound (`c = a·b mod m`). Pins the
/// `mod_mul` / `fp_mul` gadget's constraint shape.
#[test]
fn fp_mul_matches_lean_model() {
    let c = xark_test_harness::compile_file(&example("fp_mul"), "fp_mul_lean_bridge", "bn254");
    assert!(c.status_success, "fp_mul compiles: {}", c.stderr);
    // Mult-gate count, streamed from `circuit.xbc` (no r1cs.json materialization).
    let mul = c.mul_gate_count();
    assert_eq!(
        mul, 1154,
        "fp_mul mult-gate count pins mul_mod_via_Fr_limbwise_constraints_3; got {mul}"
    );
}

/// **R1CS ↔ Lean bridge (secp256k1 incomplete point-add).**
/// `Secp256k1.lean`'s `ec_add_incomplete_secp256k1_sound` proves the flag-free
/// 3-limb chord addition sound (output on `y²=x³+7`, slope unique) from the
/// generic `Curve` algebra. Pins the `ec_add_incomplete` gadget's shape.
#[test]
fn ec_incomplete_matches_lean_model() {
    let c = xark_test_harness::compile_file(
        &example("ec_incomplete"),
        "ec_incomplete_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "ec_incomplete compiles: {}", c.stderr);
    // Mult-gate count, streamed from `circuit.xbc` (no r1cs.json materialization).
    let mul = c.mul_gate_count();
    // 15369 − 9. Squaring a 3-limb element (`y²`, `λ²`, the
    // on-curve check) forms each cross product `xᵢ·xⱼ` twice in the schoolbook
    // column sums; the second reuses the first's row (`Xark.R1cs.cse_sound`), so
    // every column sum — what `mul_mod_via_limbwise_constraints` is stated over —
    // has the same value.
    let want = 15360;
    assert_eq!(
        mul, want,
        "ec_incomplete mult-gate count pins ec_add_incomplete_secp256k1_sound; got {mul}"
    );
}

/// **R1CS ↔ Lean bridge (secp256r1/P-256 incomplete point-add).**
/// `Secp256r1.lean`'s `ec_add_incomplete_secp256r1_sound` (same shape at `a=−3`).
#[test]
fn ec_incomplete_r1_matches_lean_model() {
    let c = xark_test_harness::compile_file(
        &example("ec_incomplete_r1"),
        "ec_incomplete_r1_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "ec_incomplete_r1 compiles: {}", c.stderr);
    // Mult-gate count, streamed from `circuit.xbc` (no r1cs.json materialization).
    let mul = c.mul_gate_count();
    // 15891 − 9 (the 3-limb square's repeated cross products; see
    // `ec_incomplete_matches_lean_model`).
    let want = 15882;
    assert_eq!(
        mul, want,
        "ec_incomplete_r1 mult-gate count pins ec_add_incomplete_secp256r1_sound; got {mul}"
    );
}

/// **Struct support.** A `Point { x: [Field; 3], y: [Field; 3] }` circuit —
/// struct construction, field access `p.x[i]`, and passing the struct through a
/// helper — lowers to the same R1CS as the bare `[[Field; 3]; 2]` form
/// (structs are zero-cost). Guards the `AggregateKind::Adt` lowering.
#[test]
fn struct_point_lowers() {
    let c = compile(&example("struct_point"), "struct_point");
    assert!(c.status_success, "struct_point compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    // `x0*y0 = prod` (one multiplication) + `(x0 + y0 - sum) * 1 = 0` (one linear).
    assert_eq!(
        r1cs.constraints.len(),
        2,
        "struct_point lowers to 2 constraints"
    );
    let muls = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();
    assert_eq!(muls, 1, "one genuine multiplication gate (x0*y0)");
}

/// **`From<uN>` numeric constants.** `Field::from(2u8)` / `Field::from(1000u32)`
/// lower to in-circuit constants via the *private* `constant_u64` intrinsic —
/// the only public surface is `From`. Guards the trait-instance resolution
/// (`<Field as From<u8>>::from`) and the compile-time int-cast lowering.
#[test]
fn from_const_lowers() {
    let c = compile(&example("from_const"), "from_const");
    assert!(c.status_success, "from_const compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    // `2*a == doubled` and `a + BIG == plus_big` → two linear equalities.
    assert_eq!(r1cs.constraints.len(), 2, "from_const → 2 constraints");
    let circuit = std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap();
    assert!(
        circuit.contains("123456789012345678901234567890"),
        "the full-width `Field::from(u128)` constant landed without truncation"
    );
}

/// **`From<&str>` decimal constants.** `Field::from("21888…")` / `"…".into()`
/// route through the `constant` intrinsic — for full 254-bit constants beyond
/// `u128`. Guards the string-conversion path.
#[test]
fn from_str_const_lowers() {
    let src = write_case(
        "from_str",
        "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, b: Public<Field>) {\n\
         let big = Field::from(\"218882428718392752222464057452572750885483644004160343436982041865758084956\");\n\
         let two: Field = \"2\".into();\n\
         require_eq(a * two + big, b);\n}\n",
    );
    let c = compile(&src, "from_str");
    assert!(c.status_success, "from_str compiles: {}", c.stderr);
    let r1cs = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    assert!(
        r1cs.contains(
            "218882428718392752222464057452572750885483644004160343436982041865758084956"
        ),
        "the decimal-string constant landed"
    );
}

/// A `Field::from(&str)` with a non-numeric character is a **compile-time** error
/// that names the offending character.
#[test]
fn rejects_non_numeric_field_string() {
    let src = write_case(
        "bad_str",
        "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, b: Public<Field>) {\n\
         require_eq(a + Field::from(\"12a34\"), b);\n}\n",
    );
    let c = compile(&src, "reject_bad_str");
    assert!(!c.status_success);
    assert!(
        c.stderr.contains("non-numeric character 'a'")
            // Stable: the `const fn` parser's panic (no formatting in a const panic).
            || c.stderr.contains("non-numeric character"),
        "{}",
        c.stderr
    );
}

/// **Const-generic gadget support.** A function generic over `const N: usize` is
/// monomorphized per instantiation, with `N` const-folded in loop bounds and
/// `[Field; N]` local arrays (`Repeat`). Enabler for caller-chosen limb widths.
#[test]
fn const_generic_lowers() {
    let c = compile(&example("const_generic"), "const_generic");
    assert!(c.status_success, "const_generic compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    // `2(a+b+c) + 2(a+b) == out` folds to one linear equality.
    assert_eq!(r1cs.constraints.len(), 1, "const_generic → 1 constraint");
}

/// **`Bignum<LIMBS, BITS>` wrapper.** The zero-cost newtype's methods
/// (`a.mul(b, m, m1)`) forward to the free functions, so the emitted R1CS is
/// identical to calling `mod_mul::<3,86>` directly. Guards the classify fix
/// (an inherent `mul`/`add`/… must not be mistaken for the `Field` operator)
/// and const-generic struct-method inlining.
#[test]
fn bignum_wrapper_lowers() {
    let c = compile_with_field(&example("bignum"), "bignum", "bn254");
    assert!(c.status_success, "bignum wrapper compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    // Same as the free-fn `mod_mul::<3,86>` (a·b mod m, 3×86-bit) under bn254.
    assert_eq!(r1cs.constraints.len(), 1189, "Bignum::mul is zero-cost");
}

/// **`fp!` operator layer.** `xark_bignum::fp!` defines a non-native field-element
/// type from just its modulus, with `core::ops` (`+`/`-`/`*`/unary `-`) on it
/// (`a * b + a - b`). Guards that the operator methods (`<El as Mul>::mul` etc.)
/// are *not* mistaken for the `Field` intrinsics — they inline to the
/// width-generic free functions.
#[test]
fn bignum_ops_lowers() {
    let c = compile_with_field(&example("bignum_ops"), "bignum_ops", "bn254");
    assert!(c.status_success, "bignum_ops compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    assert!(
        r1cs.constraints.len() > 1000,
        "bignum_ops lowered the mul+add+sub"
    );
}

/// **`Field::to_bits` / `from_bits`.** Bit decomposition as a first-class `Field`
/// operation (const-generic bit count, composed from `hint_bit` + arithmetic +
/// `require_eq`). 8 merged booleanity checks + 2 recompositions = 10.
#[test]
fn to_bits_lowers() {
    let c = compile(&example("to_bits"), "to_bits");
    assert!(c.status_success, "to_bits compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    assert_eq!(r1cs.constraints.len(), 10, "8 booleanity + 2 recomposition");
}

/// **Const-fold `to_bits` — zero constraints.** Decomposing a *constant* has
/// known bits, so the `N` booleanity + 1 recomposition constraints are
/// tautologies and are dropped entirely. Here the only value that ever varies is
/// the public output, and the whole body reduces to a single linear `require_eq`
/// with no multiplication (booleanity) gates at all.
#[test]
fn const_to_bits_emits_no_booleanity() {
    let src = write_case(
        "const_to_bits",
        "#![no_std]\nuse xark::{require_eq, Field, Public};\n\
         pub fn circuit(out: Public<Field>) {\n\
           let bits = Field::from(5u8).to_bits::<8>();\n\
           require_eq(Field::from_bits::<8>(bits), out);\n\
         }\n",
    );
    let c = compile(&src, "const_to_bits");
    assert!(c.status_success, "const to_bits compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul_gates = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();
    assert_eq!(
        mul_gates, 0,
        "constant decomposition must emit no booleanity/mul gates"
    );
}

/// **Const-fold `to_bits` — overflow is a compile error.** A constant that does
/// not fit in `N` bits could never satisfy the recomposition (an `N`-bit sum
/// lives in `[0, 2ᴺ)`), so it was already unprovable; const-folding turns that
/// silent dead end into a clean compile-time rejection.
#[test]
fn const_to_bits_overflow_rejected() {
    let src = write_case(
        "const_to_bits_overflow",
        "#![no_std]\nuse xark::{require_eq, Field, Public};\n\
         pub fn circuit(out: Public<Field>) {\n\
           let bits = Field::from(300u16).to_bits::<8>();\n\
           require_eq(Field::from_bits::<8>(bits), out);\n\
         }\n",
    );
    let c = compile(&src, "const_to_bits_overflow");
    assert!(!c.status_success, "overflow must be rejected");
    assert!(c.stderr.contains("does not fit in 8 bits"), "{}", c.stderr);
}

/// **Poseidon2 sponge — lowering.** Variable-length `hash::<N>` (5 elements → 3
/// permutations) compiles cleanly.
#[test]
fn poseidon2_sponge_lowers() {
    let c = compile(&example("poseidon2_sponge"), "poseidon2_sponge");
    assert!(c.status_success, "poseidon2_sponge failed: {}", c.stderr);
}

/// **Poseidon2 sponge — correctness + soundness.** For one rate-2 chunk the
/// sponge is *defined* as `poseidon2_perm([a, b, N=2])[0]`; verify the wrapper
/// computes exactly that, solves, and leaves no under-constrained witness.
#[test]
fn poseidon2_sponge_matches_permutation() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = "#![no_std]\n\
        use xark::{require_eq, Field, Private};\n\
        use xark_poseidon2::{hash, poseidon2_perm};\n\
        pub fn circuit(a: Private<Field>, b: Private<Field>) {\n\
          require_eq(hash::<2>([a, b]), poseidon2_perm([a, b, Field::from(2u8)])[0]);\n\
        }\n";
    let path = std::env::temp_dir().join("xark_p2_sponge_id.rs");
    std::fs::write(&path, src).unwrap();
    let c = compile(&path, "poseidon2_sponge_id");
    assert!(c.status_success, "sponge id compile: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };
    let mut inputs = BTreeMap::new();
    inputs.insert(id("a"), "1".to_string());
    inputs.insert(id("b"), "2".to_string());
    let assign =
        solver::solve_and_check(&program, &inputs).expect("sponge must solve & match perm");
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(
        holes.is_empty(),
        "sponge under-constrained: {:?}",
        &holes[..holes.len().min(5)]
    );
}

/// **Poseidon sponge — lowering.**
#[test]
fn poseidon_sponge_lowers() {
    let c = compile(&example("poseidon_sponge"), "poseidon_sponge");
    assert!(c.status_success, "poseidon_sponge failed: {}", c.stderr);
}

/// **Poseidon sponge — correctness + soundness.** One rate-2 chunk is defined as
/// `permute([N=2, a, b])[0]` (capacity-first layout); verify the wrapper matches,
/// solves, and is fully constrained.
#[test]
fn poseidon_sponge_matches_permutation() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = "#![no_std]\n\
        use xark::{require_eq, Field, Private};\n\
        use xark_poseidon::{hash, permute};\n\
        pub fn circuit(a: Private<Field>, b: Private<Field>) {\n\
          require_eq(hash::<2>([a, b]), permute([Field::from(2u8), a, b])[0]);\n\
        }\n";
    let path = std::env::temp_dir().join("xark_p_sponge_id.rs");
    std::fs::write(&path, src).unwrap();
    let c = compile(&path, "poseidon_sponge_id");
    assert!(c.status_success, "poseidon sponge id compile: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };
    let mut inputs = BTreeMap::new();
    inputs.insert(id("a"), "7".to_string());
    inputs.insert(id("b"), "11".to_string());
    let assign = solver::solve_and_check(&program, &inputs).expect("poseidon sponge must solve");
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(
        holes.is_empty(),
        "poseidon sponge under-constrained: {:?}",
        &holes[..holes.len().min(5)]
    );
}

/// **Variable-length SHA-256 — real vector.** `sha256::<8>(0..8)` must equal real
/// `SHA-256`, solve, be fully constrained, and reject a wrong digest.
#[test]
#[ignore = "heavy: full multi-block hash circuit"]
fn sha256_varlen_matches_real_vector() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let c = compile(
        &write_case("sha256_varlen", &sha256_bytes_src(8)),
        "sha256_hash",
    );
    assert!(c.status_success, "sha256_varlen failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };
    let mut inputs = BTreeMap::new();
    for i in 0..8u32 {
        inputs.insert(id(&format!("msg[{i}]")), i.to_string());
    }
    let digest = [
        2323980280u32,
        786891914,
        3500065668,
        2132664132,
        2487289042,
        3419504372,
        3822789318,
        2019167557,
    ];
    for (i, w) in digest.iter().enumerate() {
        inputs.insert(id(&format!("d[{i}]")), w.to_string());
    }
    let assign =
        solver::solve_and_check(&program, &inputs).expect("sha256::<8> must match real SHA-256");
    assert!(
        solver::analyze_underconstrained(&program, &assign).is_empty(),
        "sha256 under-constrained"
    );
    inputs.insert(id("d[0]"), "42".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "wrong digest must reject"
    );
}

/// **`Digest` ergonomics POC — KAT-validated.** Compiles the `sha256_consume`
/// example (the 3-line "hash bytes, then require the digest equals a known value"
/// form): its body bakes in `sha256("abc")` as a `const [u8; 32]` and pins it to
/// `Digest::from(sha256(msg))`. Solving with `msg = [97, 98, 99]` (`"abc"`) is
/// the proof the `From<[u8; 32]>` word/byte/bit ordering matches the gadget: if
/// the layout were off, the real KAT would not satisfy the constraints. A wrong
/// first byte must be rejected, and no derived var may be under-constrained.
#[test]
#[ignore = "heavy: full padded SHA-256 circuit (~15s compile)"]
fn digest_consume_matches_abc_vector() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let c = compile(&example("sha256_consume"), "sha256_consume");
    assert!(c.status_success, "sha256_consume failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };
    // The expected digest is a compile-time constant, so the only inputs are the
    // 3 private message bytes.
    let mut inputs = BTreeMap::new();
    inputs.insert(id("msg[0]"), "97".to_string()); // 'a'
    inputs.insert(id("msg[1]"), "98".to_string()); // 'b'
    inputs.insert(id("msg[2]"), "99".to_string()); // 'c'

    // KAT: sha256("abc") == baked-in constant ⇒ every constraint holds. This
    // passing IS the proof the `From<[u8; 32]>` endianness/ordering is correct.
    let assign = solver::solve_and_check(&program, &inputs)
        .expect("sha256(\"abc\") must match the baked-in Digest constant");
    assert!(
        solver::analyze_underconstrained(&program, &assign).is_empty(),
        "sha256_consume under-constrained"
    );

    // Negative control: a different preimage cannot hash to sha256("abc").
    inputs.insert(id("msg[0]"), "65".to_string()); // 'A' ≠ 'a'
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "wrong preimage must be rejected"
    );
}

/// **Variable-length BLAKE2s — real vector.** `blake2s::<100>(0..100)` (2 blocks)
/// must equal real `hashlib.blake2s`, solve, be fully constrained, reject wrong.
#[test]
#[ignore = "heavy: full multi-block hash circuit"]
fn blake2s_varlen_matches_real_vector() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let c = compile(
        &write_case("blake2s_varlen", &blake2s_bytes_src(100)),
        "blake2s_hash",
    );
    assert!(c.status_success, "blake2s_varlen failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };
    let mut inputs = BTreeMap::new();
    for i in 0..100u32 {
        inputs.insert(id(&format!("msg[{i}]")), i.to_string());
    }
    let digest = [
        2781076609u32,
        1070524933,
        1888460167,
        259487271,
        1376712093,
        2821198877,
        4177833821,
        3763347885,
    ];
    for (i, w) in digest.iter().enumerate() {
        inputs.insert(id(&format!("d[{i}]")), w.to_string());
    }
    let assign =
        solver::solve_and_check(&program, &inputs).expect("blake2s::<100> must match real BLAKE2s");
    assert!(
        solver::analyze_underconstrained(&program, &assign).is_empty(),
        "blake2s under-constrained"
    );
    inputs.insert(id("d[0]"), "42".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "wrong digest must reject"
    );
}

/// **Variable-length BLAKE3 — real vector.** `blake3::<100>(0..100)` (single chunk,
/// 2 blocks) must equal real BLAKE3, solve, be fully constrained, reject wrong.
#[test]
#[ignore = "heavy: full multi-block hash circuit"]
fn blake3_varlen_matches_real_vector() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let c = compile(
        &write_case("blake3_varlen", &blake3_bytes_src(100)),
        "blake3_hash",
    );
    assert!(c.status_success, "blake3_varlen failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };
    let mut inputs = BTreeMap::new();
    for i in 0..100u32 {
        inputs.insert(id(&format!("msg[{i}]")), i.to_string());
    }
    let digest = [
        3148951182u32,
        2399863971,
        1074928225,
        3339837856,
        3385804107,
        3104894410,
        3681706847,
        3048751132,
    ];
    for (i, w) in digest.iter().enumerate() {
        inputs.insert(id(&format!("d[{i}]")), w.to_string());
    }
    let assign =
        solver::solve_and_check(&program, &inputs).expect("blake3::<100> must match real BLAKE3");
    assert!(
        solver::analyze_underconstrained(&program, &assign).is_empty(),
        "blake3 under-constrained"
    );
    inputs.insert(id("d[0]"), "42".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "wrong digest must reject"
    );
}

/// A multiplication result reused across two `require_eq`s stays bound to `a*b`
/// in both (the product is revived after the merge).
#[test]
fn mul_reuse_binds_product_in_both_asserts() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};

    let c = compile_with_field(&example("mul_reuse"), "mul_reuse", "bn254");
    assert!(c.status_success, "mul_reuse failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap();
    let program = primitive::from_json(&json).unwrap();
    let id = |name: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == name)
            .map(|v| v.id)
            .unwrap()
    };

    // honest: a*b = c = d (3*4 = 12)
    let mut inputs = BTreeMap::new();
    inputs.insert(id("a"), "3".to_string());
    inputs.insert(id("b"), "4".to_string());
    inputs.insert(id("c"), "12".to_string());
    inputs.insert(id("d"), "12".to_string());
    let assign = solver::solve_and_check(&program, &inputs).expect("a*b == c == d must verify");
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "mul_reuse under-constrained: {holes:?}");

    // c != d must be rejected (product bound to both asserts)
    inputs.insert(id("d"), "13".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "c != d must be rejected"
    );
}

/// Field division (`/`) lowers to an inverse-pinned multiplication and solves.
#[test]
fn field_div_solves() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "field_div",
        "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>, q: Public<Field>) {\n\
         \x20   require_eq(a / b, q);\n\
         }\n",
    );
    let c = compile_with_field(&src, "field_div", "bn254");
    assert!(c.status_success, "field_div failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };
    let mut inputs = BTreeMap::new();
    inputs.insert(id("a"), "6".to_string());
    inputs.insert(id("b"), "3".to_string());
    inputs.insert(id("q"), "2".to_string()); // 6 / 3 == 2
    let assign = solver::solve_and_check(&program, &inputs).expect("a/b == q must verify");
    assert!(
        solver::analyze_underconstrained(&program, &assign).is_empty(),
        "field_div under-constrained"
    );
    inputs.insert(id("q"), "3".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "wrong quotient must reject"
    );
}

/// Compound assignment (`+=`, `Field: AddAssign`) works in a circuit.
#[test]
fn compound_assign() {
    let src = write_case(
        "field_assign_ok",
        "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, b: Public<Field>, c: Public<Field>) {\n\
         \x20   let mut acc = a;\n\
         \x20   acc += b;\n\
         \x20   require_eq(acc, c);\n\
         }\n",
    );
    let c = compile_with_field(&src, "field_assign_ok", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    assert!(accepts(&c, &[("a", "2"), ("b", "3"), ("c", "5")]));
    assert!(!accepts(&c, &[("a", "2"), ("b", "3"), ("c", "6")]));
}

/// `==` on `Field` is a circuit operation (yields a `bool` wire); a branch on it makes
/// the arm's `require` conditional.
#[test]
fn branch_on_field_comparison() {
    let src = write_case(
        "field_cmp",
        "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, b: Public<Field>) {\n\
         \x20   if a == b { require_eq(a, b); }\n\
         }\n",
    );
    let c = compile_with_field(&src, "field_cmp_ok", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    assert!(accepts(&c, &[("a", "3"), ("b", "3")]));
    assert!(accepts(&c, &[("a", "3"), ("b", "4")]));
}

/// `assert!`, `require_eq` and integer division inside a witness
/// branch bind only when the arm is taken (nested arms too); a division by zero in
/// an untaken arm is fine.
#[test]
fn conditional_requires() {
    let src = write_case(
        "cond_req",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(mode: Private<u8>, a: Private<u32>, b: Private<u32>, x: Private<Field>, out: Public<Field>) {\n\
         \x20   if mode == 1 { assert!(a < b); }\n\
         \x20   if mode == 2 { require_eq(x, Field::from(a)); }\n\
         \x20   if mode >= 4 { if a > b { require_eq(x, Field::from(b)); } }\n\
         \x20   let q = if mode == 3 { a / b } else { a };\n\
         \x20   require_eq(Field::from(q), out);\n\
         }\n",
    );
    let c = compile_with_field(&src, "cond_req", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let case = |mode: &str, a: &str, b: &str, x: &str, out: &str| {
        accepts_exactly(
            &c,
            &[("mode", mode), ("a", a), ("b", b), ("x", x), ("out", out)],
        )
    };
    assert!(case("0", "5", "0", "9", "5"));
    assert!(case("1", "3", "5", "9", "3"));
    assert!(!case("1", "5", "3", "9", "5"));
    assert!(case("2", "7", "0", "7", "7"));
    assert!(!case("2", "7", "0", "8", "7"));
    assert!(case("3", "7", "2", "0", "3"));
    assert!(!case("3", "7", "2", "0", "7"));
    assert!(!case("3", "7", "0", "0", "7"));
    assert!(case("4", "5", "3", "3", "5"));
    assert!(!case("4", "5", "3", "4", "5"));
    assert!(case("4", "1", "3", "4", "1"));
}

/// **Row-level soundness of the curve gadgets, at small scale.** The same
/// `weierstrass!` gadget code as secp256k1 (`y² = x³ + 7`, `ca = 0`) and secp256r1
/// (`y² = x³ − 3x + b`, `ca = −3`: its own doubling numerator and on-curve term),
/// instantiated over 3 × `bits` limbs and a prime `p` (`fp!` requires `3·p < 2^(3·bits)`), compiled by the same
/// frontend. With the input points fixed and the output left free, exhaustive witness
/// search proves every satisfying witness yields the same output, equal to the native
/// affine sum or double — and that there is none where the formula is undefined
/// (`x₁ = x₂`, `y = 0`). Internal freedom is allowed (the inverse isn't canonical by
/// design); the output is what's pinned. `checked_add` runs `enforce_on_curve` on both
/// inputs first, over *every* limb encoding of each coordinate: an encoding `≥ p`
/// must be rejected outright. `scaled_curve_gadget_rows_match_secp256k1` ties the rows
/// to the 86-bit circuit.
fn toy_curve_source(bits: u32, p: u64, ca: i128, op: &str) -> String {
    // `b = 7` and dummy generator tables (only the scalar-mul code reads them).
    let mask = (1u64 << bits) - 1;
    let limbs = |v: u64| [v & mask, (v >> bits) & mask, (v >> (2 * bits)) & mask];
    let b = limbs(7 % p);
    let body = match op {
        "add" => "let r = ec_add_incomplete(p, q);",
        "checked_add" => {
            "enforce_on_curve(p); enforce_on_curve(q); let r = ec_add_incomplete(p, q);"
        }
        _ => "let _ = q; let r = ec_double_incomplete(p);",
    };
    format!(
        "#![no_std]\nuse xark::prelude::*;\n\
         mod toy {{ xark_curve::weierstrass! {{ bits = {bits}, base = \"{p}\", scalar = \"{p}\", a = {ca}, \
         b = [{}, {}, {}], generators = [[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0]], \
         correction = [0,0,0,0,0,0] }} }}\n\
         use toy::{{ec_add_incomplete, ec_double_incomplete, enforce_on_curve, Point}};\n\
         #[circuit]\n\
         pub fn circuit(p: Private<Point>, q: Private<Point>, s: Public<Point>) {{\n\
         \x20   {body}\n\
         \x20   let mut i = 0;\n\
         \x20   while i < 3 {{ require_eq(r.x.limbs[i], s.x.limbs[i]); require_eq(r.y.limbs[i], s.y.limbs[i]); i += 1; }}\n\
         }}\n",
        b[0], b[1], b[2]
    )
}

/// Affine `y² = x³ + ca·x + 7` over `p`: `None` where the incomplete formula is
/// undefined.
fn toy_ec(
    p: i128,
    ca: i128,
    a: (i128, i128),
    b: (i128, i128),
    double: bool,
) -> Option<(i128, i128)> {
    let inv = |x: i128| -> Option<i128> {
        let x = x.rem_euclid(p);
        (x != 0).then(|| (1..p).find(|y| x * y % p == 1).expect("p prime"))
    };
    let lam = if double {
        (3 * a.0 * a.0 + ca).rem_euclid(p) * inv(2 * a.1)? % p
    } else {
        (b.1 - a.1).rem_euclid(p) * inv(b.0 - a.0)? % p
    };
    let x3 = (lam * lam - a.0 - if double { a.0 } else { b.0 }).rem_euclid(p);
    let y3 = (lam * (a.0 - x3) - a.1).rem_euclid(p);
    Some((x3, y3))
}

/// `op` on the toy curve over `p` for each `(P, Q)` in `pairs` (encodings included),
/// each decided by projection search against [`toy_ec`].
/// A pair of toy-curve points `(P, Q)`, as `(x, y)` coordinates.
type ToyPair = ((i128, i128), (i128, i128));

fn check_toy_curve(bits: u32, p: i128, ca: i128, op: &str, pairs: &[ToyPair]) {
    use xark_ir::witness_search::{Projection, search_projection};
    let name = format!("toy_ec_{op}_{p}_a{}", ca.unsigned_abs());
    let src = write_case(&name, &toy_curve_source(bits, p as u64, ca, op));
    let c = compile_with_field(&src, &name, "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let prog = c.program();
    let id = |n: &str| {
        prog.vars
            .iter()
            .find(|v| v.name == n)
            .unwrap_or_else(|| panic!("no leaf `{n}`"))
            .id
    };
    let leaf = |pt: &str, co: &str, i: usize| id(&format!("{pt}.{co}.limbs[{i}]"));
    let out: Vec<_> = ["x", "y"]
        .iter()
        .flat_map(|co| (0..3).map(move |i| (co, i)))
        .map(|(co, i)| leaf("s", co, i))
        .collect();
    let mask = (1i128 << bits) - 1;
    let (mut defined, mut undefined, mut noncanonical) = (0, 0, 0);
    for &(a, b) in pairs {
        let mut fixed = std::collections::BTreeMap::new();
        for (pt, v) in [("p", a), ("q", b)] {
            for (co, val) in [("x", v.0), ("y", v.1)] {
                for i in 0..3 {
                    fixed.insert(
                        leaf(pt, co, i),
                        ((val >> (bits * i as u32)) & mask).to_string(),
                    );
                }
            }
        }
        let got = search_projection(&prog, &fixed, &out, 1 << 14, None).unwrap();
        let canonical = [a.0, a.1, b.0, b.1].iter().all(|&v| v < p);
        let reduce = |v: (i128, i128)| (v.0 % p, v.1 % p);
        let want = if canonical {
            toy_ec(p, ca, a, b, op == "double")
        } else {
            None
        };
        match (want, got) {
            (Some((x3, y3)), Projection::One(v)) => {
                let limb = |k: usize| v[k].to_decimal().parse::<i128>().unwrap();
                let val = |o: usize| {
                    (0..3)
                        .map(|i| limb(o + i) << (bits * i as u32))
                        .sum::<i128>()
                };
                assert_eq!((val(0), val(3)), (x3, y3), "{op} {a:?} {b:?}");
                defined += 1;
            }
            (None, Projection::None) if canonical => undefined += 1,
            (None, Projection::None) => noncanonical += 1,
            (want, other) => panic!(
                "{op} p={p} {a:?} {b:?} (≡ {:?} {:?}): expected {want:?}, circuit {other:?}",
                reduce(a),
                reduce(b)
            ),
        }
    }
    eprintln!(
        "p = {p}, a = {ca}, {op}: {defined} defined, {undefined} undefined, {noncanonical} non-canonical rejected"
    );
    assert!(defined > 0);
}

fn toy_points(p: i128, ca: i128) -> Vec<(i128, i128)> {
    (0..p)
        .flat_map(|x| (0..p).map(move |y| (x, y)))
        .filter(|&(x, y)| (y * y - (x * x * x + ca * x + 7)).rem_euclid(p) == 0)
        .collect()
}

fn all_pairs(pts: &[(i128, i128)]) -> Vec<ToyPair> {
    pts.iter()
        .flat_map(|&a| pts.iter().map(move |&b| (a, b)))
        .collect()
}

#[test]
fn small_field_curve_gadgets_are_sound() {
    // Both curve shapes the gadgets support: `a = 0` (secp256k1) and `a = −3`
    // (secp256r1). `y² = x³ − 3x + 7` is non-singular mod 13 and 127.
    for ca in [0, -3] {
        // p = 13 (3 × 2-bit limbs): every pair, and for the checked entry every encoding.
        let pts = toy_points(13, ca);
        check_toy_curve(2, 13, ca, "add", &all_pairs(&pts));
        let doubles: Vec<_> = pts.iter().map(|&a| (a, (0, 0))).collect();
        check_toy_curve(2, 13, ca, "double", &doubles);
        let encs = |v: i128| (0..).map(move |k| v + 13 * k).take_while(|&e| e < 64);
        let mut every: Vec<_> = Vec::new();
        // Every pair for `a = 0`; for `a = −3` (169 pairs) every 5th, still with
        // every encoding of each, to keep the per-push suite quick.
        let step = if ca == 0 { 1 } else { 5 };
        for (a, b) in all_pairs(&pts).into_iter().step_by(step) {
            for ax in encs(a.0) {
                for ay in encs(a.1) {
                    for bx in encs(b.0) {
                        for by in encs(b.1) {
                            every.push(((ax, ay), (bx, by)));
                        }
                    }
                }
            }
        }
        check_toy_curve(2, 13, ca, "checked_add", &every);
        // p = 127 (3 × 3-bit limbs): every double, and a fixed sample of the adds
        // (for `a = −3`, every 3rd double and a sparser sample: p = 13 above is
        // the exhaustive case).
        let pts = toy_points(127, ca);
        let (dstep, astep) = if ca == 0 { (1, 53) } else { (3, 159) };
        let doubles: Vec<_> = pts.iter().step_by(dstep).map(|&a| (a, (0, 0))).collect();
        check_toy_curve(3, 127, ca, "double", &doubles);
        let sample: Vec<_> = all_pairs(&pts).into_iter().step_by(astep).collect();
        check_toy_curve(3, 127, ca, "add", &sample);
    }
}

/// One generic `xark_bignum` gadget for [`small_field_bignum_gadgets_are_sound`]: its
/// call (on limb arrays `a`, `b`, `c`, yielding `(r, q)`), arity, reference result
/// (`None` = no witness expected) and documented precondition.
struct BignumCase {
    name: &'static str,
    call: &'static str,
    arity: usize,
    two_out: bool,
    spec: fn(&[i128]) -> Option<[i128; 2]>,
    pre: fn(&[i128]) -> bool,
}

/// **Every generic bignum gadget, on every limb encoding.** `mod_add`, `mod_sub`,
/// `mod_neg`, `triple_mod`, `reduce_once`, `require_lt`, `is_lt`,
/// `assert_nonzero_limbs`, `mod_mul`, `mul_divmod`, `mod_inverse`, `sub2` over 3 × 2-bit
/// limbs mod 13, each input any value `< 2⁶` (so non-canonical ones too), outputs left
/// free and decided by projection search. Within a gadget's precondition the output is
/// exactly the reference (canonical); outside it the output must still be `≡` the
/// reference or there must be no witness — never a wrong value, never two values.
/// (This is what caught `mod_add` wrapping an overflowing sum and `mod_neg(0) = m`.)
///
/// Blind spot: at 3 × 2 bits every recomposition is far below Fr, so a check that is
/// only wrong when a full-width value wraps the field can't show up here — that class
/// is tested at full width (`mod_neg_full_width`, `lazy_field_gadgets_are_sound`).
#[test]
fn small_field_bignum_gadgets_are_sound() {
    use xark_ir::witness_search::{Projection, search_projection};
    const M: i128 = 13;
    let cases = [
        BignumCase {
            name: "mod_add",
            call: "(mod_add::<3, 2>(a, b, MM), Z)",
            arity: 2,
            two_out: false,
            spec: |v| Some([(v[0] + v[1]) % M, 0]),
            pre: |v| v[0] < M && v[1] < M,
        },
        BignumCase {
            name: "mod_sub",
            call: "(mod_sub::<3, 2>(a, b, CC), Z)",
            arity: 2,
            two_out: false,
            spec: |v| Some([(v[0] - v[1]).rem_euclid(M), 0]),
            pre: |v| v[0] < M && v[1] < M,
        },
        BignumCase {
            name: "mod_neg",
            call: "(mod_neg::<3, 2>(a, MM), Z)",
            arity: 1,
            two_out: false,
            spec: |v| (v[0] <= M).then(|| [(M - v[0]) % M, 0]),
            pre: |v| v[0] < M,
        },
        BignumCase {
            name: "triple_mod",
            call: "(triple_mod::<3, 2>(a, MM), Z)",
            arity: 1,
            two_out: false,
            spec: |v| Some([(3 * v[0]) % M, 0]),
            pre: |v| v[0] < M,
        },
        BignumCase {
            name: "reduce_once",
            call: "(reduce_once::<3, 2>(a, MM), Z)",
            arity: 1,
            two_out: false,
            spec: |v| Some([v[0] % M, 0]),
            pre: |v| v[0] < 2 * M,
        },
        BignumCase {
            name: "require_lt",
            call: "{ xark_bignum::require_lt::<3, 2>(a, M1); (Z, Z) }",
            arity: 1,
            two_out: false,
            spec: |v| (v[0] < M).then_some([0, 0]),
            pre: |_| true,
        },
        BignumCase {
            name: "is_lt",
            call: "([is_lt::<3, 2>(a, b), Field::from(0u8), Field::from(0u8)], Z)",
            arity: 2,
            two_out: false,
            spec: |v| Some([(v[0] < v[1]) as i128, 0]),
            pre: |_| true,
        },
        BignumCase {
            name: "assert_nonzero_limbs",
            call: "{ assert_nonzero_limbs::<3>(a); (Z, Z) }",
            arity: 1,
            two_out: false,
            spec: |v| (v[0] != 0).then_some([0, 0]),
            pre: |_| true,
        },
        BignumCase {
            name: "mod_mul",
            call: "(mod_mul::<3, 2>(a, b, MM, M1), Z)",
            arity: 2,
            two_out: false,
            spec: |v| Some([(v[0] * v[1]) % M, 0]),
            pre: |v| v[0] < M && v[1] < M,
        },
        BignumCase {
            name: "mul_divmod",
            call: "{ let (q, r) = mul_divmod::<3, 2>(a, b, MM, M1); (r, q) }",
            arity: 2,
            two_out: true,
            spec: |v| Some([v[0] * v[1] % M, v[0] * v[1] / M]),
            pre: |v| v[0] < M && v[1] < M,
        },
        BignumCase {
            name: "mod_inverse",
            call: "(mod_mul::<3, 2>(mod_inverse::<3, 2>(a, MM), [Field::from(1u8), Field::from(0u8), Field::from(0u8)], MM, M1), Z)",
            arity: 1,
            two_out: false,
            spec: |v| (v[0] % M != 0).then(|| [(1..M).find(|y| v[0] % M * y % M == 1).unwrap(), 0]),
            pre: |_| true,
        },
        BignumCase {
            name: "sub2",
            call: "(sub2::<3, 2>(a, b, c, MM, M1), Z)",
            arity: 3,
            two_out: false,
            spec: |v| Some([(v[0] - v[1] - v[2]).rem_euclid(M), 0]),
            pre: |v| v[0] < M && v[1] < M && v[2] < M,
        },
    ];
    for g in &cases {
        let src = format!(
            "#![no_std]\nuse xark::prelude::*;\nuse xark_bignum::*;\n\
             const MM: [Field; 3] = modulus_limbs::<3, 2>(\"13\");\n\
             const M1: [Field; 3] = modulus_minus_1::<3, 2>(\"13\");\n\
             const CC: [Field; 3] = complement::<3, 2>(\"13\");\n\
             const Z: [Field; 3] = [Field::zero(), Field::zero(), Field::zero()];\n\
             #[circuit]\n\
             pub fn circuit(a: Private<Bignum<3, 2>>, b: Private<Bignum<3, 2>>, c: Private<Bignum<3, 2>>, \
             s: Public<Bignum<3, 2>>, t: Public<Bignum<3, 2>>) {{\n\
             \x20   let (a, b, c) = (a.limbs, b.limbs, c.limbs);\n\
             \x20   let _ = (b, c, MM, M1, CC);\n\
             \x20   let (r, q): ([Field; 3], [Field; 3]) = {};\n\
             \x20   let mut i = 0;\n\
             \x20   while i < 3 {{ require_eq(r[i], s.limbs[i]); require_eq(q[i], t.limbs[i]); i += 1; }}\n\
             }}\n",
            g.call
        );
        let name = format!("bignum_small_{}", g.name);
        let c = compile_with_field(&write_case(&name, &src), &name, "bn254");
        assert!(c.status_success, "{}: {}", g.name, c.stderr);
        let prog = c.program();
        let id = |n: &str| prog.vars.iter().find(|v| v.name == n).map(|v| v.id);
        let proj: Vec<_> = ["s", "t"]
            .iter()
            .flat_map(|o| (0..3).map(move |i| format!("{o}.limbs[{i}]")))
            .filter_map(|n| id(&n))
            .collect();
        let mut inputs: Vec<Vec<i128>> = vec![vec![]];
        for k in 0..g.arity {
            // the third operand (`sub2`'s `c`) over a sample, to keep the run short
            let dom: Vec<i128> = if k == 2 {
                vec![0, 1, 12, 13, 40, 63]
            } else {
                (0..64).collect()
            };
            inputs = inputs
                .into_iter()
                .flat_map(|v| dom.iter().map(move |&x| [v.clone(), vec![x]].concat()))
                .collect();
        }
        let (mut exact, mut outside) = (0usize, 0usize);
        for v in inputs {
            let mut fixed = std::collections::BTreeMap::new();
            for (k, nm) in ["a", "b", "c"].iter().enumerate() {
                for i in 0..3 {
                    if let Some(var) = id(&format!("{nm}.limbs[{i}]")) {
                        let x = v.get(k).copied().unwrap_or(0);
                        fixed.insert(var, ((x >> (2 * i)) & 3).to_string());
                    }
                }
            }
            let got = search_projection(&prog, &fixed, &proj, 1 << 14, None).unwrap();
            let val = |vals: &[xark_ir::solver::Fp], o: usize| {
                (0..3)
                    .map(|i| vals[o + i].to_decimal().parse::<i128>().unwrap() << (2 * i))
                    .sum::<i128>()
            };
            let want = (g.spec)(&v);
            if (g.pre)(&v) {
                match (want, &got) {
                    (Some(w), Projection::One(vals)) => assert!(
                        val(vals, 0) == w[0] && (!g.two_out || val(vals, 3) == w[1]),
                        "{} {v:?}: want {w:?}, got {got:?}",
                        g.name
                    ),
                    (None, Projection::None) => {}
                    _ => panic!("{} {v:?}: want {want:?}, got {got:?}", g.name),
                }
                exact += 1;
            } else {
                match (want, &got) {
                    (_, Projection::None) => {}
                    (Some(w), Projection::One(vals)) => assert!(
                        val(vals, 0) % M == w[0] && (!g.two_out || val(vals, 3) == w[1]),
                        "{} {v:?} (outside its precondition): wrong value {got:?}, want ≡ {w:?}",
                        g.name
                    ),
                    _ => panic!("{} {v:?} (outside its precondition): {got:?}", g.name),
                }
                outside += 1;
            }
        }
        eprintln!(
            "{}: {exact} within the precondition exact, {outside} outside safe",
            g.name
        );
    }
}

/// **The fixed-width lazy gadgets, at full size.** `mul_lazy_k1`, `weak_reduce_k1`,
/// `finalize_k1` and their ed25519 counterparts hint no quotient (every carry is
/// determined), so exhaustive witness search decides them directly. On random,
/// all-zero and all-max limbs at their documented input bound — and one bit past
/// it — every output is `≡` the reference mod `p` and unique, or there is no
/// witness; within the bound the multiply and weak reduce always succeed.
#[test]
fn lazy_field_gadgets_are_sound() {
    use num_bigint::BigInt;
    use xark_ir::witness_search::{Projection, search_projection};
    let pk1 = BigInt::parse_bytes(
        b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
        16,
    )
    .unwrap();
    let p25: BigInt = (BigInt::from(1) << 255) - 19;
    // (gadget call, limbs, limb width, documented input bound in bits, modulus, binary,
    //  always succeeds within the bound)
    let cases: [(&str, usize, u32, u32, &BigInt, bool, bool); 6] = [
        ("mul_lazy_k1(a, b)", 4, 64, 70, &pk1, true, true),
        ("weak_reduce_k1(a)", 4, 64, 72, &pk1, false, true),
        ("finalize_k1(a)", 4, 64, 64, &pk1, false, false),
        ("mul_lazy_25519(a, b)", 3, 85, 88, &p25, true, true),
        ("weak_reduce_25519(a)", 3, 85, 88, &p25, false, true),
        ("finalize_25519(a)", 3, 85, 85, &p25, false, false),
    ];
    let value = |ls: &[BigInt], w: u32| {
        ls.iter().enumerate().fold(BigInt::from(0), |acc, (i, l)| {
            acc + (l.clone() << (w * i as u32))
        })
    };
    for (k, &(call, n, w, bound, p, binary, total)) in cases.iter().enumerate() {
        let src = format!(
            "#![no_std]\nuse xark::prelude::*;\nuse xark_bignum::*;\n#[circuit]\n\
             pub fn circuit(a: Private<[Field; {n}]>, b: Private<[Field; {n}]>, s: Public<[Field; {n}]>) {{\n\
             \x20   let _ = b;\n\x20   let r = {call};\n\
             \x20   let mut i = 0;\n\x20   while i < {n} {{ require_eq(r[i], s[i]); i += 1; }}\n}}\n"
        );
        let name = format!("lazy_gadget_{k}");
        let c = compile_with_field(&write_case(&name, &src), &name, "bn254");
        assert!(c.status_success, "{call}: {}", c.stderr);
        let prog = c.program();
        let id = |nm: &str| prog.vars.iter().find(|v| v.name == nm).map(|v| v.id);
        let out: Vec<_> = (0..n).filter_map(|i| id(&format!("s[{i}]"))).collect();
        let mut seed = 0x9e37_79b9_7f4a_7c15u64 ^ k as u64;
        let mut next = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let (mut decided, mut beyond) = (0usize, 0usize);
        for t in 0..48usize {
            let mut limb = |j: usize| -> BigInt {
                let max: BigInt = (BigInt::from(1) << bound) - 1;
                match (t + j) % 6 {
                    0 => BigInt::from(0),
                    1 => max,
                    r => {
                        let x = (BigInt::from(next()) | (BigInt::from(next()) << 64)) & max;
                        // one bit past the bound: always set, so it really exceeds it
                        if r == 5 {
                            x | (BigInt::from(1) << bound)
                        } else {
                            x
                        }
                    }
                }
            };
            let a: Vec<BigInt> = (0..n).map(&mut limb).collect();
            let b: Vec<BigInt> = (0..n).map(|j| limb(j + 3)).collect();
            let within = a
                .iter()
                .chain(if binary { &b[..] } else { &[] })
                .all(|l| l.bits() <= bound as u64);
            let mut fixed = std::collections::BTreeMap::new();
            for i in 0..n {
                fixed.insert(id(&format!("a[{i}]")).unwrap(), a[i].to_string());
                if let Some(v) = id(&format!("b[{i}]")) {
                    fixed.insert(v, b[i].to_string());
                }
            }
            let want = if binary {
                value(&a, w) * value(&b, w)
            } else {
                value(&a, w)
            } % p;
            match search_projection(&prog, &fixed, &out, 1 << 12, None).unwrap() {
                Projection::One(v) => {
                    let ls: Vec<BigInt> =
                        v.iter().map(|x| x.to_decimal().parse().unwrap()).collect();
                    assert_eq!(value(&ls, w) % p, want, "{call} {a:?} {b:?}: wrong value");
                    decided += 1;
                    beyond += !within as usize;
                }
                Projection::None => assert!(
                    !(within && total),
                    "{call} {a:?} {b:?}: rejected within its bound"
                ),
                other => panic!("{call} {a:?} {b:?}: {other:?}"),
            }
        }
        // Not vacuous: most samples are computed, not just rejected.
        assert!(
            decided >= 24,
            "{call}: only {decided}/48 samples gave a value"
        );
        println!("{call}: {decided}/48 exact ({beyond} past the bound)");
    }
}

/// Two shapes the frontend used to refuse, decided by witness search against Rust:
/// a table index LLVM narrowed using an earlier overflow check (`1 − x` can't
/// underflow, so `x ≤ 1`, so `x & 7` is `x` — the bound is learned from that check,
/// and the 64-bit pointer needs no truncation), and a store through a select of two
/// witness pointers.
#[test]
fn narrowed_index_and_nested_pointer_store() {
    let run = |name: &str, body: &str, ty: &str, cases: &[(u64, Option<u64>)]| {
        let src = format!(
            "#![no_std]\n#![allow(arithmetic_overflow)]\nuse xark::prelude::*;\n\
             pub fn circuit(x0: Private<{ty}>, out: Public<Field>) {{\n{body}\n}}\n"
        );
        let c = compile_with_field(&write_case(name, &src), name, "bn254");
        assert!(c.status_success, "{name}: {}", c.stderr);
        for &(x, want) in cases {
            let w = want.unwrap_or(0);
            for out in [w, w + 1] {
                let accepted =
                    accepts_exactly(&c, &[("x0", &x.to_string()), ("out", &out.to_string())]);
                assert_eq!(accepted, want == Some(out), "{name} x0={x} out={out}");
            }
        }
    };
    run(
        "narrowed_index",
        "let y = 1u64 - x0;\nlet v = [10u64, 20, 30, 40, 50, 60, 70, 80][(x0 & 7) as usize];\n\
         require_eq(Field::from(v + y), out);",
        "u64",
        &[
            (0, Some(11)),
            (1, Some(20)),
            (2, None),
            (7, None),
            (u64::MAX, None),
        ],
    );
    let native = |x: u64| {
        let i = if x < 100 { x & 3 } else { (x >> 2) & 3 };
        let mut t = [143u64, 120, 170, 31];
        t[i as usize] = x;
        Some(t[0] + 2 * t[1] + 3 * t[2] + 5 * t[3])
    };
    let cases: Vec<_> = [0u64, 1, 2, 3, 99, 100, 101, 200, 255]
        .iter()
        .map(|&x| (x, native(x)))
        .collect();
    run(
        "nested_store",
        "let i = if x0 < 100 { x0 & 3 } else { (x0 >> 2) & 3 };\n\
         let mut t = [143u8, 120u8, 170u8, 31u8];\nt[i as usize] = x0;\n\
         require_eq(Field::from(t[0] as u64 + 2 * t[1] as u64 + 3 * t[2] as u64 + 5 * t[3] as u64), out);",
        "u8",
        &cases,
    );
}

/// **The small-field checks are about the real circuit.** The EC add + double circuit
/// from [`small_field_curve_gadgets_are_sound`], compiled at limb widths 2–6 and 86:
/// its multiplication-gate count is exactly affine in the width (`396 + 174·bits`), so
/// no lowering path depends on the width, and the 86-bit instance (secp256k1's
/// modulus) is the shipped `xark_secp256k1::affine` gadget — the same circuit digest.
#[test]
fn scaled_curve_gadget_rows_match_secp256k1() {
    let secp = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F";
    let body = "let r = ec_add_incomplete(p, q); let d = ec_double_incomplete(p);\n\
                let mut i = 0;\n\
                while i < 3 { require_eq(r.x.limbs[i] + d.x.limbs[i], s.x.limbs[i]); \
                require_eq(r.y.limbs[i] + d.y.limbs[i], s.y.limbs[i]); i += 1; }";
    let circuit = |prelude: &str| {
        format!(
            "#![no_std]\nuse xark::prelude::*;\n{prelude}\n#[circuit]\n\
             pub fn circuit(p: Private<Point>, q: Private<Point>, s: Public<Point>) {{\n{body}\n}}\n"
        )
    };
    let toy = |bits: u32, p: &str| {
        circuit(&format!(
            "mod toy {{ xark_curve::weierstrass! {{ bits = {bits}, base = \"{p}\", scalar = \"{p}\", \
             a = 0, b = [7, 0, 0], generators = [[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0]], \
             correction = [0,0,0,0,0,0] }} }}\nuse toy::{{ec_add_incomplete, ec_double_incomplete, Point}};"
        ))
    };
    let build = |name: &str, src: String| {
        let c = compile_with_field(&write_case(name, &src), name, "bn254");
        assert!(c.status_success, "{name}: {}", c.stderr);
        c
    };
    for (bits, p) in [
        (2u32, "13"),
        (3, "127"),
        (4, "1279"),
        (5, "10007"),
        (6, "65519"),
        (86, secp),
    ] {
        let mul = build(&format!("scaled_ec_{bits}"), toy(bits, p)).mul_gate_count();
        assert_eq!(mul, 396 + 174 * bits as usize, "{bits}-bit limbs");
    }
    let toy86 = build("scaled_ec_86", toy(86, secp)).circuit_digest();
    let real = build(
        "scaled_ec_real",
        circuit("use xark_secp256k1::affine::{ec_add_incomplete, ec_double_incomplete, Point};"),
    )
    .circuit_digest();
    assert_eq!(
        toy86, real,
        "the 86-bit toy instance is the shipped secp256k1 gadget"
    );
}

/// gadget hints (`hint_div_rem`, the bignum mul/inverse/sub hints)
/// and `advice` inside a witness branch — inputs gated by the arm's guard, outputs
/// pinned where it isn't taken, every pin of theirs guarded.
#[test]
fn conditional_gadget_hints() {
    let src = write_case(
        "cond_hints",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(mode: Private<u8>, x: Private<Field>, m: Private<Field>, out: Public<Field>) {\n\
         \x20   let r = if mode == 1 {\n\
         \x20       let [q, r] = Field::hint_div_rem(x, m);\n\
         \x20       require_eq(q * m + r, x);\n\
         \x20       let _ = q.to_bits::<8>();\n\
         \x20       require(r.lt::<8>(m));\n\
         \x20       r\n\
         \x20   } else if mode == 2 {\n\
         \x20       let w = Field::advice();\n\
         \x20       require_eq(w * m, x);\n\
         \x20       w\n\
         \x20   } else {\n\
         \x20       x + m\n\
         \x20   };\n\
         \x20   require_eq(r, out);\n\
         }\n",
    );
    let c = compile_with_field(&src, "cond_hints", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    // Bare `advice` has no hint, so mode 2's witness is checked by search alone; the
    // other modes' by search and the honest solver.
    let case = |mode: &str, x: &str, m: &str, out: &str| {
        let inputs = [("mode", mode), ("x", x), ("m", m), ("out", out)];
        if mode == "2" {
            accepts_exactly_constraints(&c, &inputs)
        } else {
            accepts_exactly(&c, &inputs)
        }
    };
    // mode 0: `m = 0` is fine where the division isn't taken.
    assert!(case("0", "17", "0", "17"));
    assert!(!case("0", "17", "0", "18"));
    // mode 1: 17 = 3·5 + 2.
    assert!(case("1", "17", "5", "2"));
    assert!(!case("1", "17", "5", "7"));
    assert!(!case("1", "17", "0", "0"));
    assert!(!case("1", "17", "0", "17"));
    // mode 2: `w = x / m` (field division), pinned by the guarded `w·m = x`.
    assert!(case("2", "12", "4", "3"));
    assert!(!case("2", "12", "4", "4"));

    // Non-native field ops (mulmod, mod-inverse, sub2 hints) in arms.
    let src = write_case(
        "cond_bignum",
        "#![no_std]\nuse xark::prelude::*;\n\
         xark_bignum::fp!(El, \"57896044618658097711785492504343953926634992332820282019728792003956564819949\");\n\
         #[circuit]\n\
         pub fn circuit(mode: Private<u8>, a: Private<El>, b: Private<El>, out: Public<Field>) {\n\
         \x20   let r = if mode == 1 { a * b } else if mode == 2 { a.inverse() } \
         else if mode == 3 { a.sub2(b, b) } else { a + b };\n\
         \x20   require_eq(r.limbs[0], out);\n\
         }\n",
    );
    let c = compile_with_field(&src, "cond_bignum", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let case = |mode: &str, a: &str, b: &str, out: &str| {
        accepts_best_effort(
            &c,
            &[
                ("mode", mode),
                ("a.limbs[0]", a),
                ("a.limbs[1]", "0"),
                ("a.limbs[2]", "0"),
                ("b.limbs[0]", b),
                ("b.limbs[1]", "0"),
                ("b.limbs[2]", "0"),
                ("out", out),
            ],
        )
    };
    // mode 0: `a = 0` has no inverse, fine where `inverse` isn't taken.
    assert!(case("0", "0", "0", "0"));
    assert!(case("0", "2", "3", "5"));
    assert!(case("1", "2", "3", "6"));
    assert!(!case("1", "2", "3", "5"));
    // 2⁻¹ mod p = (p + 1) / 2 (p = 2²⁵⁵ − 19), low 86-bit limb.
    assert!(case("2", "2", "3", "77371252455336267181195255"));
    assert!(!case("2", "2", "3", "1"));
    assert!(!case("2", "0", "3", "0"));
    // 2 − 3 − 3 mod p = p − 4, low limb.
    assert!(case("3", "2", "3", "77371252455336267181195241"));
    assert!(!case("3", "2", "3", "0"));
}

/// an arm that can only panic is pruned, and the condition pinned to
/// the other arm. Shapes the fuzzer found reaching each pruning path (an arm that
/// touches witness data before it panics; one that panics past the rejoin point).
/// Every input is decided by exhaustive witness search against native Rust.
#[test]
fn pruned_arms_constrain_the_condition() {
    type Native = fn(&[u64]) -> Option<u64>;
    let cases: [(&str, &str, usize, Native); 4] = [
        (
            "prune_touch",
            "pub fn circuit(x0: Private<u16>, x1: Private<u16>, x2: Private<u16>, out: Public<Field>) {\n\
             \x20   let v0: u16 = if x0 == x2 { x0 - x2 } else { (x1 + x1).wrapping_mul(65534u16 + 2u16) };\n\
             \x20   if v0 == x1 { assert!(v0 <= x1); }\n\
             \x20   require_eq(Field::from(v0), out);\n\
             }\n",
            3,
            |x| {
                let (x0, x1, x2) = (x[0] as u16, x[1] as u16, x[2] as u16);
                if x0 == x2 {
                    Some(0)
                } else {
                    let _ = x1.checked_add(x1)?;
                    None // `65534u16 + 2u16` overflows
                }
            },
        ),
        (
            "prune_mod_zero",
            "pub fn circuit(x0: Private<u64>, x1: Private<u64>, out: Public<Field>) {\n\
             \x20   let v1: u64 = if x0 < x1 { (x1 ^ x1) & (x1 % 0u64) } else { (x1 / x1) + x1 };\n\
             \x20   require_eq(Field::from(v1), out);\n\
             }\n",
            2,
            |x| {
                let (x0, x1) = (x[0], x[1]);
                if x0 < x1 {
                    None
                } else {
                    (x1.checked_div(x1)?).checked_add(x1)
                }
            },
        ),
        (
            "prune_merged",
            "pub fn circuit(x0: Private<u32>, x1: Private<u32>, out: Public<Field>) {\n\
             \x20   let v0: u32 = x1 + x1;\n\
             \x20   let v1: u32 = if v0 == x0 { v0 } else { x0 };\n\
             \x20   let v2: u32 = if x0 != v0 { v1 - v1 } else { 7u32 * (x0 + 4294967294u32) };\n\
             \x20   require_eq(Field::from(v1 + v2), out);\n\
             }\n",
            2,
            |x| {
                let (x0, x1) = (x[0] as u32, x[1] as u32);
                let v0 = x1.checked_add(x1)?;
                let v1 = if v0 == x0 { v0 } else { x0 };
                let v2 = if x0 != v0 {
                    0
                } else {
                    7u32.checked_mul(x0.checked_add(4294967294)?)?
                };
                Some(v1.checked_add(v2)? as u64)
            },
        ),
        (
            "prune_rejoin",
            "pub fn circuit(x0: Private<u8>, x1: Private<u8>, out: Public<Field>) {\n\
             \x20   let v0: u8 = if x1 < x1 { x1 } else { x0 };\n\
             \x20   let v1: u8 = match x0 as u8 { 0 => 148, 6 => 113, 2 => 230, _ => 26 };\n\
             \x20   let v2: u8 = if v0 == v1 { v0.wrapping_add(x0) << 6 } else { !v0 };\n\
             \x20   let v4: u8 = v2 * ((x1 - v1) - (x0 % v0));\n\
             \x20   require_eq(Field::from(v4), out);\n\
             }\n",
            2,
            |x| {
                let (x0, x1) = (x[0] as u8, x[1] as u8);
                let v0 = x0;
                let v1 = match x0 {
                    0 => 148,
                    6 => 113,
                    2 => 230,
                    _ => 26,
                };
                let v2 = if v0 == v1 {
                    v0.wrapping_add(x0) << 6
                } else {
                    !v0
                };
                let d = x1.checked_sub(v1)?.checked_sub(x0.checked_rem(v0)?)?;
                Some(v2.checked_mul(d)? as u64)
            },
        ),
    ];
    let samples = [
        0u64,
        1,
        2,
        3,
        6,
        26,
        27,
        113,
        148,
        230,
        0x7fff,
        0xfffe,
        0xffff,
        0x7fff_ffff,
        0xffff_fffe,
        u64::MAX,
    ];
    for (name, body, n, native) in cases {
        let src = write_case(
            name,
            &format!(
                "#![no_std]\n#![allow(unconditional_panic, arithmetic_overflow)]\nuse xark::prelude::*;\n{body}"
            ),
        );
        let c = compile_with_field(&src, name, "bn254");
        assert!(c.status_success, "{name}: {}", c.stderr);
        let width = match name {
            "prune_touch" => 16,
            "prune_merged" => 32,
            "prune_rejoin" => 8,
            _ => 64,
        };
        let mask = if width == 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        };
        let mut grid: Vec<Vec<u64>> = vec![vec![]];
        for _ in 0..n {
            grid = grid
                .into_iter()
                .flat_map(|xs| {
                    samples
                        .iter()
                        .map(move |&v| [xs.clone(), vec![v & mask]].concat())
                })
                .collect();
        }
        grid.sort();
        grid.dedup();
        for xs in grid {
            let names: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
            let vals: Vec<String> = xs.iter().map(|v| v.to_string()).collect();
            let run = |out: u64| {
                let out = out.to_string();
                let mut inputs: Vec<(&str, &str)> = names
                    .iter()
                    .map(String::as_str)
                    .zip(vals.iter().map(String::as_str))
                    .collect();
                inputs.push(("out", &out));
                accepts_exactly(&c, &inputs)
            };
            match native(&xs) {
                Some(v) => {
                    assert!(run(v), "{name} {xs:?}: Rust gives {v}, circuit rejects");
                    assert!(!run(v + 1), "{name} {xs:?}: accepts {v} + 1");
                }
                None => {
                    for out in [0, 1, xs[0]] {
                        assert!(
                            !run(out),
                            "{name} {xs:?}: Rust panics, circuit accepts {out}"
                        );
                    }
                }
            }
        }
    }
}

/// `Field` range checks (`to_bits`), comparisons (`lt`) and
/// inverses inside a witness branch bind only when the arm is taken — an untaken
/// arm may see an out-of-range value or a zero.
#[test]
fn conditional_field_ops() {
    let src = write_case(
        "cond_field",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(mode: Private<u8>, x: Private<Field>, y: Private<Field>, out: Public<Field>) {\n\
         \x20   let r = if mode == 1 {\n\
         \x20       let b = x.to_bits::<8>();\n\
         \x20       b[0] + b[7]\n\
         \x20   } else if mode == 2 {\n\
         \x20       x.inv()\n\
         \x20   } else if mode == 3 {\n\
         \x20       if x.lt::<8>(y) { Field::from(1u8) } else { Field::from(2u8) }\n\
         \x20   } else {\n\
         \x20       x + y\n\
         \x20   };\n\
         \x20   require_eq(r, out);\n\
         }\n",
    );
    let c = compile_with_field(&src, "cond_field", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let case = |mode: &str, x: &str, y: &str, out: &str| {
        accepts_exactly(&c, &[("mode", mode), ("x", x), ("y", y), ("out", out)])
    };
    // mode 0: an out-of-range / zero `x` is fine in the untaken arms.
    assert!(case("0", "0", "5", "5"));
    assert!(case("0", "100000", "1", "100001"));
    assert!(!case("0", "1", "1", "3"));
    // mode 1: `x < 2^8`, out = bit0 + bit7.
    assert!(case("1", "129", "0", "2"));
    assert!(case("1", "2", "0", "0"));
    assert!(!case("1", "129", "0", "1"));
    assert!(!case("1", "256", "0", "0"));
    // mode 2: `x ≠ 0`, out = 1/x.
    assert!(case("2", "1", "0", "1"));
    assert!(!case("2", "0", "0", "0"));
    assert!(!case("2", "2", "0", "2"));
    // mode 3: `x, y < 2^8`.
    assert!(case("3", "3", "4", "1"));
    assert!(case("3", "4", "3", "2"));
    assert!(!case("3", "4", "3", "1"));
    assert!(!case("3", "300", "3", "2"));
}

/// `==` on `Field`, `<` via `Field::lt::<N>` + `require`, and witness mux via
/// `bool` wire arithmetic.
#[test]
fn cmp_operators_solve() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "cmp_ops",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>, eq: Public<Field>, feq: Public<Field>, mux: Public<Field>) {\n\
         \x20   let c = a.lt::<8>(b);\n\
         \x20   require(c);\n\
         \x20   require_eq(a == b, eq);\n\
         \x20   require_eq(a == b, feq);\n\
         \x20   let r = Field::from(c) * b + Field::from(!c) * a;\n\
         \x20   require_eq(r, mux);\n\
         }\n",
    );
    let c = compile_with_field(&src, "cmp_ops", "bn254");
    assert!(c.status_success, "cmp_ops failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };

    let mut inputs = BTreeMap::new();
    // a=3,b=5: require_lt passes (3<5), mux picks b=5.
    inputs.insert(id("a"), "3".to_string());
    inputs.insert(id("b"), "5".to_string());
    inputs.insert(id("eq"), "0".to_string());
    inputs.insert(id("feq"), "0".to_string());
    inputs.insert(id("mux"), "5".to_string());
    let asg = solver::solve_and_check(&program, &inputs).expect("3<5 solves");
    assert!(
        solver::analyze_underconstrained(&program, &asg).is_empty(),
        "comparison circuit under-constrained"
    );
    // a=5,b=3: require_lt fails (5 < 3 is false).
    inputs.insert(id("a"), "5".to_string());
    inputs.insert(id("b"), "3".to_string());
    inputs.insert(id("mux"), "5".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "5 < 3 must violate require_lt"
    );
    // a=5,b=5: require_lt fails (5 < 5 is false).
    inputs.insert(id("a"), "5".to_string());
    inputs.insert(id("b"), "5".to_string());
    inputs.insert(id("eq"), "1".to_string());
    inputs.insert(id("feq"), "1".to_string());
    inputs.insert(id("mux"), "5".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "5 < 5 must violate require_lt"
    );
}

/// Branchless lowering of `if` on a witness `bool`: the compiler detects both
/// arms are pure value copies converging at a join block, and replaces the
/// `SwitchInt` with muxes (`else + cond·(then − else)`).
#[test]
fn if_mux_lowers_and_solves() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "if_mux",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(x: Private<Field>, a: Private<Field>, b: Private<Field>, left: Public<Field>, right: Public<Field>) {\n\
         \x20   let (l, r) = if x.is_zero() {\n\
         \x20       (a, b)\n\
         \x20   } else {\n\
         \x20       (b, a)\n\
         \x20   };\n\
         \x20   require_eq(l, left);\n\
         \x20   require_eq(r, right);\n\
         }\n",
    );
    let c = compile_with_field(&src, "if_mux", "bn254");
    assert!(c.status_success, "if_mux failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };
    let case = |x: &str, a: &str, b: &str, left: &str, right: &str| {
        let mut m = BTreeMap::new();
        m.insert(id("x"), x.to_string());
        m.insert(id("a"), a.to_string());
        m.insert(id("b"), b.to_string());
        m.insert(id("left"), left.to_string());
        m.insert(id("right"), right.to_string());
        m
    };
    // x=0 → is_zero=true → pick (a,b) = (7,9). (The zero-input edge case yields
    // a statically free inverse witness — a known limitation of the gadget, not
    // a soundness issue.)
    solver::solve_and_check(&program, &case("0", "7", "9", "7", "9")).expect("x=0 pick a");
    // x=5 → is_zero=false → pick (b,a) = (9,7). Non-zero case must be fully constrained.
    let asg =
        solver::solve_and_check(&program, &case("5", "7", "9", "9", "7")).expect("x=5 pick b");
    assert!(
        solver::analyze_underconstrained(&program, &asg).is_empty(),
        "if-mux circuit under-constrained: {:?}",
        solver::analyze_underconstrained(&program, &asg)
    );
    // Wrong result rejected.
    assert!(
        solver::solve_and_check(&program, &case("0", "7", "9", "9", "7")).is_err(),
        "wrong mux must reject"
    );
}

/// `is_zero` gadget via `require`: x=0 passes; x=7 is rejected.
#[test]
fn is_zero_gadget_solves() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "is_zero",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(x: Private<Field>) {\n\
         \x20   require(x.is_zero());\n\
         }\n",
    );
    let c = compile_with_field(&src, "is_zero", "bn254");
    assert!(c.status_success, "is_zero failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };

    let mut inputs = BTreeMap::new();
    inputs.insert(id("x"), "0".to_string());
    solver::solve_and_check(&program, &inputs).expect("is_zero(0) must pass");

    inputs.insert(id("x"), "7".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "is_zero(7) must be rejected"
    );
}

/// `require(a == b)`: a=b=5 passes; a=5,b=6 is rejected.
#[test]
fn equality_operator_solves() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "eq_op",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>) {\n\
         \x20   require(a == b);\n\
         }\n",
    );
    let c = compile_with_field(&src, "eq_op", "bn254");
    assert!(c.status_success, "eq_op failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };

    let mut inputs = BTreeMap::new();
    inputs.insert(id("a"), "5".to_string());
    inputs.insert(id("b"), "5".to_string());
    solver::solve_and_check(&program, &inputs).expect("a == b must pass");

    inputs.insert(id("b"), "6".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "a != b must be rejected"
    );
}

/// A secp256k1 scalar must be canonical (`< n`) and nonzero; a non-canonical `s`
/// and `s = 0` are both rejected.
#[test]
fn ecdsa_scalar_range_checks() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let c = compile_with_field(&example("scalar_range"), "scalar_range", "bn254");
    assert!(c.status_success, "scalar_range failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };
    let case = |s0: &str, s1: &str, s2: &str| {
        let mut m = BTreeMap::new();
        m.insert(id("s0"), s0.to_string());
        m.insert(id("s1"), s1.to_string());
        m.insert(id("s2"), s2.to_string());
        m
    };
    // s = 1 (canonical, nonzero) → satisfiable.
    solver::solve_and_check(&program, &case("1", "0", "0")).expect("s = 1 must be a valid scalar");
    // s = 0 → rejected by assert_nonzero.
    assert!(
        solver::solve_and_check(&program, &case("0", "0", "0")).is_err(),
        "s = 0 must be rejected"
    );
    // Every limb at 2^86-1 → value ≈ 2^258, far above n → rejected by assert_canonical.
    let max_limb = "77371252455336267181195263"; // 2^86 - 1
    assert!(
        solver::solve_and_check(&program, &case(max_limb, max_limb, max_limb)).is_err(),
        "a non-canonical scalar (>= n) must be rejected"
    );
}

/// Branchless boolean mux: `require_bool` pins the condition, then
/// `if_false + cond·(if_true − if_false)` selects — a non-boolean condition is
/// rejected by `require_bool`.
#[test]
fn bool_mux_solve() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "bool_mux",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(cond: Private<Field>, a: Private<Field>, b: Private<Field>, out: Public<Field>) {\n\
         \x20   cond.require_bool();\n\
         \x20   require_eq(b + cond * (a - b), out);\n\
         }\n",
    );
    let c = compile_with_field(&src, "bool_mux", "bn254");
    assert!(c.status_success, "bool_mux failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };
    let case = |cond: &str, a: &str, b: &str, out: &str| {
        let mut m = BTreeMap::new();
        m.insert(id("cond"), cond.to_string());
        m.insert(id("a"), a.to_string());
        m.insert(id("b"), b.to_string());
        m.insert(id("out"), out.to_string());
        m
    };
    solver::solve_and_check(&program, &case("1", "7", "9", "7")).expect("cond=true selects a");
    solver::solve_and_check(&program, &case("0", "7", "9", "9")).expect("cond=false selects b");
    assert!(
        solver::solve_and_check(&program, &case("1", "7", "9", "9")).is_err(),
        "wrong mux must reject"
    );
    assert!(
        solver::solve_and_check(&program, &case("2", "7", "9", "7")).is_err(),
        "non-boolean cond must reject"
    );
}

/// `Field` boolean combinators `and`/`or`/`not` (on wires pinned `{0,1}` by
/// `require_bool`) lower and solve.
#[test]
fn bool_combinators_solve() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "bool_ops",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>, want: Public<Field>) {\n\
         \x20   a.require_bool();\n\
         \x20   b.require_bool();\n\
         \x20   require_eq(a.and(b).or(a.not()), want);\n\
         }\n",
    );
    let c = compile_with_field(&src, "bool_ops", "bn254");
    assert!(c.status_success, "bool_ops failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };
    let case = |a: &str, b: &str, want: &str| {
        let mut m = BTreeMap::new();
        m.insert(id("a"), a.to_string());
        m.insert(id("b"), b.to_string());
        m.insert(id("want"), want.to_string());
        m
    };
    // a.and(b).or(a.not()) : a=1,b=0 -> (1&0)|!1 = 0 ; a=0,b=1 -> (0&1)|!0 = 1.
    solver::solve_and_check(&program, &case("1", "0", "0")).expect("(1&0)|!1 == 0");
    solver::solve_and_check(&program, &case("0", "1", "1")).expect("(0&1)|!0 == 1");
    // Non-boolean input is rejected by require_bool.
    assert!(
        solver::solve_and_check(&program, &case("2", "0", "0")).is_err(),
        "non-boolean input must reject"
    );
}

/// Rejections carry an actionable `help:` line (the diagnostic contract).
#[test]
fn rejections_carry_actionable_help() {
    // A bare `Field` parameter (must be wrapped in a visibility marker).
    let bare = write_case(
        "diag_bare_field",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(x: Field, out: Public<Field>) {\n\
         \x20   require_eq(x, out);\n\
         }\n",
    );
    let c = compile_with_field(&bare, "diag_bare_field", "bn254");
    assert!(!c.status_success, "bare Field param should be rejected");
    assert!(
        c.stderr.contains("help:"),
        "rejection must include a help line; got: {}",
        c.stderr
    );
    assert!(
        c.stderr.contains("Private<Field>") || c.stderr.contains("Public<Field>"),
        "help should point at the visibility markers; got: {}",
        c.stderr
    );
}

// (The standalone secp256k1 on-curve snapshot test was removed with the
// `on_curve_k1` example; secp256k1's on-curve check is now exercised by the
// `ecdsa_verify` example's off-curve-pubkey reject test, on the 4×64 path the GLV
// gadget actually uses.)

/// The secp256r1 (a = −3) on-curve gadget: real pubkey accepted, perturbed rejected.
#[test]
fn secp256r1_on_curve_accepts_real_rejects_perturbed() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let c = compile_with_field(&example("on_curve_r1"), "on_curve_r1", "bn254");
    assert!(c.status_success, "on_curve_r1 failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };
    let kat = [
        ("q.x.limbs[0]", "67266088408721815440178629"),
        ("q.x.limbs[1]", "32122441355340553600857496"),
        ("q.x.limbs[2]", "8254854985909125326758352"),
        ("q.y.limbs[0]", "20513967152570891030533053"),
        ("q.y.limbs[1]", "70247732038174899916449580"),
        ("q.y.limbs[2]", "15284152633358001387265917"),
    ];
    let base = || {
        let mut m = BTreeMap::new();
        for (k, v) in kat.iter() {
            m.insert(id(k), v.to_string());
        }
        m
    };
    solver::solve_and_check(&program, &base()).expect("on-curve P-256 pubkey must be accepted");
    let mut bad = base();
    bad.insert(id("q.y.limbs[0]"), "1".to_string());
    assert!(
        solver::solve_and_check(&program, &bad).is_err(),
        "an off-curve P-256 pubkey must be rejected"
    );
}

/// The Ed25519 on-curve gadget accepts a real point (base point B) and rejects
/// a perturbed coordinate.
#[test]
fn ed25519_on_curve_accepts_real_rejects_perturbed() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let c = compile_with_field(&example("on_curve_ed25519"), "on_curve_ed25519", "bn254");
    assert!(c.status_success, "on_curve_ed25519 failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };
    // Ed25519 base point B, as 86-bit limbs (from xark_ed25519::base()).
    let kat = [
        ("q.x.limbs[0]", "45522188556658772877366554"),
        ("q.x.limbs[1]", "10615720421966981067801172"),
        ("q.x.limbs[2]", "2524463244633754693274190"),
        ("q.y.limbs[0]", "46422751473201760308717144"),
        ("q.y.limbs[1]", "30948500982134506872478105"),
        ("q.y.limbs[2]", "7737125245533626718119526"),
    ];
    let base = || {
        let mut m = BTreeMap::new();
        for (k, v) in kat.iter() {
            m.insert(id(k), v.to_string());
        }
        m
    };
    solver::solve_and_check(&program, &base()).expect("on-curve Ed25519 point must be accepted");
    let mut bad = base();
    bad.insert(id("q.y.limbs[0]"), "1".to_string());
    assert!(
        solver::solve_and_check(&program, &bad).is_err(),
        "an off-curve Ed25519 point must be rejected"
    );
}

// --- require / require_lt / require_ge (author-facing constraint API) ------------

/// `require(cond)` constrains a boolean wire to true. a=b passes; a≠b fails.
#[test]
fn require_bool_demo() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};

    let src = write_case(
        "assert_demo",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>) {\n\
         \x20   require(a == b);\n\
         }\n",
    );
    let c = compile_with_field(&src, "assert_demo", "bn254");
    assert!(c.status_success, "assert_demo failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .map(|v| v.id)
            .unwrap()
    };

    let mut inputs = BTreeMap::new();
    inputs.insert(id("a"), "3".to_string());
    inputs.insert(id("b"), "3".to_string());
    solver::solve_and_check(&program, &inputs).expect("a == b must pass");

    inputs.insert(id("b"), "5".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "a != b must violate require"
    );
}

// --- Field vs native-int-constant comparison surface (docs/integer-ops.md) -----
// `PartialEq<uN>` (`==`/`!=`, width-independent) and `PartialOrd<uN>`
// (`<`/`<=`/`>`/`>=`, range-checked to `< 2^N`) for `Field`, plus the
// explicit-width Field-vs-Field methods `Field::lt::<N>` etc.

/// Build a `bn254` circuit from a body (prelude in scope) and return its
/// primitive program.
fn cmp_program(name: &str, body: &str) -> xark_ir::primitive::PrimitiveProgram {
    let src = write_case(
        name,
        &format!("#![no_std]\nuse xark::prelude::*;\n{body}\n"),
    );
    let c = compile_with_field(&src, name, "bn254");
    assert!(c.status_success, "{name} failed to compile: {}", c.stderr);
    xark_ir::primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
        .unwrap()
}

/// Solve `program` with the given `(name, decimal)` inputs; returns whether the
/// witness solves AND satisfies every constraint.
fn solves(program: &xark_ir::primitive::PrimitiveProgram, inputs: &[(&str, &str)]) -> bool {
    use std::collections::BTreeMap;
    let id = |n: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == n)
            .unwrap_or_else(|| panic!("no input var `{n}`"))
            .id
    };
    let map: BTreeMap<u32, String> = inputs.iter().map(|(n, v)| (id(n), v.to_string())).collect();
    xark_ir::solver::solve_and_check(program, &map).is_ok()
}

/// `x == c` / `x != c` / `x < c` / `x <= c` / `x > c` / `x >= c` against a `u32`
/// constant: each comparison is bound to a public output; a correct set of
/// outputs solves, and flipping any one output is rejected.
#[test]
fn field_cmp_uint_const_ops_solve() {
    let program = cmp_program(
        "cmp_uint_const",
        "pub fn circuit(x: Private<Field>, lt: Public<Field>, le: Public<Field>, \
         gt: Public<Field>, ge: Public<Field>, eq: Public<Field>, ne: Public<Field>) {\n\
         \x20   require_eq(x < 100u32, lt);\n\
         \x20   require_eq(x <= 100u32, le);\n\
         \x20   require_eq(x > 100u32, gt);\n\
         \x20   require_eq(x >= 100u32, ge);\n\
         \x20   require_eq(x == 100u32, eq);\n\
         \x20   require_eq(x != 100u32, ne);\n\
         }",
    );
    // x = 50: <100 t, <=100 t, >100 f, >=100 f, ==100 f, !=100 t.
    let ok = [
        ("x", "50"),
        ("lt", "1"),
        ("le", "1"),
        ("gt", "0"),
        ("ge", "0"),
        ("eq", "0"),
        ("ne", "1"),
    ];
    assert!(solves(&program, &ok), "x=50 correct outputs must solve");
    // Flip each output → rejected.
    for (i, (nm, _)) in ok.iter().enumerate().skip(1) {
        let mut bad = ok;
        bad[i].1 = if ok[i].1 == "1" { "0" } else { "1" };
        assert!(
            !solves(&program, &bad),
            "flipping `{nm}` must violate a constraint"
        );
    }
    // x = 100: ==100 t, <100 f, <=100 t, >100 f, >=100 t, !=100 f.
    assert!(
        solves(
            &program,
            &[
                ("x", "100"),
                ("lt", "0"),
                ("le", "1"),
                ("gt", "0"),
                ("ge", "1"),
                ("eq", "1"),
                ("ne", "0"),
            ]
        ),
        "x=100 boundary outputs must solve"
    );
}

/// Boundary behaviour of `<` and `<=` against a constant, via `require`.
#[test]
fn field_cmp_boundaries() {
    // require(x < 100): true at 99, false at 100.
    let lt = cmp_program(
        "cmp_lt_boundary",
        "pub fn circuit(x: Private<Field>) { require(x < 100u32); }",
    );
    assert!(solves(&lt, &[("x", "99")]), "99 < 100 holds");
    assert!(!solves(&lt, &[("x", "100")]), "100 < 100 must fail");

    // require(x <= 100): true at 100, false at 101.
    let le = cmp_program(
        "cmp_le_boundary",
        "pub fn circuit(x: Private<Field>) { require(x <= 100u32); }",
    );
    assert!(solves(&le, &[("x", "100")]), "100 <= 100 holds");
    assert!(!solves(&le, &[("x", "101")]), "101 <= 100 must fail");
}

/// Edge constants: `c = 0` (`x < 0` never holds; `x >= 0` always holds) and a
/// constant near `2^32 − 1` (the negation form of `<=` avoids a `c + 1`
/// overflow at the top of the domain).
#[test]
fn field_cmp_edge_constants() {
    // x < 0u32 is always false: unprovable even for x = 0.
    let lt0 = cmp_program(
        "cmp_lt_zero",
        "pub fn circuit(x: Private<Field>) { require(x < 0u32); }",
    );
    assert!(!solves(&lt0, &[("x", "0")]), "x < 0 is never true");

    // x >= 0u32 is always true.
    let ge0 = cmp_program(
        "cmp_ge_zero",
        "pub fn circuit(x: Private<Field>) { require(x >= 0u32); }",
    );
    assert!(solves(&ge0, &[("x", "0")]), "0 >= 0 holds");
    assert!(solves(&ge0, &[("x", "5")]), "5 >= 0 holds");

    // c = 2^32 - 2: x <= c true at c, false at c+1 = 2^32 - 1 (both in-domain).
    let hi = cmp_program(
        "cmp_le_near_max",
        "pub fn circuit(x: Private<Field>) { require(x <= 4294967294u32); }",
    );
    assert!(
        solves(&hi, &[("x", "4294967294")]),
        "x <= 2^32-2 holds at 2^32-2"
    );
    assert!(
        !solves(&hi, &[("x", "4294967295")]),
        "2^32-1 <= 2^32-2 must fail"
    );
}

/// SOUNDNESS: the `to_bits::<32>` range check inside `<` makes an out-of-domain
/// witness (`x = 2^32 + 5`) unprovable — the decomposition cannot recompose to
/// `x`, so no false proof of `x < 100u32` is possible.
#[test]
fn field_cmp_out_of_range_is_unprovable() {
    let program = cmp_program(
        "cmp_soundness",
        "pub fn circuit(x: Private<Field>) { require(x < 100u32); }",
    );
    // In-domain small value proves.
    assert!(solves(&program, &[("x", "50")]), "50 < 100 proves");
    // 2^32 + 5 = 4294967301: residue's low 32 bits are 5 (< 100), but it is NOT
    // < 2^32, so the range check is unsatisfiable — must be REJECTED.
    assert!(
        !solves(&program, &[("x", "4294967301")]),
        "an out-of-32-bit witness must fail the range check, not sneak a proof"
    );
}

/// Field-vs-Field explicit-width methods: `a.lt::<32>(b)` proves for `a < b`,
/// rejects `a >= b`, and rejects an out-of-domain `a` (both operands are
/// range-checked).
#[test]
fn field_field_lt_method() {
    let program = cmp_program(
        "cmp_field_field",
        "pub fn circuit(a: Private<Field>, b: Private<Field>) { require(a.lt::<32>(b)); }",
    );
    assert!(solves(&program, &[("a", "3"), ("b", "5")]), "3 < 5 proves");
    assert!(
        !solves(&program, &[("a", "5"), ("b", "3")]),
        "5 < 3 rejects"
    );
    assert!(
        !solves(&program, &[("a", "5"), ("b", "5")]),
        "5 < 5 rejects"
    );
    // Out-of-range `a` (2^32 + 1) fails its own range check.
    assert!(
        !solves(&program, &[("a", "4294967297"), ("b", "5")]),
        "out-of-range `a` must fail the range check"
    );

    // le/ge via `!gt`/`!lt`.
    let le = cmp_program(
        "cmp_field_field_le",
        "pub fn circuit(a: Private<Field>, b: Private<Field>) { require(a.le::<32>(b)); }",
    );
    assert!(solves(&le, &[("a", "5"), ("b", "5")]), "5 <= 5 proves");
    assert!(!solves(&le, &[("a", "6"), ("b", "5")]), "6 <= 5 rejects");
}

// --- Field shift + modulus surface (docs/integer-ops.md) -----------------------
// `Shr<uN>` (`x >> n`), `Shl<uN>` (`x << n`, truncated to N bits), and `Rem<uN>`
// (`x % m`) for `Field`, where the native-int RHS type carries the domain width
// `N` and its value is the shift amount / modulus. All range-check `x < 2^N`.

/// `x >> 3u32` = ⌊x / 8⌋ within the 32-bit domain (100 → 12); a wrong output is
/// rejected, and an out-of-32-bit witness fails the `to_bits::<32>` range check.
#[test]
fn field_shr_solves() {
    let program = cmp_program(
        "shr_u32",
        "pub fn circuit(x: Private<Field>, out: Public<Field>) { require_eq(x >> 3u32, out); }",
    );
    assert!(
        solves(&program, &[("x", "100"), ("out", "12")]),
        "100 >> 3 = 12"
    );
    assert!(
        !solves(&program, &[("x", "100"), ("out", "13")]),
        "wrong result rejected"
    );
    // SOUNDNESS: 2^32 + 100 is not < 2^32, so `to_bits::<32>` is unsatisfiable —
    // no sneaking a proof by supplying the low-32-bit shift.
    assert!(
        !solves(&program, &[("x", "4294967396"), ("out", "12")]),
        "out-of-32-bit witness must fail the range check"
    );
}

/// BIT CACHE (docs/integer-ops.md § Bit caching): a witness value decomposed to
/// the same width `N` more than once shares ONE `to_bits::<N>` — the second op
/// reuses the stored bits, skipping the `N` booleanity + 1 recomposition
/// constraints. Proven differentially: reusing one `x` costs exactly one 32-bit
/// decomposition (33 constraints) less than decomposing two distinct values.
#[test]
fn bit_cache_shares_one_decomposition() {
    // `x` is used in both `x < 100u32` and `x >> 1u32` → one shared decomposition.
    let shared = cmp_program(
        "bitcache_shared",
        "pub fn circuit(x: Private<Field>, half: Public<Field>) {\n\
         \x20   require(x < 100u32);\n\
         \x20   require_eq(x >> 1u32, half);\n\
         }",
    );
    // Same shape but the shift is on a *distinct* value `y` → two independent
    // decompositions (no cache hit possible across different values).
    let distinct = cmp_program(
        "bitcache_distinct",
        "pub fn circuit(x: Private<Field>, y: Private<Field>, half: Public<Field>) {\n\
         \x20   require(x < 100u32);\n\
         \x20   require_eq(y >> 1u32, half);\n\
         }",
    );

    // A width-32 decomposition is 32 booleanity constraints + 1 recomposition.
    const DECOMP_32: usize = 33;
    let shared_n = shared.constraints.len();
    let distinct_n = distinct.constraints.len();
    assert!(
        shared_n < distinct_n,
        "the reused decomposition must drop constraints: shared={shared_n}, distinct={distinct_n}"
    );
    assert_eq!(
        shared_n + DECOMP_32,
        distinct_n,
        "reusing `x` must save exactly one 32-bit decomposition ({DECOMP_32} constraints): \
         shared={shared_n}, distinct={distinct_n}"
    );

    // CORRECTNESS still holds with the shared decomposition: x = 50 (< 100),
    // 50 >> 1 = 25 solves; a wrong shifted output is rejected.
    assert!(
        solves(&shared, &[("x", "50"), ("half", "25")]),
        "x=50: 50 < 100 and 50 >> 1 = 25 must solve"
    );
    assert!(
        !solves(&shared, &[("x", "50"), ("half", "26")]),
        "a wrong `x >> 1` output must be rejected"
    );
    // The bounds check is real: x = 100 is not < 100 → unprovable.
    assert!(
        !solves(&shared, &[("x", "100"), ("half", "50")]),
        "x=100 violates `x < 100u32`"
    );
}

/// Shift edges: `x >> 0u32` is the identity, and `x >> 40u32` at width 32 shifts
/// every bit out → 0.
#[test]
fn field_shr_edges() {
    let id = cmp_program(
        "shr_zero",
        "pub fn circuit(x: Private<Field>, out: Public<Field>) { require_eq(x >> 0u32, out); }",
    );
    assert!(
        solves(&id, &[("x", "12345"), ("out", "12345")]),
        "x >> 0 = x"
    );
    assert!(
        !solves(&id, &[("x", "12345"), ("out", "12344")]),
        "x >> 0 != x-1"
    );

    let big = cmp_program(
        "shr_overshift",
        "pub fn circuit(x: Private<Field>, out: Public<Field>) { require_eq(x >> 40u32, out); }",
    );
    assert!(
        solves(&big, &[("x", "4000000000"), ("out", "0")]),
        "shift >= width -> 0"
    );
    assert!(
        !solves(&big, &[("x", "4000000000"), ("out", "1")]),
        "overshift is exactly 0"
    );
}

/// `x << 2u16` = x·4 within the 16-bit domain (5 → 20); wrong output rejected.
#[test]
fn field_shl_solves() {
    let program = cmp_program(
        "shl_u16",
        "pub fn circuit(x: Private<Field>, out: Public<Field>) { require_eq(x << 2u16, out); }",
    );
    assert!(
        solves(&program, &[("x", "5"), ("out", "20")]),
        "5 << 2 = 20"
    );
    assert!(
        !solves(&program, &[("x", "5"), ("out", "21")]),
        "wrong result rejected"
    );
}

/// `<<` truncates at `2^N` (integer shift semantics, NOT `x·2ⁿ mod p`): an 8-bit
/// `200u8 << 2` drops the bits pushed past position 8, giving `(200<<2) mod 256
/// = 32`.
#[test]
fn field_shl_truncates() {
    let program = cmp_program(
        "shl_trunc_u8",
        "pub fn circuit(x: Private<Field>, out: Public<Field>) { require_eq(x << 2u8, out); }",
    );
    // 200 << 2 = 800; low 8 bits = 800 mod 256 = 32.
    assert!(
        solves(&program, &[("x", "200"), ("out", "32")]),
        "200 << 2 truncates to 32"
    );
    // The non-truncated value 800 is NOT the result.
    assert!(
        !solves(&program, &[("x", "200"), ("out", "800")]),
        "no `x*4` (would be 800)"
    );
}

/// `x % 8u32` — power-of-two modulus, the low 3 bits, no hint (100 → 4).
#[test]
fn field_rem_pow2_solves() {
    let program = cmp_program(
        "rem_pow2_u32",
        "pub fn circuit(x: Private<Field>, out: Public<Field>) { require_eq(x % 8u32, out); }",
    );
    assert!(
        solves(&program, &[("x", "100"), ("out", "4")]),
        "100 % 8 = 4"
    );
    assert!(
        !solves(&program, &[("x", "100"), ("out", "5")]),
        "wrong remainder rejected"
    );
    // Out-of-32-bit witness fails the range check.
    assert!(
        !solves(&program, &[("x", "4294967396"), ("out", "4")]),
        "out-of-range witness must fail the range check"
    );
}

/// `x % 7u32` — general (non-power-of-two) modulus via `hint_div_rem`, pinned by
/// `7·q + r == x`, `r < 7`, `q < 2³²` (100 → 2). A wrong remainder is
/// unsatisfiable (the hint is honest; the equality/range pins reject a forged
/// `r`), and an out-of-range witness fails.
#[test]
fn field_rem_general_solves() {
    let program = cmp_program(
        "rem_general_u32",
        "pub fn circuit(x: Private<Field>, out: Public<Field>) { require_eq(x % 7u32, out); }",
    );
    assert!(
        solves(&program, &[("x", "100"), ("out", "2")]),
        "100 % 7 = 2"
    );
    assert!(solves(&program, &[("x", "98"), ("out", "0")]), "98 % 7 = 0");
    // SOUNDNESS: a circuit asserting a *wrong* remainder is unsatisfiable.
    assert!(
        !solves(&program, &[("x", "100"), ("out", "3")]),
        "forged remainder rejected"
    );
    assert!(
        !solves(&program, &[("x", "4294967396"), ("out", "2")]),
        "out-of-range witness must fail the range check"
    );
}

/// SOUNDNESS: `Rem<u128>` is intentionally NOT provided (a general modulus at
/// `N = 128` could wrap `m·q` past the field and forge a remainder). `x % 5u128`
/// must therefore fail to compile — while `x >> 3u128` (a shift, always sound at
/// any width) and `x % 5u64` (a narrower modulus) still work.
#[test]
fn field_rem_u128_is_not_provided() {
    // `Rem<u128> for Field` does not resolve → a type error, compile fails.
    let bad = write_case(
        "rem_u128",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(x: Private<Field>, out: Public<Field>) { require_eq(x % 5u128, out); }\n",
    );
    let c = compile_with_field(&bad, "rem_u128", "bn254");
    assert!(
        !c.status_success,
        "`x % 5u128` must not compile (Rem<u128> is deliberately omitted)"
    );

    // Shifts remain available at u128 (pure re-wiring, sound).
    let shr = cmp_program(
        "shr_u128",
        "pub fn circuit(x: Private<Field>, out: Public<Field>) { require_eq(x >> 3u128, out); }",
    );
    assert!(
        solves(&shr, &[("x", "100"), ("out", "12")]),
        "100 >> 3u128 = 12"
    );

    // Modulus remains available at u64 (2N = 128 <= 253, sound).
    let rem = cmp_program(
        "rem_u64",
        "pub fn circuit(x: Private<Field>, out: Public<Field>) { require_eq(x % 5u64, out); }",
    );
    assert!(
        solves(&rem, &[("x", "100"), ("out", "0")]),
        "100 % 5u64 = 0"
    );
    assert!(
        solves(&rem, &[("x", "103"), ("out", "3")]),
        "103 % 5u64 = 3"
    );
}

/// `witness_only` regions: multiplications inside `witness_begin()`/`witness_end()`
/// emit witness-gen but **no constraints**, the unreferenced `x²` scratch is
/// exempt from `check_pinning` (so the circuit even compiles), and the derived
/// result stays sound because it's pinned to a constrained recompute.
#[test]
fn witness_only_derives_without_constraints() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let c = compile_with_field(
        &example("witness_only_check"),
        "witness_only_check",
        "bn254",
    );
    // Compiling at all proves the exemption: without it, the unreferenced `x²`
    // scratch would be rejected as an unpinned hint output.
    assert!(c.status_success, "witness_only_check failed: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    // The two witness-only muls (`x²`, `d`) emit zero constraints; only the
    // constrained `x·x·x·x` and the equality pins remain. Constraining them
    // naively would add two mul gates.
    let n = program.constraints.len();
    // Only the constrained `x·x·x·x` (3 muls) + 2 equality pins remain; the two
    // witness-only muls emit nothing. Constraining them naively would add two.
    assert!(
        n <= 5,
        "witness-only muls must not each emit a constraint (got {n})"
    );
    let id = |name: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == name)
            .unwrap_or_else(|| panic!("missing var `{name}`"))
            .id
    };
    let inputs = |claim: &str| {
        let mut m = BTreeMap::new();
        m.insert(id("x"), "3".to_string());
        m.insert(id("claim"), claim.to_string());
        m
    };
    // 3⁴ = 81 accepts; a wrong claim is rejected (the pinned result is sound).
    solver::solve_and_check(&program, &inputs("81")).expect("3⁴ = 81 must accept");
    assert!(
        solver::solve_and_check(&program, &inputs("80")).is_err(),
        "claim ≠ x⁴ must be rejected"
    );
}

/// `Field::from(x)` on a native `uN` *witness* is the identity on its (already
/// range-checked) wire, including through the widening cast inside `From<u8>`.
#[test]
fn uint_witness_converts_to_field() {
    for ty in ["u8", "u32", "u64", "u128"] {
        let src = format!(
            "#![no_std]\nuse xark::prelude::*;\n\
             pub fn circuit(a: Private<{ty}>, b: Public<Field>) {{\n\
             require_eq(Field::from(a), b);\n}}\n"
        );
        let name = format!("uint_to_field_{ty}");
        let c = compile_with_field(&write_case(&name, &src), &name, "bn254");
        assert!(c.status_success, "{ty}: {}", c.stderr);
        let p = c.program();
        assert!(
            solves(&p, &[("a", "200"), ("b", "200")]),
            "{ty}: equal values solve"
        );
        assert!(
            !solves(&p, &[("a", "200"), ("b", "201")]),
            "{ty}: unequal values reject"
        );
    }
}

/// A narrowing cast of a witness (`a as u8`) truncates, as Rust defines it.
#[test]
fn narrowing_witness_cast() {
    let src = "#![no_std]\nuse xark::prelude::*;\n\
        pub fn circuit(a: Private<u64>, b: Public<Field>) {\n\
        let x = a as u8;\n\
        require_eq(Field::from(x), b);\n}\n";
    let c = compile_with_field(&write_case("narrow_cast", src), "narrow_cast", "bn254");
    // Truncation, pinned by the decomposition of `a` (0x1234 → 0x34).
    assert!(c.status_success, "{}", c.stderr);
    assert!(accepts(&c, &[("a", "4660"), ("b", "52")]));
    assert!(!accepts(&c, &[("a", "4660"), ("b", "4660")]));
    assert!(!accepts(&c, &[("a", "4660"), ("b", "53")]));
}

/// A `[u8; N]` `#[circuit]` parameter reaches the body as `[Field; N]`; the macro must
/// still range-check every byte, or a prover could pass 256 (or any field element).
#[test]
fn byte_array_param_is_range_checked() {
    let src = "#![no_std]\nuse xark::prelude::*;\n\
        #[circuit]\n\
        pub fn bytes(b: Private<[u8; 2]>, s: Public<Field>) {\n\
        require_eq(b[0] + b[1], s);\n}\n";
    let c = compile_with_field(&write_case("byte_param", src), "byte_param", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let p = c.program();
    assert!(solves(&p, &[("b[0]", "255"), ("b[1]", "1"), ("s", "256")]));
    assert!(
        !solves(&p, &[("b[0]", "256"), ("b[1]", "0"), ("s", "256")]),
        "256 is not a byte"
    );
}

/// `#[input]` with native integers, a byte array, and a nested struct:
/// leaves are named by the structural flatten, each `uN` is range-checked on entry, and
/// `to_fields()` flattens nested structs inline.
#[test]
fn circuit_input_with_uints_and_nesting() {
    let src = "#![no_std]\nuse xark::prelude::*;\n\
        #[input]\n\
        pub struct Inner { pub a: u64, pub b: Field }\n\
        #[input]\n\
        pub struct Outer { pub inner: Inner, pub tag: [u8; 2], pub c: u32 }\n\
        #[circuit]\n\
        pub fn nested(o: Private<Outer>, h: Public<Field>) {\n\
        let f = o.to_fields();\n\
        require_eq(f[0] + f[1] + f[2] + f[3] + f[4], h);\n}\n";
    let c = compile_with_field(&write_case("nested_input", src), "nested_input", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let p = c.program();
    let ok = [
        ("o.inner.a", "10"),
        ("o.inner.b", "20"),
        ("o.tag[0]", "1"),
        ("o.tag[1]", "2"),
        ("o.c", "3"),
        ("h", "36"),
    ];
    assert!(solves(&p, &ok));
    let mut wrong_sum = ok;
    wrong_sum[5] = ("h", "37");
    assert!(!solves(&p, &wrong_sum));
    let mut big_a = ok;
    big_a[0] = ("o.inner.a", "18446744073709551616"); // 2^64
    big_a[5] = ("h", "18446744073709551642");
    assert!(
        !solves(&p, &big_a),
        "a u64 field >= 2^64 must fail its range check"
    );
    let mut big_byte = ok;
    big_byte[2] = ("o.tag[0]", "256");
    big_byte[5] = ("h", "291");
    assert!(
        !solves(&p, &big_byte),
        "a u8 field >= 256 must fail its range check"
    );
}

/// `xark build` writes `schema.json` beside `circuit.xbc`: each input's `Input::TYPE`
/// (struct definitions, `uN` widths, byte arrays), plus the public leaves in proof
/// order. `xark client` generates clients from it with no setup or proof.
#[test]
fn build_writes_input_schema() {
    let src = "#![no_std]\nuse xark::prelude::*;\n\
        #[input]\n\
        pub struct Policy { pub min: u64, pub tags: [u8; 2] }\n\
        #[circuit]\n\
        pub fn gate(secret: Private<Field>, policy: Public<Policy>, out: Public<Field>, b: Private<[u8; 3]>) {\n\
        require(secret.ge::<64>(Field::from(policy.min)));\n\
        require_eq(secret + b[0] + Field::from(policy.tags[1]), out);\n}\n";
    let c = compile_with_field(&write_case("schema_case", src), "schema_case", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let text = std::fs::read_to_string(c.out_dir.join("schema.json")).expect("schema.json");
    let schema: serde_json::Value = serde_json::from_str(&text).unwrap();
    assert_eq!(
        schema,
        serde_json::json!({
            "version": 2,
            "xark": env!("CARGO_PKG_VERSION"),
            "circuit": "gate",
            "inputs": [
                { "name": "secret", "visibility": "private", "type": "field" },
                { "name": "policy", "visibility": "public", "type": { "ref": "Policy" } },
                { "name": "out", "visibility": "public", "type": "field" },
                { "name": "b", "visibility": "private",
                  "type": { "array": { "of": { "uint": 8 }, "len": 3 } } },
            ],
            "types": {
                "Policy": { "struct": [
                    { "name": "min", "type": { "uint": 64 } },
                    { "name": "tags", "type": { "array": { "of": { "uint": 8 }, "len": 2 } } },
                ] }
            },
            "public_inputs": ["policy.min", "policy.tags[0]", "policy.tags[1]", "out"],
        })
    );
}

/// A byte input costs its entry range check and nothing more. Code in the entry shim
/// between binding the bytes and using them can make LLVM carry `[u8; 3]` packed in
/// one integer; the compiler takes such a word apart for free (see
/// `packed_words_cost_nothing`), and `xark::input::Binder` keeps it from arising.
#[test]
fn byte_inputs_are_not_repacked() {
    let src = "#![no_std]\nuse xark::prelude::*;\n\
        #[circuit]\n\
        pub fn bytes_in(msg: Private<[u8; 3]>, k: Public<Field>) {\n\
        let mut acc = Field::from(0u8);\n\
        let mut i = 0;\n\
        while i < 3 { let b = msg[i].to_bits::<8>(); acc = acc + b[0] * b[7]; i += 1; }\n\
        require_eq(acc, k);\n}\n";
    let c = compile_with_field(&write_case("bytes_in", src), "bytes_in", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    let rows = xark_ir::json::from_json(&json).unwrap().constraints.len();
    // 3 × 9 entry range checks, 3 × 9 decompositions (`to_bits` hasn't the entry's bits),
    // 3 products and the final equality. (A repacking shim once cost 105.)
    assert_eq!(rows, 58, "byte inputs cost more than their range checks");
}

/// Packing narrow values into a word (`c << 16 | b << 8 | a`) and taking it apart
/// again (`>>`, `&`, `as u8`, `/` and `%` by powers of two, a byte through memory)
/// is linear: the pieces' bits can't overlap, so OR is a sum and each piece is read
/// back off the sum. Only the inputs' range checks are constraints.
#[test]
fn packed_words_cost_nothing() {
    let src = "#![no_std]\nuse xark::prelude::*;\n\
        #[circuit]\n\
        pub fn pack(a: Private<u8>, b: Private<u8>, c: Private<u8>, out: Public<Field>) {\n\
        let w = core::hint::black_box((c as u32) << 16 | (b as u32) << 8 | a as u32);\n\
        let bytes = core::hint::black_box(w.to_le_bytes());\n\
        let (x, y, z) = ((w & 0xff) as u8, (w >> 8) as u8, (w / 65536) as u8);\n\
        let r = (w % 256) as u8;\n\
        let s = Field::from(x) + Field::from(y) * 2u64 + Field::from(z) * 4u64 + Field::from(r) * 8u64;\n\
        require_eq(s + Field::from(bytes[2]) * 16u64, out);\n}\n";
    let c = compile_with_field(&write_case("packed_words", src), "packed_words", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    let rows = xark_ir::json::from_json(&json).unwrap().constraints.len();
    // 3 × 9 entry range checks and the final equality.
    assert_eq!(rows, 28, "taking a packed word apart emitted constraints");
    let p = c.program();
    let run = |a: u64, b: u64, cc: u64| {
        let out = (a + 2 * b + 4 * cc + 8 * a + 16 * cc).to_string();
        let (a, b, cc) = (a.to_string(), b.to_string(), cc.to_string());
        solves(&p, &[("a", &a), ("b", &b), ("c", &cc), ("out", &out)])
    };
    assert!(run(1, 2, 3) && run(255, 0, 255) && run(0, 255, 7));
    assert!(!solves(
        &p,
        &[("a", "1"), ("b", "2"), ("c", "3"), ("out", "0")]
    ));
}

/// A `bool` input is a `{0, 1}` wire: it selects, converts to a `Field`, sits in a
/// derived struct, and a value other than 0 or 1 fails its entry check.
#[test]
fn bool_inputs() {
    let src = "#![no_std]\nuse xark::prelude::*;\n\
        #[input]\n\
        pub struct Gate { pub open: bool, pub level: u8 }\n\
        #[circuit]\n\
        pub fn gated(flag: Private<bool>, g: Private<Gate>, x: Private<Field>, out: Public<Field>) {\n\
        let y = if flag { x } else { x * x };\n\
        require(g.open);\n\
        require_eq(y + Field::from(flag) + Field::from(g.level), out);\n}\n";
    let c = compile_with_field(&write_case("bool_in", src), "bool_in", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let p = c.program();
    let run = |flag: &str, open: &str, out: &str| {
        solves(
            &p,
            &[
                ("flag", flag),
                ("g.open", open),
                ("g.level", "2"),
                ("x", "5"),
                ("out", out),
            ],
        )
    };
    assert!(run("1", "1", "8") && run("0", "1", "27"));
    assert!(!run("1", "0", "8"), "the gate is closed");
    assert!(!run("2", "1", "8"), "2 is not a bool");
    assert!(!run("1", "1", "9"));
}

/// `Choice::require_in` accepts exactly a declared variant that the set allows: not
/// one outside it, not a position past the enum, not a set with a bit past it, and
/// not the forged `i − 2ʷ (mod p)` that would zero a disallowed variant's factor
/// without the `w`-bit check.
#[test]
fn choice_require_in_is_sound() {
    let src = "#![no_std]\nuse xark::prelude::*;\n\
        #[input]\n\
        pub enum K { A, B, C }\n\
        #[circuit]\n\
        pub fn pick(c: Private<Choice<K>>, set: Public<Bitfield<K>>) {\n\
        c.require_in(set);\n}\n";
    let c = compile_with_field(&write_case("choice_in", src), "choice_in", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let p = c.program();
    let ok = |choice: &str, set: &str| solves(&p, &[("c", choice), ("set", set)]);
    assert!(ok("0", "1") && ok("2", "5") && ok("1", "7"));
    assert!(!ok("1", "1"), "B is not in the set of A alone");
    assert!(!ok("3", "7"), "position 3 is past the enum");
    // Three variants: the choice is checked to 2 bits, and a disallowed variant's
    // factor is offset by 2² = 4. p − 4 + 1 = p − 3 would zero B's (position 1)
    // factor mod p without that check.
    let forged = "21888242871839275222246405745257275088548364400416034343698204186575808495614";
    assert!(
        !ok(forged, "1"),
        "a forged choice must fail the 2-bit check"
    );
    assert!(!ok("4", "7"), "4 needs 3 bits");
    assert!(!ok("18446744073709551616", "7"), "2⁶⁴ is not a variant");
    // The set has one bit per variant: a bit past them isn't a set.
    assert!(!ok("0", "9"), "bit 3 names no variant");
}

/// Equality on the standard types and on derived structs: one equality constraint
/// per field element.
#[test]
fn standard_types_compare() {
    let src = "#![no_std]\nuse xark::prelude::*;\n\
        #[input]\n\
        pub struct Id { pub doc: Text, pub born: Date }\n\
        #[circuit]\n\
        pub fn same(a: Private<Id>, b: Public<Id>, c: Private<Choice<Country>>, s: Public<Bitfield<Country>>) {\n\
        require_eq(a, b);\n\
        require_eq(a.doc, b.doc);\n\
        require(c == Country::US);\n\
        require_eq(s, Bitfield::of([Country::US, Country::GB]));\n}\n";
    let c = compile_with_field(&write_case("same_types", src), "same_types", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let p = c.program();
    let us = (0..249)
        .find(|&i| <xark::Country as xark::Enum>::VARIANTS.names[i] == "US")
        .unwrap();
    let gb = (0..249)
        .find(|&i| <xark::Country as xark::Enum>::VARIANTS.names[i] == "GB")
        .unwrap();
    let set =
        (num_bigint::BigUint::from(1u8) << us | num_bigint::BigUint::from(1u8) << gb).to_string();
    let us = us.to_string();
    let run = |b_born: &str, c: &str, s: &str| {
        solves(
            &p,
            &[
                ("a.doc", "7"),
                ("a.born", "19900101"),
                ("b.doc", "7"),
                ("b.born", b_born),
                ("c", c),
                ("s", s),
            ],
        )
    };
    assert!(run("19900101", &us, &set));
    assert!(!run("19900102", &us, &set), "the structs differ");
    assert!(!run("19900101", "0", &set), "not US");
    assert!(!run("19900101", &us, "1"), "a different set");
}

/// Compile `body` as a bn254 circuit with `params` and, per case, check the
/// exhaustive search accepts exactly when `accepted` says so.
fn probe(name: &str, params: &str, body: &str, cases: &[(&[(&str, &str)], bool)]) {
    let src = format!(
        "#![no_std]\n#![allow(arithmetic_overflow, clippy::all)]\nuse xark::prelude::*;\n\
         pub fn circuit({params}) {{\n{body}\n}}\n"
    );
    let c = compile_with_field(&write_case(name, &src), name, "bn254");
    assert!(c.status_success, "{name}: {}", c.stderr);
    for &(inputs, want) in cases {
        assert_eq!(accepts_exactly(&c, inputs), want, "{name} {inputs:?}");
    }
}

/// A `witness_begin()`/`witness_end()` region emits no constraints, so nothing it
/// computes may be remembered as proven: redoing the same bit decomposition, select,
/// AND, XOR or bounded subtraction after the region must constrain it afresh.
#[test]
fn witness_regions_leave_no_proven_facts() {
    probe(
        "wo_bits",
        "x: Private<Field>, out: Public<Field>",
        "witness_begin();\nlet _ = core::hint::black_box(x.to_bits::<8>());\nwitness_end();\n\
         let b = x.to_bits::<8>();\nrequire_eq(b[0] + b[1] * 2u64 + b[2] * 4u64, out);",
        &[
            (&[("x", "5"), ("out", "5")], true),
            (&[("x", "5"), ("out", "4")], false),
            (&[("x", "300"), ("out", "4")], false),
        ],
    );
    probe(
        "wo_mux",
        "c: Private<Field>, x: Private<Field>, y: Private<Field>, out: Public<Field>",
        "witness_begin();\nlet r = if c == 1u64 { x } else { y };\n\
         let _ = core::hint::black_box(r * r);\nwitness_end();\n\
         let r2 = if c == 1u64 { x } else { y };\nrequire_eq(r2, out);",
        &[
            (&[("c", "1"), ("x", "5"), ("y", "7"), ("out", "5")], true),
            (&[("c", "1"), ("x", "5"), ("y", "7"), ("out", "7")], false),
            (&[("c", "0"), ("x", "5"), ("y", "7"), ("out", "7")], true),
        ],
    );
    probe(
        "wo_and",
        "a: Private<u32>, b: Private<u32>, k: Private<u32>, out: Public<Field>",
        "witness_begin();\ncore::hint::black_box(a & b);\nwitness_end();\n\
         require_eq(Field::from(a & k), out);",
        &[
            (&[("a", "3"), ("b", "6"), ("k", "1"), ("out", "1")], true),
            (&[("a", "3"), ("b", "6"), ("k", "1"), ("out", "0")], false),
        ],
    );
    probe(
        "wo_xor",
        "x: Private<Field>, y: Private<Field>, out: Public<Field>",
        "let a = x.to_bits::<1>()[0];\nlet b = y.to_bits::<1>()[0];\n\
         witness_begin();\nlet c = core::hint::black_box(a ^ b);\nwitness_end();\n\
         let d = (a ^ b).to_bits::<1>()[0];\nlet _ = c;\nrequire_eq(d, out);",
        &[
            (&[("x", "1"), ("y", "0"), ("out", "1")], true),
            (&[("x", "1"), ("y", "0"), ("out", "0")], false),
            (&[("x", "1"), ("y", "1"), ("out", "0")], true),
        ],
    );
    probe(
        "wo_bound",
        "x: Private<u64>, out: Public<Field>",
        "witness_begin();\ncore::hint::black_box(1u64 - x);\nwitness_end();\n\
         require_eq(Field::from(x.wrapping_mul(1 << 40)), out);",
        &[
            (&[("x", "1"), ("out", "1099511627776")], true),
            (&[("x", "1073741825"), ("out", "1099511627776")], true),
            (
                &[("x", "1073741825"), ("out", "1180591620717411303424")],
                false,
            ),
        ],
    );
}

/// Memory reached through a select of pointers: a `memory.copy` from a nested
/// select, an unaligned store whose two possible targets overlap, and a
/// sign-extending byte load of a select with a negative constant arm.
#[test]
fn memory_through_pointer_selects() {
    probe(
        "copy_nested_select",
        "m: Private<u64>, n: Private<u64>, out: Public<Field>",
        "let a = [1u64; 64];\nlet b = [2u64; 64];\nlet c = [3u64; 64];\nlet mut d = [0u64; 64];\n\
         let p: &[u64; 64] = if m == 1 { if n == 1 { &a } else { &b } } else { &c };\n\
         d.copy_from_slice(core::hint::black_box(p));\ncore::hint::black_box(&mut d);\n\
         require_eq(Field::from(d[0] + d[63]), out);",
        &[
            (&[("m", "1"), ("n", "1"), ("out", "2")], true),
            (&[("m", "1"), ("n", "1"), ("out", "0")], false),
            (&[("m", "1"), ("n", "0"), ("out", "4")], true),
            (&[("m", "0"), ("n", "1"), ("out", "6")], true),
        ],
    );
    probe(
        "store_overlapping_select",
        "c: Private<u64>, x: Private<u64>, out: Public<Field>",
        "let mut buf = [0u8; 16];\nlet i = if c == 1 { 0 } else { 4 };\n\
         unsafe { core::ptr::write_unaligned(buf.as_mut_ptr().add(i) as *mut u64, x) };\n\
         let buf = core::hint::black_box(buf);\n\
         let v = u32::from_le_bytes([buf[4], buf[5], buf[6], buf[7]]);\n\
         require_eq(Field::from(v), out);",
        &[
            (
                &[
                    ("c", "1"),
                    ("x", "1234605616436508552"),
                    ("out", "287454020"),
                ],
                true,
            ),
            (
                &[("c", "1"), ("x", "1234605616436508552"), ("out", "0")],
                false,
            ),
            (
                &[
                    ("c", "0"),
                    ("x", "1234605616436508552"),
                    ("out", "1432778632"),
                ],
                true,
            ),
        ],
    );
    probe(
        "sext_load_select",
        "c: Private<u64>, y: Private<u32>, out: Public<Field>",
        "#[inline(never)]\nfn first(a: &[i8; 4]) -> i32 { a[0] as i32 }\n\
         let arr: [i8; 4] = [if c == 1 { -128 } else { 5 }, 0, 0, 0];\n\
         let v = first(core::hint::black_box(&arr));\n\
         require_eq(Field::from((v as u32) ^ y), out);",
        &[
            (&[("c", "1"), ("y", "0"), ("out", "4294967168")], true),
            (&[("c", "1"), ("y", "0"), ("out", "0")], false),
            (&[("c", "0"), ("y", "1"), ("out", "4")], true),
        ],
    );
}

/// `mod_neg` at full width (4 × 64 bits, secp256k1's `p`): `b = k·Fr` (k = 1..5, all
/// `< p`) recomposes to `p` in the field, which once made `out = m` misfire and return
/// non-canonical limbs. Every case must give exactly `(p − b) mod p`, canonical.
#[test]
fn mod_neg_full_width() {
    use num_bigint::BigUint;
    let p = BigUint::parse_bytes(
        b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
        16,
    )
    .unwrap();
    let fr = BigUint::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
        10,
    )
    .unwrap();
    let src = format!(
        "#![no_std]\nuse xark::prelude::*;\nuse xark_bignum::*;\n\
         const MM: [Field; 4] = modulus_limbs::<4, 64>(\"{p}\");\n\
         #[circuit]\n\
         pub fn circuit(a: Private<Bignum<4, 64>>, s: Public<Bignum<4, 64>>) {{\n\
         \x20   range_check_limbs::<4, 64>(a.limbs);\n\
         \x20   let r = mod_neg::<4, 64>(a.limbs, MM);\n\
         \x20   let mut i = 0;\n\
         \x20   while i < 4 {{ require_eq(r[i], s.limbs[i]); i += 1; }}\n\
         }}\n"
    );
    let c = compile_with_field(&write_case("mod_neg_full", &src), "mod_neg_full", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let limbs = |x: &BigUint, n: &str| -> Vec<(String, String)> {
        (0..4)
            .map(|i| {
                let l: BigUint = (x >> (64 * i)) & BigUint::from(u64::MAX);
                (format!("{n}.limbs[{i}]"), l.to_string())
            })
            .collect()
    };
    let mut bs: Vec<BigUint> = (1u32..=5).map(|k| &fr * k).collect();
    bs.extend([BigUint::from(0u8), BigUint::from(1u8), p.clone(), &p - 1u8]);
    for b in bs {
        assert!(b <= p);
        let want = (&p - &b) % &p;
        for (s, ok) in [(want.clone(), true), ((&want + 1u8) % &p, false)] {
            let named: Vec<_> = limbs(&b, "a").into_iter().chain(limbs(&s, "s")).collect();
            let refs: Vec<(&str, &str)> = named
                .iter()
                .map(|(n, v)| (n.as_str(), v.as_str()))
                .collect();
            assert_eq!(accepts_best_effort(&c, &refs), ok, "b = {b}, s = {s}");
        }
    }
}

/// A loop whose length is a witness bounded by its width (`0..(a & 3)`) unrolls: once
/// the counter passes the bound's proven width the exit test is decided. An unbounded
/// one (`0..(a & 255)` nests one witness branch per iteration) is refused with a
/// diagnostic — it once overflowed the frontend's stack.
#[test]
fn witness_bounded_loops() {
    let body = "let n = (a & 3) as usize;\nlet mut s = 0u32;\n\
                for i in 0..n { s += core::hint::black_box(i as u32 * 5 + 1); }\n\
                require_eq(Field::from(s), o);";
    let cases: Vec<(String, String, bool)> = (0u32..8)
        .flat_map(|a| {
            let want: u32 = (0..(a & 3)).map(|i| i * 5 + 1).sum();
            [
                (a.to_string(), want.to_string(), true),
                (a.to_string(), (want + 1).to_string(), false),
            ]
        })
        .collect();
    let refs: Vec<([(&str, &str); 2], bool)> = cases
        .iter()
        .map(|(a, o, ok)| ([("a", a.as_str()), ("o", o.as_str())], *ok))
        .collect();
    let cases: Vec<(&[(&str, &str)], bool)> = refs.iter().map(|(x, ok)| (&x[..], *ok)).collect();
    probe(
        "bounded_loop",
        "a: Private<u32>, o: Public<Field>",
        body,
        &cases,
    );
    let src = "#![no_std]\nuse xark::prelude::*;\npub fn circuit(a: Private<u32>, o: Public<Field>) {\n\
               let n = (a & 255) as usize;\nlet mut s = 0u32;\n\
               for i in 0..n { s += core::hint::black_box(i as u32); }\nrequire_eq(Field::from(s), o);\n}\n";
    let c = compile_with_field(
        &write_case("unbounded_loop", src),
        "unbounded_loop",
        "bn254",
    );
    assert!(!c.status_success);
    assert!(c.stderr.contains("nest too deeply"), "{}", c.stderr);
}

/// **The signature circuits' building blocks, searched at full size.** The ECDSA and
/// EdDSA circuits (1.6M–3.4M rows) are too big to search whole, so each block they
/// are built from is searched exhaustively on its own, at the real field sizes,
/// against a native reference: the ed25519 extended add and double (the output is
/// determined by the inputs), `on_curve` (accepts exactly the canonical points on
/// the curve), `eq_mod_p`, the 16-way point muxes, the scalar range checks
/// (ed25519 `S < L`, secp `assert_canonical`), `scalar_to_bits` and `Fq::reduce`
/// with the real secp256k1 / secp256r1 orders. The blocks left out need a
/// non-native inverse or modular product (the incomplete-affine add and double,
/// `enforce_on_curve`, `mod_mul`), which search can't decide at 256 bits; those are
/// checked over small fields (`small_field_curve_gadgets_are_sound`,
/// `small_field_bignum_gadgets_are_sound`) and proven in Lean.
#[test]
fn signature_blocks_are_sound() {
    use num_bigint::BigInt;
    use xark_ir::witness_search::{
        Projection, WitnessSearch, search_projection, search_witnesses_within,
    };
    let big = |s: &str| BigInt::parse_bytes(s.as_bytes(), 10).unwrap();
    let hex = |s: &str| BigInt::parse_bytes(s.as_bytes(), 16).unwrap();
    let one = BigInt::from(1);
    let limbs = |v: &BigInt, n: usize, w: u32| -> Vec<BigInt> {
        let mask = (BigInt::from(1) << w) - 1;
        (0..n).map(|i| (v >> (w * i as u32)) & &mask).collect()
    };
    let value = |ls: &[BigInt], w: u32| {
        ls.iter()
            .enumerate()
            .fold(BigInt::from(0), |a, (i, l)| a + (l << (w * i as u32)))
    };
    let mut seed = 0x51f1_5eed_0bad_cafeu64;
    let mut rand_bits = move |bits: u32| -> BigInt {
        let mut x = BigInt::from(0);
        for _ in 0..bits.div_ceil(64) {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            x = (x << 64) | BigInt::from(seed);
        }
        x & ((BigInt::from(1) << bits) - 1)
    };
    // One circuit per block: `params` and `body` in a `#[circuit]`.
    let build = |name: &str, params: &str, body: &str| {
        let src = format!(
            "#![no_std]\nuse xark::prelude::*;\nuse xark_bignum::*;\n#[circuit]\n\
             pub fn circuit({params}) {{\n{body}\n}}\n"
        );
        let name = format!("blocks_{name}");
        let c = compile_with_field(&write_case(&name, &src), &name, "bn254");
        assert!(c.status_success, "{name}: {}", c.stderr);
        c.program()
    };
    let ids = |prog: &xark_ir::primitive::PrimitiveProgram, arr: &str, n: usize| -> Vec<u32> {
        (0..n)
            .map(|i| {
                let nm = format!("{arr}[{i}]");
                prog.vars
                    .iter()
                    .find(|v| v.name == nm)
                    .unwrap_or_else(|| panic!("no leaf `{nm}`"))
                    .id
            })
            .collect()
    };
    let fix = |m: &mut std::collections::BTreeMap<u32, String>, ids: &[u32], vals: &[BigInt]| {
        for (id, v) in ids.iter().zip(vals) {
            m.insert(*id, v.to_string());
        }
    };
    let limit = Some(std::time::Duration::from_secs(120));
    // A function block: the output must be determined, and equal `want` when given.
    let project = |prog: &xark_ir::primitive::PrimitiveProgram,
                   fixed: &std::collections::BTreeMap<u32, String>,
                   out: &[u32]|
     -> Option<Vec<BigInt>> {
        match search_projection(prog, fixed, out, 1 << 12, limit).unwrap() {
            Projection::One(v) => Some(v.iter().map(|x| big(&x.to_decimal())).collect()),
            Projection::None => None,
            other => panic!("not determined: {other:?}"),
        }
    };
    // A check block: accepted (exactly one witness) or rejected (none).
    let accepts = |prog: &xark_ir::primitive::PrimitiveProgram,
                   fixed: &std::collections::BTreeMap<u32, String>|
     -> bool {
        match search_witnesses_within(prog, fixed, 1 << 12, limit).unwrap() {
            WitnessSearch::Unique(_) => true,
            WitnessSearch::None => false,
            other => panic!("not decided: {other:?}"),
        }
    };

    // ---- ed25519: 3 × 85-bit limbs mod p = 2²⁵⁵ − 19 ----
    let p = (BigInt::from(1) << 255) - 19;
    let md = |x: BigInt| ((x % &p) + &p) % &p;
    let inv = |x: &BigInt| x.modpow(&(&p - 2), &p);
    let d = md(big("-121665") * inv(&big("121666")));
    let ed_add = |a: &(BigInt, BigInt), b: &(BigInt, BigInt)| {
        let t = md(&d * &a.0 * &b.0 * &a.1 * &b.1);
        (
            md((&a.0 * &b.1 + &a.1 * &b.0) * inv(&md(&one + &t))),
            md((&a.1 * &b.1 + &a.0 * &b.0) * inv(&md(&one - &t))),
        )
    };
    let base = (
        big("15112221349535400772501151409588531511454012693041857206046113283949847762202"),
        big("46316835694926478169428394003475163141307993866256225615783033603165251855960"),
    );
    let mut pts = vec![(BigInt::from(0), one.clone()), base.clone()];
    for _ in 0..3 {
        let next = ed_add(pts.last().unwrap(), &base);
        pts.push(next);
    }
    let on_curve = |x: &BigInt, y: &BigInt| {
        x < &p && y < &p && md(y * y - x * x) == md(&one + &d * x * x * y * y)
    };

    // Extended add and double: the 12 output limbs are determined by the inputs.
    let ext = |pt: &(BigInt, BigInt)| -> Vec<BigInt> {
        let t = md(&pt.0 * &pt.1);
        [&pt.0, &pt.1, &one, &t]
            .iter()
            .flat_map(|v| limbs(v, 3, 85))
            .collect()
    };
    for (k, call) in [
        "ext_add_25519(a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3])",
        "ext_double_25519(a[0], a[1], a[2])",
    ]
    .iter()
    .enumerate()
    {
        let prog = build(
            &format!("ext_{k}"),
            "pf: Private<[Field; 12]>, qf: Private<[Field; 12]>, s: Public<[Field; 12]>",
            &format!(
                "    let a = [[pf[0], pf[1], pf[2]], [pf[3], pf[4], pf[5]], [pf[6], pf[7], pf[8]], [pf[9], pf[10], pf[11]]];\n\
                 \x20   let b = [[qf[0], qf[1], qf[2]], [qf[3], qf[4], qf[5]], [qf[6], qf[7], qf[8]], [qf[9], qf[10], qf[11]]];\n\
                 \x20   let _ = b;\n\
                 \x20   let (r0, r1, r2, r3) = {call};\n\
                 \x20   let r = [r0, r1, r2, r3];\n\
                 \x20   let mut i = 0;\n\
                 \x20   while i < 12 {{ require_eq(r[i / 3][i % 3], s[i]); i += 1; }}"
            ),
        );
        let (pa, qa, out) = (
            ids(&prog, "pf", 12),
            ids(&prog, "qf", 12),
            ids(&prog, "s", 12),
        );
        for t in 0..6 {
            let (a, b): (Vec<BigInt>, Vec<BigInt>) = if t < 3 {
                (ext(&pts[t + 1]), ext(&pts[t + 2]))
            } else {
                (
                    (0..12).map(|_| rand_bits(85)).collect(),
                    (0..12).map(|_| rand_bits(85)).collect(),
                )
            };
            let mut m = Default::default();
            fix(&mut m, &pa, &a);
            fix(&mut m, &qa, &b);
            assert!(
                project(&prog, &m, &out).is_some(),
                "{call}: no output for {a:?} {b:?}"
            );
        }
    }

    // on_curve: accepts exactly the canonical points on the curve.
    let prog = build(
        "ed_on_curve",
        "x: Private<[Field; 3]>, y: Private<[Field; 3]>",
        "    xark_ed25519::blocks::on_curve(x, y);",
    );
    let (xs, ys) = (ids(&prog, "x", 3), ids(&prog, "y", 3));
    let mut samples: Vec<(BigInt, BigInt)> = pts.clone();
    samples.push((p.clone(), one.clone())); // (0, 1) with x encoded as p
    samples.push((BigInt::from(0), &one + &p)); // … and y as 1 + p
    samples.push((base.0.clone(), &base.1 + 1)); // off the curve
    samples.push((rand_bits(255), rand_bits(255)));
    for (x, y) in &samples {
        let mut m = Default::default();
        fix(&mut m, &xs, &limbs(x, 3, 85));
        fix(&mut m, &ys, &limbs(y, 3, 85));
        assert_eq!(accepts(&prog, &m), on_curve(x, y), "on_curve({x}, {y})");
    }

    // eq_mod_p: accepts exactly u ≡ v (mod p).
    let prog = build(
        "ed_eq_mod_p",
        "u: Private<[Field; 3]>, v: Private<[Field; 3]>",
        "    xark_ed25519::blocks::eq_mod_p(u, v);",
    );
    let (us, vs) = (ids(&prog, "u", 3), ids(&prog, "v", 3));
    let r = rand_bits(254);
    for (u, v) in [
        (r.clone(), r.clone()),
        (BigInt::from(5), BigInt::from(5) + &p),
        (r.clone(), &r + 1),
        (BigInt::from(0), p.clone()),
        (rand_bits(255), rand_bits(255)),
    ] {
        let mut m = Default::default();
        fix(&mut m, &us, &limbs(&u, 3, 85));
        fix(&mut m, &vs, &limbs(&v, 3, 85));
        assert_eq!(
            accepts(&prog, &m),
            md(&u - &v) == BigInt::from(0),
            "eq_mod_p({u}, {v})"
        );
    }

    // The 16-way extended-point mux picks entry `b3 b2 b1 b0`.
    let prog = build(
        "ed_select16",
        "t: Private<[Field; 192]>, b: Private<[Field; 4]>, s: Public<[Field; 12]>",
        "    let mut tab = [[[Field::from(0u8); 3]; 4]; 16];\n\
         \x20   let mut i = 0;\n\
         \x20   while i < 192 { tab[i / 12][(i % 12) / 3][i % 3] = t[i]; i += 1; }\n\
         \x20   let r = xark_ed25519::blocks::select16(tab, b[3], b[2], b[1], b[0]);\n\
         \x20   let mut i = 0;\n\
         \x20   while i < 12 { require_eq(r[i / 3][i % 3], s[i]); i += 1; }",
    );
    let (ts, bs, out) = (
        ids(&prog, "t", 192),
        ids(&prog, "b", 4),
        ids(&prog, "s", 12),
    );
    let table: Vec<BigInt> = (0..192).map(|_| rand_bits(85)).collect();
    for idx in [0usize, 5, 10, 15] {
        let mut m = Default::default();
        fix(&mut m, &ts, &table);
        let bits: Vec<BigInt> = (0..4).map(|k| BigInt::from((idx >> k) & 1)).collect();
        fix(&mut m, &bs, &bits);
        let got = project(&prog, &m, &out).expect("select16 has an output");
        assert_eq!(
            got,
            table[12 * idx..12 * idx + 12].to_vec(),
            "select16 entry {idx}"
        );
    }

    // The EdDSA scalar check: accepts exactly S < L.
    let l: BigInt = (BigInt::from(1) << 252) + big("27742317777372353535851937790883648493");
    let prog = build(
        "ed_scalar",
        "bits: Private<[Field; 256]>",
        "    xark_ed25519::blocks::scalar_below_order(bits);",
    );
    let bs = ids(&prog, "bits", 256);
    for sv in [
        BigInt::from(0),
        &l - 1,
        l.clone(),
        &l + 1,
        BigInt::from(1) << 252,
        (BigInt::from(1) << 256) - 1,
        rand_bits(252),
    ] {
        let mut m = Default::default();
        let bits: Vec<BigInt> = (0..256).map(|i| (&sv >> i) & &one).collect();
        fix(&mut m, &bs, &bits);
        assert_eq!(accepts(&prog, &m), sv < l, "scalar_below_order({sv})");
    }

    // ---- secp256k1 / secp256r1 scalars: 3 × 86-bit limbs ----
    let orders = [
        (
            "k1",
            hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
        ),
        (
            "r1",
            hex("FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551"),
        ),
    ];

    // scalar_to_bits: the 256 bits are determined and are the value's binary
    // expansion; a limb past its width has no witness.
    let prog = build(
        "scalar_to_bits",
        "u: Private<[Field; 3]>, s: Public<[Field; 256]>",
        "    let r = scalar_to_bits(u);\n\
         \x20   let mut i = 0;\n\
         \x20   while i < 256 { require_eq(r[i], s[i]); i += 1; }",
    );
    let (us, out) = (ids(&prog, "u", 3), ids(&prog, "s", 256));
    for v in [
        BigInt::from(0),
        (BigInt::from(1) << 256) - 1,
        rand_bits(256),
        rand_bits(256),
    ] {
        let mut m = Default::default();
        fix(&mut m, &us, &limbs(&v, 3, 86));
        let got = project(&prog, &m, &out).expect("scalar_to_bits has an output");
        let want: Vec<BigInt> = (0..256).map(|i| (&v >> i) & &one).collect();
        assert_eq!(got, want, "scalar_to_bits({v})");
    }
    for bad in [
        vec![BigInt::from(1) << 86, BigInt::from(0), BigInt::from(0)],
        vec![BigInt::from(0), BigInt::from(0), BigInt::from(1) << 84],
    ] {
        let mut m = Default::default();
        fix(&mut m, &us, &bad);
        assert!(
            project(&prog, &m, &out).is_none(),
            "scalar_to_bits({bad:?}) out of range"
        );
    }

    // The 16-way affine mux.
    let prog = build(
        "select16_affine",
        "t: Private<[Field; 96]>, b: Private<[Field; 4]>, s: Public<[Field; 6]>",
        "    let mut tab = [[[Field::from(0u8); 3]; 2]; 16];\n\
         \x20   let mut i = 0;\n\
         \x20   while i < 96 { tab[i / 6][(i % 6) / 3][i % 3] = t[i]; i += 1; }\n\
         \x20   let r = select16_affine(tab, b[3], b[2], b[1], b[0]);\n\
         \x20   let mut i = 0;\n\
         \x20   while i < 6 { require_eq(r[i / 3][i % 3], s[i]); i += 1; }",
    );
    let (ts, bs, out) = (ids(&prog, "t", 96), ids(&prog, "b", 4), ids(&prog, "s", 6));
    let table: Vec<BigInt> = (0..96).map(|_| rand_bits(86)).collect();
    for idx in [0usize, 6, 9, 15] {
        let mut m = Default::default();
        fix(&mut m, &ts, &table);
        let bits: Vec<BigInt> = (0..4).map(|k| BigInt::from((idx >> k) & 1)).collect();
        fix(&mut m, &bs, &bits);
        let got = project(&prog, &m, &out).expect("select16_affine has an output");
        assert_eq!(
            got,
            table[6 * idx..6 * idx + 6].to_vec(),
            "select16_affine entry {idx}"
        );
    }

    for (curve, n) in &orders {
        let ty = format!("xark_secp256{curve}::affine::Fq");
        // assert_canonical: accepts exactly limbs in range and a value < n.
        let prog = build(
            &format!("canonical_{curve}"),
            "u: Private<[Field; 3]>",
            &format!("    {ty}::new(u).assert_canonical();"),
        );
        let us = ids(&prog, "u", 3);
        for v in [
            BigInt::from(0),
            n - 1,
            n.clone(),
            n + 1,
            (BigInt::from(1) << 256) - 1,
            rand_bits(255),
        ] {
            let mut m = Default::default();
            fix(&mut m, &us, &limbs(&v, 3, 86));
            assert_eq!(accepts(&prog, &m), &v < n, "{curve} assert_canonical({v})");
        }
        // reduce: a value < 2n maps to the canonical value mod n.
        let prog = build(
            &format!("reduce_{curve}"),
            "u: Private<[Field; 3]>, s: Public<[Field; 3]>",
            &format!(
                "    let r = {ty}::new(u).reduce();\n\
                 \x20   let mut i = 0;\n\
                 \x20   while i < 3 {{ require_eq(r.limbs[i], s[i]); i += 1; }}"
            ),
        );
        let (us, out) = (ids(&prog, "u", 3), ids(&prog, "s", 3));
        for v in [BigInt::from(0), n - 1, n.clone(), 2 * n - 1, rand_bits(255)] {
            let mut m = Default::default();
            fix(&mut m, &us, &limbs(&v, 3, 86));
            let got = project(&prog, &m, &out).expect("reduce has an output");
            assert_eq!(value(&got, 86), &v % n, "{curve} reduce({v})");
        }
    }
}

/// **The AES circuits' building blocks, searched whole.** The CTR / GCM / AES-256
/// examples (300k–1M rows) are too big to search, but they are built from the AES
/// block (searched through the `aes` example) plus these two: the AES-256 block
/// (the FIPS-197 C.3 vector: the ciphertext is determined and correct) and the GHASH
/// multiply `gf128_mul` (the product is determined by its inputs; its values are
/// checked by the GCM known-answer tests).
#[test]
fn aes_blocks_are_sound() {
    use xark_ir::witness_search::{Projection, search_projection};
    let limit = Some(std::time::Duration::from_secs(300));
    let leaf = |prog: &xark_ir::primitive::PrimitiveProgram, nm: String| {
        prog.vars
            .iter()
            .find(|v| v.name == nm)
            .unwrap_or_else(|| panic!("no leaf `{nm}`"))
            .id
    };
    let unhex = |s: &str| -> Vec<u8> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect()
    };

    // AES-256, FIPS-197 C.3.
    let src = write_case(
        "aes_block_256",
        "#![no_std]\nuse xark::prelude::*;\n#[circuit]\n\
         pub fn circuit(pt: Private<[Field; 16]>, key: Private<[Field; 32]>, ct: Public<[Field; 16]>) {\n\
         \x20   let r = xark_aes::aes256_encrypt_bytes(pt, key);\n\
         \x20   let mut i = 0;\n\
         \x20   while i < 16 { require_eq(r[i], ct[i]); i += 1; }\n}\n",
    );
    let c = compile_with_field(&src, "aes_block_256", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let prog = c.program();
    eprintln!("aes256 block: {} constraints", prog.constraints.len());
    let mut fixed = std::collections::BTreeMap::new();
    for (i, b) in unhex("00112233445566778899aabbccddeeff").iter().enumerate() {
        fixed.insert(leaf(&prog, format!("pt[{i}]")), b.to_string());
    }
    for (i, b) in unhex("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")
        .iter()
        .enumerate()
    {
        fixed.insert(leaf(&prog, format!("key[{i}]")), b.to_string());
    }
    let out: Vec<_> = (0..16).map(|i| leaf(&prog, format!("ct[{i}]"))).collect();
    let t = std::time::Instant::now();
    match search_projection(&prog, &fixed, &out, 1 << 12, limit).unwrap() {
        Projection::One(v) => {
            let got: Vec<u8> = v.iter().map(|x| x.to_decimal().parse().unwrap()).collect();
            assert_eq!(
                got,
                unhex("8ea2b7ca516745bfeafc49904b496089"),
                "aes256 ciphertext"
            );
        }
        other => panic!("aes256: {other:?}"),
    }
    eprintln!("  decided in {:.1?}", t.elapsed());

    // GHASH multiply: the 128 product bits are determined by the inputs.
    let src = write_case(
        "aes_gf128_mul",
        "#![no_std]\nuse xark::prelude::*;\n#[circuit]\n\
         pub fn circuit(x: Private<[Field; 128]>, y: Private<[Field; 128]>, s: Public<[Field; 128]>) {\n\
         \x20   let r = xark_aes::gf128_mul(x, y);\n\
         \x20   let mut i = 0;\n\
         \x20   while i < 128 { require_eq(r[i], s[i]); i += 1; }\n}\n",
    );
    let c = compile_with_field(&src, "aes_gf128_mul", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let prog = c.program();
    eprintln!("gf128_mul: {} constraints", prog.constraints.len());
    let out: Vec<_> = (0..128).map(|i| leaf(&prog, format!("s[{i}]"))).collect();
    let mut seed = 0x6a09_e667_f3bc_c908u64;
    for _ in 0..4 {
        let mut fixed = std::collections::BTreeMap::new();
        for arr in ["x", "y"] {
            for i in 0..128 {
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                fixed.insert(leaf(&prog, format!("{arr}[{i}]")), (seed & 1).to_string());
            }
        }
        match search_projection(&prog, &fixed, &out, 1 << 12, limit).unwrap() {
            Projection::One(v) => assert!(
                v.iter()
                    .all(|b| b.to_decimal() == "0" || b.to_decimal() == "1")
            ),
            other => panic!("gf128_mul: {other:?}"),
        }
    }
}

/// `require_eq` takes any `Into<Field>` scalar on either side: every unsigned
/// width, decimal strings, and constant/computed booleans, in both operand orders.
#[test]
fn require_eq_accepts_into_field_operands() {
    let src = "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(x: Private<Field>) {\n\
         \x20   require_eq(x, 7u8);\n\
         \x20   require_eq(7u16, x);\n\
         \x20   require_eq(x, 7u32);\n\
         \x20   require_eq(7u64, x);\n\
         \x20   require_eq(x, 7u128);\n\
         \x20   require_eq(\"7\", x);\n\
         \x20   require_eq(true, Field::from(1u8));\n\
         \x20   require_eq(Field::from(0u8), false);\n\
         \x20   require_eq(x == Field::from(7u8), true);\n\
         }\n";
    let c = compile_with_field(
        &write_case("require_eq_into", src),
        "require_eq_into",
        "bn254",
    );
    assert!(
        c.status_success,
        "Into<Field> operands should compile: {}",
        c.stderr
    );
    let program = c.program();
    assert!(solves(&program, &[("x", "7")]));
    assert!(
        !solves(&program, &[("x", "8")]),
        "the converted constants must still constrain the witness"
    );

    let signed = "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(x: Private<Field>) { require_eq(-1i64, x); }\n";
    let c = compile_with_field(
        &write_case("require_eq_signed", signed),
        "require_eq_signed",
        "bn254",
    );
    assert!(
        !c.status_success,
        "signed integers have no Into<Field> implementation"
    );
}

/// An integer on the left is the same circuit as an explicit `Field::from`.
#[test]
fn require_eq_integer_matches_explicit_conversion() {
    let digest = |name: &str, body: &str| {
        let src = format!(
            "#![no_std]\nuse xark::prelude::*;\npub fn circuit(x: Private<Field>) {{ {body} }}\n"
        );
        let c = compile_with_field(&write_case(name, &src), name, "bn254");
        assert!(c.status_success, "{name} failed: {}", c.stderr);
        c.circuit_digest()
    };
    assert_eq!(
        digest("require_eq_int_lhs", "require_eq(7u64, x);"),
        digest("require_eq_field_lhs", "require_eq(Field::from(7u64), x);"),
    );
}

/// `#[circuit]` rejects arguments rather than ignoring them: an option like
/// `max_constraints` would otherwise compile and look enforced.
#[test]
fn circuit_attribute_rejects_arguments() {
    let src = "use xark::prelude::*;\n\
         #[circuit(max_constraints = 10)]\n\
         pub fn square(x: Private<Field>, y: Public<Field>) { require_eq(x * x, y); }\n";
    let c = compile_with_field(&write_case("circuit_args", src), "circuit_args", "bn254");
    assert!(!c.status_success, "arguments to #[circuit] were accepted");
    assert!(c.stderr.contains("takes no arguments"), "{}", c.stderr);
}
