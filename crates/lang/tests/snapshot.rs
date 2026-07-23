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
    xark_test_harness::compile_file(src, out_name, field)
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

/// Native integers compare directly with literals and named constants. Constants
/// remain constants in the circuit rather than requiring a redundant public input.
#[test]
fn native_u64_literal_comparison() {
    use xark_ir::solver;
    let src = "#![no_std]\n\
        use xark::prelude::*;\n\
        const MINIMUM: u64 = 9_000;\n\
        pub fn circuit(power: Private<u64>) {\n\
        require(power > MINIMUM);\n\
        require(9_000u64 < power);\n\
        }\n";
    let c = compile_with_field(
        &write_case("native_u64_literal_cmp", src),
        "native_u64_literal_cmp",
        "bn254",
    );
    assert!(
        c.status_success,
        "native u64 literal compare failed: {}",
        c.stderr
    );
    let p = c.program();
    let power = p.vars.iter().find(|v| v.name == "power").unwrap().id;
    let inputs = |value: &str| {
        let mut values = std::collections::BTreeMap::new();
        values.insert(power, value.to_string());
        values
    };

    solver::solve_and_check(&p, &inputs("9001")).expect("9001 > 9000 must solve");
    assert!(
        solver::solve_and_check(&p, &inputs("9000")).is_err(),
        "the strict literal boundary must be rejected"
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
    let r1cs = xark_ir::json::from_json(&json).unwrap();
    assert_eq!(r1cs.constraints.len(), 241);
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
        240,
        "expected exactly 240 S-box multiplication gates"
    );

    // The relation setup/proving consume: minimization folds the capacity lane's
    // first three multiplications (its input starts constant) and substitutes the
    // final output binding — 240 - 3 = 237 multiplication constraints, no
    // standalone equalities left.
    let min = c.minimized_r1cs();
    let min_equalities = min
        .constraints
        .iter()
        .filter(|k| k.b.terms.is_empty() && k.c.terms.is_empty() && k.c.constant.is_zero())
        .count();
    assert_eq!(min.constraints.len(), 237);
    assert_eq!(
        min_equalities, 0,
        "the output binding should be substituted; ARK/MDS are free"
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
    assert_eq!(r1cs.constraints.len(), 977);
    let nonzeros: usize = r1cs
        .constraints
        .iter()
        .map(|k| k.a.terms.len() + k.b.terms.len() + k.c.terms.len())
        .sum();
    assert_eq!(nonzeros, 25_330, "depth-4 Poseidon Merkle nonzero count");

    // The relation setup/proving consume: 4 levels × (237 minimized `hash2` gates
    // [capacity lane folded] + 1 booleanity + 2 sibling muxes) = 4×240 = 960, with
    // every hash-output/root binding substituted. The nonzero pin guards LC
    // density: an accidental function-boundary materialization keeps the count
    // but fattens the substituted combinations (and the proving-side matrices).
    let min = c.minimized_r1cs();
    let min_nonzeros: usize = min
        .constraints
        .iter()
        .map(|k| k.a.terms.len() + k.b.terms.len() + k.c.terms.len())
        .sum();
    assert_eq!(min.constraints.len(), 960);
    assert_eq!(
        min_nonzeros, 25_252,
        "depth-4 Poseidon Merkle minimized nonzero count"
    );
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
    let c = compile_with_field(&example("merkle"), "merkle_lean_bridge", "bn254");
    assert!(c.status_success, "merkle gadget compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");

    let mul_gates = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();

    // 4 levels × (240 Poseidon S-box muls + 1 booleanity + 2 select muxes) = 972.
    // The shape `merkle_level_swap_sound` + `poseidon_permutation_determined` are
    // stated over. If this fails, reconcile the gadget with the Lean model.
    assert_eq!(
        mul_gates, 972,
        "depth-4 Merkle must emit 972 multiplication gates (matches \
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
/// `sha256_block` (the former `examples/sha256`).
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
/// via `keccak256_block` (the former `examples/keccak`).
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
/// 4-lane digest (the former `examples/keccak256`).
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
/// `blake3_hash_one_block` (the former `examples/blake3`), for the Lean bridge.
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
/// `blake3::<n>` (the former `examples/blake3_hash`), for the multi-block vector.
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

/// Unkeyed BLAKE2s single-block over a 16-word message → 8-word digest (the
/// former `examples/blake2s`).
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

/// Byte-oriented unkeyed BLAKE2s over an `n`-byte message → 8-word digest (the
/// former `examples/blake2s_hash`), for the multi-block real-vector bridge.
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
    assert_eq!(constraints, 39018, "SHA-256 constraint count changed");
    assert_eq!(
        json.matches("\"name\": \"w").count(),
        6568,
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
    use xark_ir::{primitive, solver};

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
    let c = compile_with_field(&path, "sha256_abc", "bn254");
    assert!(c.status_success, "sha256_abc failed: {}", c.stderr);
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
    let mut inputs = BTreeMap::new();
    for (i, v) in block.iter().enumerate() {
        inputs.insert(id(&format!("b{i}")), v.to_string());
    }
    for (i, v) in out.iter().enumerate() {
        inputs.insert(id(&format!("o{i}")), v.to_string());
    }

    // The gadget computes real SHA-256("abc") and all constraints hold.
    let assign = solver::solve_and_check(&program, &inputs).expect("SHA-256(\"abc\") must verify");

    // Soundness smoke-test: no derived variable is under-constrained.
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(
        holes.is_empty(),
        "SHA-256 has {} under-constrained vars: {:?}",
        holes.len(),
        &holes[..holes.len().min(5)]
    );

    // Negative control: a wrong digest word must violate a constraint.
    inputs.insert(id("o0"), "123456".to_string());
    assert!(solver::solve_and_check(&program, &inputs).is_err());
}

/// Correctness against a real vector: compile the Keccak-256 gadget and solve
/// its hint program on the empty-message padded block; the output must be the
/// known Ethereum `keccak256("")` digest. `#[ignore]` (large circuit, ~20s+).
#[test]
#[ignore]
fn keccak_matches_empty_vector() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};

    let c = compile_with_field(
        &write_case("keccak_empty", &keccak_block_src()),
        "keccak",
        "bn254",
    );
    assert!(c.status_success, "keccak failed: {}", c.stderr);
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

    // Empty-message padded block (little-endian lanes): words[0]=1, words[16]=2^63.
    let mut inputs = BTreeMap::new();
    for i in 0..17 {
        inputs.insert(id(&format!("words[{i}]")), "0".to_string());
    }
    inputs.insert(id("words[0]"), "1".to_string());
    inputs.insert(id("words[16]"), "9223372036854775808".to_string());
    // keccak256("") = c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
    let digest = [
        "4333579421379646149",
        "13836122230913597074",
        "4262519377828905189",
        "8116759062988257915",
    ];
    for (i, v) in digest.iter().enumerate() {
        inputs.insert(id(&format!("d[{i}]")), v.to_string());
    }
    let assign = solver::solve_and_check(&program, &inputs).expect("keccak256(\"\") must verify");

    // Soundness smoke-test: no derived variable is under-constrained (in
    // particular, every fused-XOR output and advice bit is uniquely pinned).
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(
        holes.is_empty(),
        "Keccak has {} under-constrained vars: {:?}",
        holes.len(),
        &holes[..holes.len().min(5)]
    );

    inputs.insert(id("d[0]"), "42".to_string());
    assert!(solver::solve_and_check(&program, &inputs).is_err());
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
/// `cargo test --features cli --test snapshot -- --ignored keccak256`.
#[test]
#[ignore]
fn keccak256_varlen_matches_real_vector() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};

    let c = compile_with_field(
        &write_case("keccak256_varlen", &keccak256_varlen_src()),
        "keccak256",
        "bn254",
    );
    assert!(c.status_success, "keccak256 varlen failed: {}", c.stderr);
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

    // Private message = bytes 0..200.
    let mut inputs = BTreeMap::new();
    for i in 0..200usize {
        inputs.insert(id(&format!("msg[{i}]")), i.to_string());
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
        inputs.insert(id(&format!("d[{i}]")), v.to_string());
    }

    // (1) Correctness: the sponge reproduces the genuine keccak256 digest.
    let assign =
        solver::solve_and_check(&program, &inputs).expect("keccak256(bytes(0..200)) must verify");

    // (2) Soundness: no derived variable is under-constrained.
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(
        holes.is_empty(),
        "keccak256 has {} under-constrained vars: {:?}",
        holes.len(),
        &holes[..holes.len().min(5)]
    );

    // (3) Negative control: a wrong digest word must violate a constraint.
    inputs.insert(id("d[0]"), "42".to_string());
    assert!(solver::solve_and_check(&program, &inputs).is_err());
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
    use xark_ir::{primitive, solver};

    let c = compile_with_field(&example("ec_incomplete_r1"), "ec_incomplete_r1", "bn254");
    assert!(c.status_success, "ec_incomplete_r1 failed: {}", c.stderr);
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
    let set = |m: &mut BTreeMap<u32, String>, pre: &str, v: [&str; 3]| {
        for (i, vi) in v.iter().enumerate() {
            m.insert(id(&format!("{pre}[{i}]")), vi.to_string());
        }
    };
    let mut inputs = BTreeMap::new();
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

    let assign = solver::solve_and_check(&program, &inputs).expect("r1 3-limb 2G/3G must verify");
    assert!(solver::analyze_underconstrained(&program, &assign).is_empty());
    inputs.insert(id("two_g.y.limbs[0]"), "7".to_string());
    assert!(solver::solve_and_check(&program, &inputs).is_err());
}

/// Validate the 3-limb (86-bit) incomplete EC ops: `2G` and `3G` from `G`.
/// Exercises the whole 3-limb field stack (add/sub/mul/inverse), analyzer-clean.
#[test]
#[ignore]
fn ec_incomplete_matches_vectors() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};

    let c = compile_with_field(&example("ec_incomplete"), "ec_incomplete", "bn254");
    assert!(c.status_success, "ec_incomplete failed: {}", c.stderr);
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
    let set = |m: &mut BTreeMap<u32, String>, pre: &str, v: [&str; 3]| {
        for (i, vi) in v.iter().enumerate() {
            m.insert(id(&format!("{pre}[{i}]")), vi.to_string());
        }
    };
    let mut inputs = BTreeMap::new();
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

    let assign = solver::solve_and_check(&program, &inputs).expect("3-limb 2G/3G must verify");
    assert!(solver::analyze_underconstrained(&program, &assign).is_empty());
    inputs.insert(id("two_g.x.limbs[0]"), "1".to_string());
    assert!(solver::solve_and_check(&program, &inputs).is_err());
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

/// A `for` over anything but a constant integer range or a fixed-size array is
/// rejected with a clear diagnostic — never an ICE. A range iterator adapter
/// (`.rev()`) gets the specific "only `for` over a constant integer range"
/// message; a slice iterator (`.iter()`, which needs an unsize coercion the
/// circuit can't lower) is also cleanly rejected.
#[test]
fn for_over_unsupported_iterator_is_rejected() {
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

    // `.rev()` reaches our range modeling and gets the specific message.
    let rev = compile(
        &mk(
            "for_reject_rev",
            "for _i in (0..2).rev() { acc = acc * a; }",
        ),
        "for_reject_rev",
    );
    assert!(!rev.status_success, "a range adapter must be rejected");
    assert!(
        rev.stderr
            .contains("only `for` over a constant integer range is supported"),
        "{}",
        rev.stderr
    );

    // `.iter()` is rejected too (cleanly — no ICE).
    let it = compile(
        &mk("for_reject_iter", "for x in arr.iter() { acc = acc + *x; }"),
        "for_reject_iter",
    );
    assert!(!it.status_success, "a slice iterator must be rejected");
    assert!(
        it.stderr.contains("error:") && !it.stderr.contains("panicked"),
        "expected a clean rejection, got: {}",
        it.stderr
    );
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
    let c = compile_with_field(&example("poseidon2"), "poseidon2_lean_bridge", "bn254");
    assert!(c.status_success, "poseidon2 gadget compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");

    let mul_gates = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();

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
    let c = compile_with_field(
        &write_case("sha256_lean", &sha256_block_src()),
        "sha256_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "sha256 gadget compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();
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
    assert_eq!(
        mul, 35158,
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
    let c = compile_with_field(
        &write_case("blake3_lean", &blake3_block_src()),
        "blake3_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "blake3 gadget compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();
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
    let c = compile_with_field(
        &write_case("blake2s_lean", &blake2s_block_src()),
        "blake2s_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "blake2s gadget compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();
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
    let c = compile_with_field(
        &write_case("keccak_lean", &keccak_block_src()),
        "keccak_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "keccak gadget compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();
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
    let c = compile_with_field(&example("aes"), "aes_lean_bridge", "bn254");
    assert!(c.status_success, "aes gadget compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();
    assert_eq!(mul, 145816, "AES-128 mult-gate count; got {mul}");
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
    let c = compile_with_field(
        &write_case("aes256_lean", src),
        "aes256_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "aes256 gadget compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();
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
    let c = compile_with_field(&write_case("gf128_lean", src), "gf128_lean_bridge", "bn254");
    assert!(c.status_success, "gf128_mul gadget compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();
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
    let c = compile_with_field(&example("aes_gcm"), "aes_gcm_lean_bridge", "bn254");
    assert!(c.status_success, "aes_gcm gadget compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();
    assert_eq!(mul, 715240, "AES-128-GCM mult-gate count; got {mul}");
}

/// **R1CS ↔ Lean bridge (secp256k1 non-native field multiply).**
/// `NonNative.lean`'s `mul_mod_via_Fr_limbwise_constraints_3` proves the 3-limb
/// 86-bit modular-product constraints sound (`c = a·b mod m`). Pins the
/// `mod_mul` / `fp_mul` gadget's constraint shape.
#[test]
fn fp_mul_matches_lean_model() {
    let c = compile_with_field(&example("fp_mul"), "fp_mul_lean_bridge", "bn254");
    assert!(c.status_success, "fp_mul compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();
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
    let c = compile_with_field(
        &example("ec_incomplete"),
        "ec_incomplete_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "ec_incomplete compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();
    assert_eq!(
        mul, 15369,
        "ec_incomplete mult-gate count pins ec_add_incomplete_secp256k1_sound; got {mul}"
    );
}

/// **R1CS ↔ Lean bridge (secp256r1/P-256 incomplete point-add).**
/// `Secp256r1.lean`'s `ec_add_incomplete_secp256r1_sound` (same shape at `a=−3`).
#[test]
fn ec_incomplete_r1_matches_lean_model() {
    let c = compile_with_field(
        &example("ec_incomplete_r1"),
        "ec_incomplete_r1_lean_bridge",
        "bn254",
    );
    assert!(c.status_success, "ec_incomplete_r1 compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul = r1cs
        .constraints
        .iter()
        .filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty())
        .count();
    assert_eq!(
        mul, 15891,
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
         let big = Field::from(\"21888242871839275222246405745257275088548364400416034343698204186575808495617\");\n\
         let two: Field = \"2\".into();\n\
         require_eq(a * two + big, b);\n}\n",
    );
    let c = compile(&src, "from_str");
    assert!(c.status_success, "from_str compiles: {}", c.stderr);
    let r1cs = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    assert!(
        r1cs.contains(
            "21888242871839275222246405745257275088548364400416034343698204186575808495617"
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
        c.stderr.contains("non-numeric character 'a'"),
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

/// Compound assignment (`+=`, …) is rejected in-circuit (write `acc = acc + b`).
#[test]
fn rejects_compound_assign() {
    let src = write_case(
        "field_assign",
        "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, b: Public<Field>) {\n\
         \x20   let mut acc = a;\n\
         \x20   acc += b;\n\
         \x20   require_eq(acc, b);\n\
         }\n",
    );
    let c = compile(&src, "reject_assign");
    assert!(
        !c.status_success,
        "compound assignment should be rejected in a circuit"
    );
    assert!(
        c.stderr.contains("not supported inside a circuit"),
        "unexpected error: {}",
        c.stderr
    );
}

/// `==` on `Field` is now a circuit operation (yields a `bool` wire); what is
/// rejected is branching on that witness-dependent bool.
#[test]
fn rejects_field_comparison() {
    let src = write_case(
        "field_cmp",
        "#![no_std]\nuse xark::{require_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, b: Public<Field>) {\n\
         \x20   if a == b { require_eq(a, b); }\n\
         }\n",
    );
    let c = compile(&src, "reject_cmp");
    assert!(
        !c.status_success,
        "branching on a witness comparison should have been rejected"
    );
    assert!(
        c.stderr.contains("conditional arm ends with")
            || c.stderr.contains("unsupported operation"),
        "unexpected error: {}",
        c.stderr
    );
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
