//! Integration tests: compile the workspace examples and compare their emitted
//! `r1cs.json` / `graph.dot` against committed snapshots. Also exercises the
//! rejection diagnostics for unsupported inputs.
//!
//! Set `UPDATE_SNAPSHOTS=1` to overwrite the snapshot files with fresh output.

use std::path::{Path, PathBuf};

use xark_test_harness::Compiled;

fn workspace_root() -> PathBuf {
    // CARGO_MANIFEST_DIR = <root>/crates/xark
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
    let expected = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("missing snapshot {path:?}: {e}"));
    assert_eq!(
        expected, actual,
        "snapshot mismatch for {snapshot_rel}; run with UPDATE_SNAPSHOTS=1 to refresh"
    );
}

fn example(name: &str) -> PathBuf {
    workspace_root().join("examples").join(name).join("src/lib.rs")
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
    assert!(!json.contains("\"name\": \"t0\""), "unexpected mul gate in linear circuit");
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
    assert!(json.contains("7120861356467033611736373842526102177239622603558704633600844922174959859415"));
    // bn254 modulus recorded.
    assert!(json.contains("21888242871839275222246405745257275088548364400416034343698204186575808495617"));
}

/// The `xark-mimc` gadget crate is inlined across the crate boundary and yields
/// exactly the same R1CS as the hand-unrolled `mimc` example.
#[test]
fn mimc_gadget_matches_snapshot_and_inline() {
    let c = compile_with_field(&example("mimc_gadget"), "mimc_gadget", "bn254");
    assert!(c.status_success, "mimc_gadget failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    let dot = std::fs::read_to_string(c.out_dir.join("graph.dot")).unwrap();
    check_snapshot("mimc_gadget.r1cs.json", &json);
    check_snapshot("mimc_gadget.graph.dot", &dot);

    // Same constraint structure as the inline hand-unrolled version.
    let inline = compile_with_field(&example("mimc"), "mimc_cmp", "bn254");
    let inline_json = std::fs::read_to_string(inline.out_dir.join("r1cs.json")).unwrap();
    assert_eq!(json, inline_json, "gadget crate must lower identically to inline mimc");
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
    assert!(json.contains("\"name\": \"w0\""), "missing advice var: {json}");
    assert!(json.contains("\"note\": \"x * w0 = 1\""), "unexpected R1CS: {json}");
    assert_eq!(json.matches("\"source_span\"").count(), 2);
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

    assert_eq!(looped, unrolled, "loop+array MiMC must match the hand-unrolled version");
    assert_eq!(looped.matches("\"source_span\"").count(), 7);
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
        assert!(json.contains(&format!("\"name\": \"w{i}\"")), "missing advice bit w{i}");
    }
    // 8 booleanity gates + 1 recomposition + 2 demo equalities.
    assert_eq!(json.matches("\"source_span\"").count(), 11);
    // Recomposition folds bits into a linear combination (no gate): the note is a
    // `(...) * 1 = 0` equality carrying all 8 power-of-two coefficients.
    assert!(json.contains("128*w7"), "recomposition coefficients missing: {json}");
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

    // R_F=4 full (9 gates each) + R_P=2 partial (3 gates each) = 42 S-box gates,
    // plus 1 final `assert_eq` equality = 43 constraints.
    assert_eq!(json.matches("\"source_span\"").count(), 43);
    let notes: Vec<&str> = json.lines().filter(|l| l.contains("\"note\"")).collect();
    let equalities = notes.iter().filter(|n| n.contains("* 1 = 0")).count();
    assert_eq!(equalities, 1, "only the output binding should be an equality; ARK/MDS are free");
    assert_eq!(notes.len() - equalities, 42, "expected exactly 42 S-box multiplication gates");
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
    assert_eq!(json.matches("\"source_span\"").count(), 165);
    // add32's carry decomposition uses 33 bits; two inputs use 32 each → 97 advice.
    assert_eq!(json.matches("\"visibility\": \"Private\"").count() - 2 /*a,b inputs*/, 97);
}

/// Nested arrays `[[Field; N]; M]` work, including as function arguments.
#[test]
fn nested_arrays() {
    let src = write_case(
        "nested",
        "#![no_std]\nuse xark::{assert_eq, Field, Private, Public};\n\
         fn get(m: [[Field; 2]; 2], i: usize, j: usize) -> Field { m[i][j] }\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>, c: Public<Field>) {\n\
             let m = [[a, b], [b, a]];\n\
             assert_eq(get(m, 0, 0) + m[1][1], c);\n\
         }\n",
    );
    let c = compile(&src, "nested");
    assert!(c.status_success, "nested arrays failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    assert!(json.contains("\"note\": \"(2*a - c) * 1 = 0\""), "{json}");
}

/// Full SHA-256 single-block compression (`xark-sha256`): 64 rounds + message
/// schedule fully unrolled. This is a large circuit (~37k constraints) and the
/// main stress test for the compiler's inlining/unrolling performance — it
/// should compile in seconds, not minutes.
#[test]
fn sha256_compiles() {
    let c = compile_with_field(&example("sha256"), "sha256", "bn254");
    assert!(c.status_success, "sha256 failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    let constraints = json.matches("\"source_span\"").count();
    // Deterministic circuit; exact counts guard against accidental changes.
    assert_eq!(constraints, 38602, "SHA-256 constraint count changed");
    assert_eq!(json.matches("\"name\": \"w").count(), 7680, "advice bit count changed");
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
        program.vars.iter().find(|v| v.name == name).map(|v| v.id).unwrap()
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
    assert!(holes.is_empty(), "bit_decompose under-constrained: {holes:?}");

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
        assert!(names.contains(&want), "missing flattened input `{want}`; got {names:?}");
    }

    let id_of = |name: &str| program.vars.iter().find(|v| v.name == name).map(|v| v.id).unwrap();
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
    let id_of = |name: &str| program.vars.iter().find(|v| v.name == name).map(|v| v.id).unwrap();

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
         use xark::{assert_eq, Field, Private, Public};\n\
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
    src.push_str("];\n  let mut w = [zero; 16];\n  let mut k = 0usize;\n\
        while k < 16usize { let bits = words[k].to_bits::<32>(); let mut j = 0usize; \
        while j < 32usize { w[k][j] = bits[j]; j += 1; } k += 1; }\n\
        let hash = sha256_block(w);\n  let o = [");
    for i in 0..8 {
        let _ = write!(src, "o{i},");
    }
    src.push_str("];\n  let mut i = 0usize;\n\
        while i < 8usize { let mut word = zero; let mut j = 0usize; \
        while j < 32usize { word[j] = hash[i][j]; j += 1; } \
        assert_eq(Field::from_bits::<32>(word), o[i]); i += 1; }\n}\n");

    let path = write_case("sha256_abc", &src);
    let c = compile_with_field(&path, "sha256_abc", "bn254");
    assert!(c.status_success, "sha256_abc failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap();
    let program = primitive::from_json(&json).unwrap();
    let id = |name: &str| program.vars.iter().find(|v| v.name == name).map(|v| v.id).unwrap();

    let block = [
        "1633837952", "0", "0", "0", "0", "0", "0", "0", "0", "0", "0", "0", "0", "0", "0", "24",
    ];
    let out = [
        "3128432319", "2399260650", "1094795486", "1571693091", "2953011619", "2518121116",
        "3021012833", "4060091821",
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
    assert!(holes.is_empty(), "SHA-256 has {} under-constrained vars: {:?}", holes.len(), &holes[..holes.len().min(5)]);

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

    let c = compile_with_field(&example("keccak"), "keccak", "bn254");
    assert!(c.status_success, "keccak failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap();
    let program = primitive::from_json(&json).unwrap();
    let id = |name: &str| program.vars.iter().find(|v| v.name == name).map(|v| v.id).unwrap();

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
    assert!(holes.is_empty(), "Keccak has {} under-constrained vars: {:?}", holes.len(), &holes[..holes.len().min(5)]);

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

    let c = compile_with_field(&example("keccak256"), "keccak256", "bn254");
    assert!(c.status_success, "keccak256 example failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap();
    let program = primitive::from_json(&json).unwrap();
    let id = |name: &str| program.vars.iter().find(|v| v.name == name).map(|v| v.id).unwrap();

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
        primitive::from_json(&std::fs::read_to_string(comp.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |name: &str| program.vars.iter().find(|v| v.name == name).map(|v| v.id).unwrap();
    let set = |m: &mut BTreeMap<u32, String>, pre: &str, v: [&str; 3]| {
        for i in 0..3 { m.insert(id(&format!("{pre}[{i}]")), v[i].to_string()); }
    };
    // a < b+c so qabs = 1 (borrow path exercised).
    let mut inputs = BTreeMap::new();
    set(&mut inputs, "a", ["20632333988089671248318737", "5158083497022417812079684", "5037190915060954894609"]);
    set(&mut inputs, "b", ["30948500982134506872478105", "46422751473201760308717158", "45334718235548594051481"]);
    set(&mut inputs, "c", ["10316166994044835624159368", "41264667976179342496637474", "40297527320487639156872"]);
    set(&mut inputs, "r", ["56738918467246591637908255", "72213168958313849369115579", "19262218059193091516985070"]);

    // (1) correctness + (2) analyzer-clean.
    let assign = solver::solve_and_check(&program, &inputs).expect("(a-b-c) mod p must verify");
    assert!(solver::analyze_underconstrained(&program, &assign).is_empty(), "sub2 under-constrained");

    // (3) forgery: claim a wrong result → rejected.
    let mut bad = inputs.clone();
    bad.insert(id("r[0]"), "12345".to_string());
    assert!(solver::solve_and_check(&program, &bad).is_err(), "wrong result must be rejected");

    // (4) adversarial: inflate an internal carry (a derived var with a small honest
    // value in [2,7] is a biased carry; bits are 0/1 and result limbs are ~2^85).
    // Pushing it out of its 3-bit range must make the constraints reject it.
    let carry = program.vars.iter().find(|v| {
        matches!(v.role, primitive::VarRole::Derived)
            && assign.get(&v.id).map(|x| { let d = x.to_decimal(); d.parse::<u64>().map(|n| (2..=7).contains(&n)).unwrap_or(false) }).unwrap_or(false)
    }).expect("a biased carry variable should exist");
    let mut forged = assign.clone();
    let infl = forged.get(&carry.id).unwrap().to_decimal().parse::<u64>().unwrap() + 8;
    forged.insert(carry.id, solver::fp_from_decimal(&infl.to_string(), &program));
    assert!(solver::check(&program, &forged).is_err(), "out-of-range carry must be rejected");
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
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |name: &str| program.vars.iter().find(|v| v.name == name).map(|v| v.id).unwrap();
    let set = |m: &mut BTreeMap<u32, String>, pre: &str, v: [&str; 3]| {
        for i in 0..3 { m.insert(id(&format!("{pre}[{i}]")), v[i].to_string()); }
    };
    let mut inputs = BTreeMap::new();
    set(&mut inputs, "g.x.limbs", ["52227620040540588600771222", "33347259622618539004134583", "8091721874918813684698062"]);
    set(&mut inputs, "g.y.limbs", ["59685082318776612195095029", "54599710628478995760242092", "6036146923926000695307902"]);
    set(&mut inputs, "two_g.x.limbs", ["60574784517941929169033592", "38742641973200156549941727", "9440742814978962916680995"]);
    set(&mut inputs, "two_g.y.limbs", ["50180633949907515547874257", "52108912657982010475124979", "564125721045731681407961"]);
    set(&mut inputs, "three_g.x.limbs", ["55202213340089332766604652", "75352241312048865668270014", "7162618025266537839759230"]);
    set(&mut inputs, "three_g.y.limbs", ["19003939109578686433415218", "32907397120494406415210721", "10215774641556159746766000"]);

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
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |name: &str| program.vars.iter().find(|v| v.name == name).map(|v| v.id).unwrap();
    let set = |m: &mut BTreeMap<u32, String>, pre: &str, v: [&str; 3]| {
        for i in 0..3 { m.insert(id(&format!("{pre}[{i}]")), v[i].to_string()); }
    };
    let mut inputs = BTreeMap::new();
    set(&mut inputs, "g.x.limbs", ["17117865558768631194064792", "12501176021340589225372855", "9198697782662356105779718"]);
    set(&mut inputs, "g.y.limbs", ["6441780312434748884571320", "57953919405111227542741658", "5457536640262350763842127"]);
    set(&mut inputs, "two_g.x.limbs", ["57105948487393027623526117", "2088890992725950981549619", "14961784698075395646489684"]);
    set(&mut inputs, "two_g.y.limbs", ["46925586441427271765976362", "19820246243853867596485833", "2031033786214458435714136"]);
    set(&mut inputs, "three_g.x.limbs", ["57545291876987742944507641", "75066192660561802595210765", "18828234277447069677687620"]);
    set(&mut inputs, "three_g.y.limbs", ["2583640362791394057184882", "38197615293098406611150035", "4273588397735691711217203"]);

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
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |name: &str| program.vars.iter().find(|v| v.name == name).map(|v| v.id).unwrap();

    // a·b ≡ c (mod p) with 3×86-bit limbs.
    let a = ["67135996574970214581469201", "51946031311641451697362329", "16825126466515450054094827"];
    let b = ["24414941800469763390285221", "15797894945784124056166873", "85968058283706962481699"];
    let cc = ["3097648669108091694378015", "51742203992647403024604737", "1775314877412124564790042"];
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
    assert!(c.stderr.contains("unsupported circuit parameter type `u64`"), "{}", c.stderr);
}

/// A compile-time-constant branch (`if true`) is resolved at lowering — the
/// taken branch is emitted, the other is dropped. (Witness-dependent branches
/// can't even be written: `Field` isn't comparable.)
#[test]
fn constant_branch_is_resolved() {
    let src = write_case(
        "ctrl",
        "#![no_std]\nuse xark::{assert_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, c: Public<Field>) { if true { assert_eq(a, c); } }\n",
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
        "#![no_std]\nuse xark::{assert_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, c: Public<Field>) {\n\
             let mut acc = a; let mut i = 0u64;\n\
             while i < 2 { acc = acc * a; i += 1; }\n\
             assert_eq(acc, c);\n\
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

/// A helper function is inlined, and a multiplication inside it still merges
/// into the following `assert_eq` — proving the gadget-as-library model.
#[test]
fn inlines_helper_function() {
    let src = write_case(
        "square",
        "#![no_std]\nuse xark::{assert_eq, Field, Private, Public};\n\
         fn square(x: Field) -> Field { x * x }\n\
         pub fn circuit(a: Private<Field>, c: Public<Field>) { assert_eq(square(a), c); }\n",
    );
    let c = compile(&src, "inline_square");
    assert!(c.status_success, "square failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    // Inlined `a*a` merges with `== c` into a single `a * a = c` constraint,
    // with no leftover internal variable.
    assert_eq!(json.matches("\"source_span\"").count(), 1);
    assert!(json.contains("\"note\": \"a * a = c\""), "unexpected R1CS: {json}");
    assert!(!json.contains("\"name\": \"t0\""), "mul gate should have merged away");
}

/// A recursive helper is rejected rather than looping forever.
#[test]
fn rejects_recursion() {
    let src = write_case(
        "recurse",
        "#![no_std]\nuse xark::{assert_eq, Field, Private, Public};\n\
         fn rec(x: Field) -> Field { rec(x) }\n\
         pub fn circuit(a: Private<Field>, c: Public<Field>) { assert_eq(rec(a), c); }\n",
    );
    let c = compile(&src, "reject_recurse");
    assert!(!c.status_success);
    assert!(c.stderr.contains("recursion is not supported"), "{}", c.stderr);
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
    let c = compile_with_field(&example("sha256"), "sha256_lean_bridge", "bn254");
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
    assert_eq!(
        mul, 36814,
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
    let c = compile_with_field(&example("blake3"), "blake3_lean_bridge", "bn254");
    assert!(c.status_success, "blake3 gadget compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul = r1cs.constraints.iter().filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty()).count();
    assert_eq!(mul, 19792, "BLAKE3 mult-gate count pins blake3_round_compose_bit; got {mul}");
}

/// **R1CS ↔ Lean bridge (BLAKE2s).**
/// Same `Blake.lean` G-mixing soundness, via `blake2s_round_compose_bit`
/// (10-round schedule, the 10 SIGMA rows). Pins the Rust gadget's mult-gate count.
#[test]
fn blake2s_matches_lean_model() {
    let c = compile_with_field(&example("blake2s"), "blake2s_lean_bridge", "bn254");
    assert!(c.status_success, "blake2s gadget compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul = r1cs.constraints.iter().filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty()).count();
    assert_eq!(mul, 27808, "BLAKE2s mult-gate count pins blake2s_round_compose_bit; got {mul}");
}

/// **R1CS ↔ Lean bridge (Keccak-f[1600]).** `#[ignore]` — 156k constraints.
/// `formal/Formal/Keccak.lean` proves per-bit soundness of one round
/// `ι∘χ∘π∘ρ∘θ` (`keccakRoundStep_bit_sound`). The ρ·π
/// permutation index in the Lean model was corrected to `(X+3Y)%5` to match this
/// (KAT-verified) gadget exactly across all 25 lanes. This test pins the count.
#[test]
#[ignore]
fn keccak_matches_lean_model() {
    let c = compile_with_field(&example("keccak"), "keccak_lean_bridge", "bn254");
    assert!(c.status_success, "keccak gadget compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    )
    .expect("parse r1cs.json");
    let mul = r1cs.constraints.iter().filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty()).count();
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
    let mul = r1cs.constraints.iter().filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty()).count();
    assert_eq!(mul, 145816, "AES-128 mult-gate count; got {mul}");
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
    ).expect("parse r1cs.json");
    let mul = r1cs.constraints.iter().filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty()).count();
    assert_eq!(mul, 1154, "fp_mul mult-gate count pins mul_mod_via_Fr_limbwise_constraints_3; got {mul}");
}

/// **R1CS ↔ Lean bridge (secp256k1 incomplete point-add).**
/// `Secp256k1.lean`'s `ec_add_incomplete_secp256k1_sound` proves the flag-free
/// 3-limb chord addition sound (output on `y²=x³+7`, slope unique) from the
/// generic `Curve` algebra. Pins the `ec_add_incomplete` gadget's shape.
#[test]
fn ec_incomplete_matches_lean_model() {
    let c = compile_with_field(&example("ec_incomplete"), "ec_incomplete_lean_bridge", "bn254");
    assert!(c.status_success, "ec_incomplete compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    ).expect("parse r1cs.json");
    let mul = r1cs.constraints.iter().filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty()).count();
    assert_eq!(mul, 15369, "ec_incomplete mult-gate count pins ec_add_incomplete_secp256k1_sound; got {mul}");
}

/// **R1CS ↔ Lean bridge (secp256r1/P-256 incomplete point-add).**
/// `Secp256r1.lean`'s `ec_add_incomplete_secp256r1_sound` (same shape at `a=−3`).
#[test]
fn ec_incomplete_r1_matches_lean_model() {
    let c = compile_with_field(&example("ec_incomplete_r1"), "ec_incomplete_r1_lean_bridge", "bn254");
    assert!(c.status_success, "ec_incomplete_r1 compiles: {}", c.stderr);
    let r1cs = xark_ir::json::from_json(
        &std::fs::read_to_string(c.out_dir.join("r1cs.json")).expect("read r1cs.json"),
    ).expect("parse r1cs.json");
    let mul = r1cs.constraints.iter().filter(|k| !k.a.terms.is_empty() && !k.b.terms.is_empty()).count();
    assert_eq!(mul, 15891, "ec_incomplete_r1 mult-gate count pins ec_add_incomplete_secp256r1_sound; got {mul}");
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
    assert_eq!(r1cs.constraints.len(), 2, "struct_point lowers to 2 constraints");
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
        "#![no_std]\nuse xark::{assert_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, b: Public<Field>) {\n\
         let big = Field::from(\"21888242871839275222246405745257275088548364400416034343698204186575808495617\");\n\
         let two: Field = \"2\".into();\n\
         assert_eq(a * two + big, b);\n}\n",
    );
    let c = compile(&src, "from_str");
    assert!(c.status_success, "from_str compiles: {}", c.stderr);
    let r1cs = std::fs::read_to_string(c.out_dir.join("r1cs.json")).unwrap();
    assert!(
        r1cs.contains("21888242871839275222246405745257275088548364400416034343698204186575808495617"),
        "the decimal-string constant landed"
    );
}

/// A `Field::from(&str)` with a non-numeric character is a **compile-time** error
/// that names the offending character.
#[test]
fn rejects_non_numeric_field_string() {
    let src = write_case(
        "bad_str",
        "#![no_std]\nuse xark::{assert_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, b: Public<Field>) {\n\
         assert_eq(a + Field::from(\"12a34\"), b);\n}\n",
    );
    let c = compile(&src, "reject_bad_str");
    assert!(!c.status_success);
    assert!(c.stderr.contains("non-numeric character 'a'"), "{}", c.stderr);
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

/// **`fp!` operator layer.** `xark_ff::fp!` defines a non-native field-element
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
    assert!(r1cs.constraints.len() > 1000, "bignum_ops lowered the mul+add+sub");
}

/// **`Field::to_bits` / `from_bits`.** Bit decomposition as a first-class `Field`
/// operation (const-generic bit count, composed from `hint_bit` + arithmetic +
/// `assert_eq`). 8 merged booleanity checks + 2 recompositions = 10.
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
        use xark::{assert_eq, Field, Private};\n\
        use xark_poseidon2::{hash, poseidon2_perm};\n\
        pub fn circuit(a: Private<Field>, b: Private<Field>) {\n\
          assert_eq(hash::<2>([a, b]), poseidon2_perm([a, b, Field::from(2u8)])[0]);\n\
        }\n";
    let path = std::env::temp_dir().join("xark_p2_sponge_id.rs");
    std::fs::write(&path, src).unwrap();
    let c = compile(&path, "poseidon2_sponge_id");
    assert!(c.status_success, "sponge id compile: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let mut inputs = BTreeMap::new();
    inputs.insert(id("a"), "1".to_string());
    inputs.insert(id("b"), "2".to_string());
    let assign = solver::solve_and_check(&program, &inputs).expect("sponge must solve & match perm");
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "sponge under-constrained: {:?}", &holes[..holes.len().min(5)]);
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
        use xark::{assert_eq, Field, Private};\n\
        use xark_poseidon::{hash, permute};\n\
        pub fn circuit(a: Private<Field>, b: Private<Field>) {\n\
          assert_eq(hash::<2>([a, b]), permute([Field::from(2u8), a, b])[0]);\n\
        }\n";
    let path = std::env::temp_dir().join("xark_p_sponge_id.rs");
    std::fs::write(&path, src).unwrap();
    let c = compile(&path, "poseidon_sponge_id");
    assert!(c.status_success, "poseidon sponge id compile: {}", c.stderr);
    let program =
        primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap())
            .unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let mut inputs = BTreeMap::new();
    inputs.insert(id("a"), "7".to_string());
    inputs.insert(id("b"), "11".to_string());
    let assign = solver::solve_and_check(&program, &inputs).expect("poseidon sponge must solve");
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "poseidon sponge under-constrained: {:?}", &holes[..holes.len().min(5)]);
}

/// **Variable-length SHA-256 — real vector.** `sha256::<8>(0..8)` must equal real
/// `SHA-256`, solve, be fully constrained, and reject a wrong digest.
#[test]
#[ignore = "heavy: full multi-block hash circuit"]
fn sha256_varlen_matches_real_vector() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let c = compile(&example("sha256_hash"), "sha256_hash");
    assert!(c.status_success, "sha256_hash failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let mut inputs = BTreeMap::new();
    for i in 0..8u32 { inputs.insert(id(&format!("msg[{i}]")), i.to_string()); }
    let digest = [2323980280u32, 786891914, 3500065668, 2132664132, 2487289042, 3419504372, 3822789318, 2019167557];
    for (i, w) in digest.iter().enumerate() { inputs.insert(id(&format!("d[{i}]")), w.to_string()); }
    let assign = solver::solve_and_check(&program, &inputs).expect("sha256::<8> must match real SHA-256");
    assert!(solver::analyze_underconstrained(&program, &assign).is_empty(), "sha256 under-constrained");
    inputs.insert(id("d[0]"), "42".to_string());
    assert!(solver::solve_and_check(&program, &inputs).is_err(), "wrong digest must reject");
}

/// **Variable-length BLAKE2s — real vector.** `blake2s::<100>(0..100)` (2 blocks)
/// must equal real `hashlib.blake2s`, solve, be fully constrained, reject wrong.
#[test]
#[ignore = "heavy: full multi-block hash circuit"]
fn blake2s_varlen_matches_real_vector() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let c = compile(&example("blake2s_hash"), "blake2s_hash");
    assert!(c.status_success, "blake2s_hash failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let mut inputs = BTreeMap::new();
    for i in 0..100u32 { inputs.insert(id(&format!("msg[{i}]")), i.to_string()); }
    let digest = [2781076609u32, 1070524933, 1888460167, 259487271, 1376712093, 2821198877, 4177833821, 3763347885];
    for (i, w) in digest.iter().enumerate() { inputs.insert(id(&format!("d[{i}]")), w.to_string()); }
    let assign = solver::solve_and_check(&program, &inputs).expect("blake2s::<100> must match real BLAKE2s");
    assert!(solver::analyze_underconstrained(&program, &assign).is_empty(), "blake2s under-constrained");
    inputs.insert(id("d[0]"), "42".to_string());
    assert!(solver::solve_and_check(&program, &inputs).is_err(), "wrong digest must reject");
}

/// **Variable-length BLAKE3 — real vector.** `blake3::<100>(0..100)` (single chunk,
/// 2 blocks) must equal real BLAKE3, solve, be fully constrained, reject wrong.
#[test]
#[ignore = "heavy: full multi-block hash circuit"]
fn blake3_varlen_matches_real_vector() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let c = compile(&example("blake3_hash"), "blake3_hash");
    assert!(c.status_success, "blake3_hash failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let mut inputs = BTreeMap::new();
    for i in 0..100u32 { inputs.insert(id(&format!("msg[{i}]")), i.to_string()); }
    let digest = [3148951182u32, 2399863971, 1074928225, 3339837856, 3385804107, 3104894410, 3681706847, 3048751132];
    for (i, w) in digest.iter().enumerate() { inputs.insert(id(&format!("d[{i}]")), w.to_string()); }
    let assign = solver::solve_and_check(&program, &inputs).expect("blake3::<100> must match real BLAKE3");
    assert!(solver::analyze_underconstrained(&program, &assign).is_empty(), "blake3 under-constrained");
    inputs.insert(id("d[0]"), "42".to_string());
    assert!(solver::solve_and_check(&program, &inputs).is_err(), "wrong digest must reject");
}

/// A multiplication result reused across two `assert_eq`s must stay bound to
/// `a*b` in BOTH. The first `assert_eq` folds the product's defining row (the
/// compaction optimization); the second must not be left pinning a detached
/// free witness. Compiling `examples/mul_reuse` and
/// solving it confirms the product is revived: the honest `a*b == c == d`
/// witness verifies, and a `c != d` witness is rejected.
#[test]
fn mul_reuse_binds_product_in_both_asserts() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};

    let c = compile_with_field(&example("mul_reuse"), "mul_reuse", "bn254");
    assert!(c.status_success, "mul_reuse failed: {}", c.stderr);
    let json = std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap();
    let program = primitive::from_json(&json).unwrap();
    let id = |name: &str| program.vars.iter().find(|v| v.name == name).map(|v| v.id).unwrap();

    // Honest: a*b = c = d (3*4 = 12). Pre-fix this FAILED to solve — the reused
    // product `t` had no witness-gen op after the merge dropped it.
    let mut inputs = BTreeMap::new();
    inputs.insert(id("a"), "3".to_string());
    inputs.insert(id("b"), "4".to_string());
    inputs.insert(id("c"), "12".to_string());
    inputs.insert(id("d"), "12".to_string());
    let assign = solver::solve_and_check(&program, &inputs).expect("a*b == c == d must verify");
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "mul_reuse under-constrained: {holes:?}");

    // Soundness: c != d must be rejected — the product is bound to both asserts,
    // so `d = 13` with `a*b = c = 12` cannot satisfy the circuit.
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
        "#![no_std]\nuse xark::{assert_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>, q: Public<Field>) {\n\
         \x20   assert_eq(a / b, q);\n\
         }\n",
    );
    let c = compile_with_field(&src, "field_div", "bn254");
    assert!(c.status_success, "field_div failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let mut inputs = BTreeMap::new();
    inputs.insert(id("a"), "6".to_string());
    inputs.insert(id("b"), "3".to_string());
    inputs.insert(id("q"), "2".to_string()); // 6 / 3 == 2
    let assign = solver::solve_and_check(&program, &inputs).expect("a/b == q must verify");
    assert!(solver::analyze_underconstrained(&program, &assign).is_empty(), "field_div under-constrained");
    inputs.insert(id("q"), "3".to_string());
    assert!(solver::solve_and_check(&program, &inputs).is_err(), "wrong quotient must reject");
}

/// Compound assignment (`+=`, `*=`, …) needs `&mut self`; taking a reference to
/// a `Field` is not a circuit operation, so the compiler rejects it in-circuit
/// (write `acc = acc + b`). The `AddAssign`/… traits still exist for host/const
/// use — this only asserts the *circuit* rejection.
#[test]
fn rejects_compound_assign() {
    let src = write_case(
        "field_assign",
        "#![no_std]\nuse xark::{assert_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, b: Public<Field>) {\n\
         \x20   let mut acc = a;\n\
         \x20   acc += b;\n\
         \x20   assert_eq(acc, b);\n\
         }\n",
    );
    let c = compile(&src, "reject_assign");
    assert!(!c.status_success, "compound assignment should be rejected in a circuit");
    assert!(c.stderr.contains("not supported inside a circuit"), "unexpected error: {}", c.stderr);
}

/// `==` (and the other comparisons) on `Field` need `&self`; a native `bool`
/// from comparing witnesses is not a circuit operation, so the compiler rejects
/// it in-circuit. The `PartialEq`/… impls still exist for host/const use.
#[test]
fn rejects_field_comparison() {
    let src = write_case(
        "field_cmp",
        "#![no_std]\nuse xark::{assert_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, b: Public<Field>) {\n\
         \x20   if a == b { assert_eq(a, b); }\n\
         }\n",
    );
    let c = compile(&src, "reject_cmp");
    assert!(!c.status_success, "comparison circuit should have been rejected");
    assert!(c.stderr.contains("not supported inside a circuit"), "unexpected error: {}", c.stderr);
}

/// `is_zero` gadget: returns 1 iff the input is 0, as a pinned boolean wire.
#[test]
fn is_zero_gadget_solves() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "is_zero",
        "#![no_std]\nuse xark::{assert_eq, Field, Private, Public};\n\
         pub fn circuit(x: Private<Field>, want: Public<Field>) {\n\
         \x20   assert_eq(x.is_zero().value(), want);\n\
         }\n",
    );
    let c = compile_with_field(&src, "is_zero", "bn254");
    assert!(c.status_success, "is_zero failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let case = |x: &str, want: &str| {
        let mut m = BTreeMap::new();
        m.insert(id("x"), x.to_string());
        m.insert(id("want"), want.to_string());
        m
    };
    // is_zero(0) == 1, is_zero(7) == 0.
    solver::solve_and_check(&program, &case("0", "1")).expect("is_zero(0) == 1");
    let assign = solver::solve_and_check(&program, &case("7", "0")).expect("is_zero(7) == 0");
    // For a nonzero input the inverse advice is pinned ⇒ fully determined.
    assert!(solver::analyze_underconstrained(&program, &assign).is_empty(), "is_zero(x!=0) under-constrained");
    // Lying either way is rejected.
    assert!(solver::solve_and_check(&program, &case("7", "1")).is_err(), "is_zero(7) != 1 must reject");
    assert!(solver::solve_and_check(&program, &case("0", "0")).is_err(), "is_zero(0) != 0 must reject");
}

/// `is_eq` gadget: returns 1 iff the two inputs are equal, as a boolean wire.
#[test]
fn is_eq_gadget_solves() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "is_eq",
        "#![no_std]\nuse xark::{assert_eq, Field, Private, Public};\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>, want: Public<Field>) {\n\
         \x20   assert_eq(a.is_eq(b).value(), want);\n\
         }\n",
    );
    let c = compile_with_field(&src, "is_eq", "bn254");
    assert!(c.status_success, "is_eq failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let case = |a: &str, b: &str, want: &str| {
        let mut m = BTreeMap::new();
        m.insert(id("a"), a.to_string());
        m.insert(id("b"), b.to_string());
        m.insert(id("want"), want.to_string());
        m
    };
    solver::solve_and_check(&program, &case("5", "5", "1")).expect("is_eq(5,5) == 1");
    solver::solve_and_check(&program, &case("5", "6", "0")).expect("is_eq(5,6) == 0");
    assert!(solver::solve_and_check(&program, &case("5", "6", "1")).is_err(), "is_eq(5,6) != 1 must reject");
    assert!(solver::solve_and_check(&program, &case("5", "5", "0")).is_err(), "is_eq(5,5) != 0 must reject");
}

/// `U<N>` fixed-width unsigned integers: range-proved construction + ordering
/// comparisons (`lt`/`le`) that solve correctly and reject false claims and
/// out-of-range inputs.
#[test]
fn uint_comparisons_solve() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "uint_cmp",
        "#![no_std]\nuse xark::{assert_eq, Field, Private, Public, U};\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>, lt: Public<Field>, le: Public<Field>) {\n\
         \x20   let ua = U::<8>::new(a);\n\
         \x20   let ub = U::<8>::new(b);\n\
         \x20   assert_eq(ua.lt(ub).value(), lt);\n\
         \x20   assert_eq(ua.le(ub).value(), le);\n\
         }\n",
    );
    let c = compile_with_field(&src, "uint_cmp", "bn254");
    assert!(c.status_success, "uint_cmp failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let case = |a: &str, b: &str, lt: &str, le: &str| {
        let mut m = BTreeMap::new();
        m.insert(id("a"), a.to_string());
        m.insert(id("b"), b.to_string());
        m.insert(id("lt"), lt.to_string());
        m.insert(id("le"), le.to_string());
        m
    };
    // 3 < 5 (lt=1, le=1); 5 vs 3 (lt=0, le=0); 5 == 5 (lt=0, le=1).
    solver::solve_and_check(&program, &case("3", "5", "1", "1")).expect("3 < 5");
    solver::solve_and_check(&program, &case("5", "3", "0", "0")).expect("5 > 3");
    let assign = solver::solve_and_check(&program, &case("5", "5", "0", "1")).expect("5 == 5");
    assert!(solver::analyze_underconstrained(&program, &assign).is_empty(), "U<8> cmp under-constrained");
    // A false ordering claim is rejected.
    assert!(solver::solve_and_check(&program, &case("3", "5", "0", "1")).is_err(), "3<5 but lt=0 must reject");
    // An out-of-range input (300 >= 2^8) fails the construction range proof.
    assert!(solver::solve_and_check(&program, &case("300", "5", "0", "0")).is_err(), "a=300 exceeds U<8>");
}

/// A secp256k1 scalar must be canonical (`< n`) and nonzero — `s ∈ [1, n-1]` —
/// which is what makes ECDSA signatures non-malleable. Solving `scalar_range`
/// proves such an `s`; a non-canonical `s` (all limbs `2^86-1`, value
/// `≈ 2^258 >> n`) and `s = 0` are both rejected.
#[test]
fn ecdsa_scalar_range_checks() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let c = compile_with_field(&example("scalar_range"), "scalar_range", "bn254");
    assert!(c.status_success, "scalar_range failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
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
    assert!(solver::solve_and_check(&program, &case("0", "0", "0")).is_err(), "s = 0 must be rejected");
    // Every limb at 2^86-1 → value ≈ 2^258, far above n → rejected by assert_canonical.
    let max_limb = "77371252455336267181195263"; // 2^86 - 1
    assert!(
        solver::solve_and_check(&program, &case(max_limb, max_limb, max_limb)).is_err(),
        "a non-canonical scalar (>= n) must be rejected"
    );
}

/// `Bool` + `select`: branchless conditional pick, with a non-boolean condition
/// rejected by `Bool::new`.
#[test]
fn select_and_bool_solve() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "bool_select",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(cond: Private<Field>, a: Private<Field>, b: Private<Field>, out: Public<Field>) {\n\
         \x20   let c = Bool::new(cond);\n\
         \x20   assert_eq(select(c, a, b), out);\n\
         }\n",
    );
    let c = compile_with_field(&src, "bool_select", "bn254");
    assert!(c.status_success, "bool_select failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
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
    assert!(solver::solve_and_check(&program, &case("1", "7", "9", "9")).is_err(), "wrong select must reject");
    assert!(solver::solve_and_check(&program, &case("2", "7", "9", "7")).is_err(), "non-boolean cond must reject");
}

/// `U<N>` checked arithmetic: `add`/`sub`/`mul` compose and solve; a wrong
/// claimed result is rejected.
#[test]
fn uint_checked_arithmetic_solves() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "uint_arith",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>, sum: Public<Field>, diff: Public<Field>, prod: Public<Field>) {\n\
         \x20   let ua = U::<8>::new(a);\n\
         \x20   let ub = U::<8>::new(b);\n\
         \x20   assert_eq((ua + ub).value(), sum);\n\
         \x20   assert_eq((ua - ub).value(), diff);\n\
         \x20   assert_eq((ua * ub).value(), prod);\n\
         }\n",
    );
    let c = compile_with_field(&src, "uint_arith", "bn254");
    assert!(c.status_success, "uint_arith failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let case = |a: &str, b: &str, sum: &str, diff: &str, prod: &str| {
        let mut m = BTreeMap::new();
        m.insert(id("a"), a.to_string());
        m.insert(id("b"), b.to_string());
        m.insert(id("sum"), sum.to_string());
        m.insert(id("diff"), diff.to_string());
        m.insert(id("prod"), prod.to_string());
        m
    };
    // a=5, b=3: 5+3=8, 5-3=2, 5*3=15 (all fit in 8 bits).
    solver::solve_and_check(&program, &case("5", "3", "8", "2", "15")).expect("5,3 arithmetic");
    assert!(solver::solve_and_check(&program, &case("5", "3", "8", "2", "16")).is_err(), "wrong product must reject");
}

/// A `Private<U<N>>` input is prover-chosen, so the compiler injects an N-bit
/// range proof at the input boundary: an honest in-range value solves, and an
/// out-of-range value is unsatisfiable.
#[test]
fn private_uint_input_is_range_proved() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "priv_uint_input",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(x: Private<U<8>>, out: Public<Field>) {\n\
         \x20   assert_eq(x.value(), out);\n\
         }\n",
    );
    let c = compile_with_field(&src, "priv_uint_input", "bn254");
    assert!(c.status_success, "priv_uint_input failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let case = |x: &str, out: &str| {
        let mut m = BTreeMap::new();
        m.insert(id("x"), x.to_string());
        m.insert(id("out"), out.to_string());
        m
    };
    // In range (< 2^8): solves and is fully constrained.
    let assign = solver::solve_and_check(&program, &case("200", "200")).expect("x=200 in range");
    assert!(solver::analyze_underconstrained(&program, &assign).is_empty(), "private U<8> input under-constrained");
    // Out of range (>= 2^8): the injected range proof makes it unsatisfiable.
    assert!(solver::solve_and_check(&program, &case("300", "300")).is_err(), "x=300 exceeds U<8> and must reject");
}

/// A `Public<U<N>>` input carries no in-circuit range proof — the verifier
/// checks the bound before `verify` — so the circuit accepts any field value
/// for it. (The soundness rests on the on-chain program's own check.)
#[test]
fn public_uint_input_delegates_range_to_verifier() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "pub_uint_input",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(x: Public<U<8>>, out: Public<Field>) {\n\
         \x20   assert_eq(x.value(), out);\n\
         }\n",
    );
    let c = compile_with_field(&src, "pub_uint_input", "bn254");
    assert!(c.status_success, "pub_uint_input failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let case = |x: &str, out: &str| {
        let mut m = BTreeMap::new();
        m.insert(id("x"), x.to_string());
        m.insert(id("out"), out.to_string());
        m
    };
    // No in-circuit range proof: an out-of-range value still solves in-circuit,
    // which is exactly the contract (the program range-checks it externally).
    solver::solve_and_check(&program, &case("300", "300")).expect("public U<8> input is not range-proved in-circuit");
    // A count check pins the "no injected proof" property: only the single
    // `x == out` row, no bit-decomposition constraints.
    assert!(program.constraints.len() <= 2, "public U<N> must not emit a range proof (got {} constraints)", program.constraints.len());
}

/// `Bool` supports the standard boolean operators (`&`, `|`, `!`) as core-trait
/// impls, so circuits read like ordinary Rust. Verifies they lower and solve.
#[test]
fn bool_operators_solve() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "bool_ops",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>, want: Public<Field>) {\n\
         \x20   let x = Bool::new(a);\n\
         \x20   let y = Bool::new(b);\n\
         \x20   assert_eq(((x & y) | !x).value(), want);\n\
         }\n",
    );
    let c = compile_with_field(&src, "bool_ops", "bn254");
    assert!(c.status_success, "bool_ops failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let case = |a: &str, b: &str, want: &str| {
        let mut m = BTreeMap::new();
        m.insert(id("a"), a.to_string());
        m.insert(id("b"), b.to_string());
        m.insert(id("want"), want.to_string());
        m
    };
    // (x & y) | !x : a=1,b=0 -> (1&0)|!1 = 0 ; a=0,b=1 -> (0&1)|!0 = 1.
    solver::solve_and_check(&program, &case("1", "0", "0")).expect("(1&0)|!1 == 0");
    solver::solve_and_check(&program, &case("0", "1", "1")).expect("(0&1)|!0 == 1");
    // Non-boolean input is rejected by Bool::new.
    assert!(solver::solve_and_check(&program, &case("2", "0", "0")).is_err(), "non-boolean input must reject");
}

/// Rejections carry an actionable `help:` line, not just a terse error — this is
/// what `xark check` surfaces in rust-analyzer. Guards that the diagnostic
/// contract doesn't silently regress.
#[test]
fn rejections_carry_actionable_help() {
    // A bare `Field` parameter (must be wrapped in a visibility marker).
    let bare = write_case(
        "diag_bare_field",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(x: Field, out: Public<Field>) {\n\
         \x20   assert_eq(x, out);\n\
         }\n",
    );
    let c = compile_with_field(&bare, "diag_bare_field", "bn254");
    assert!(!c.status_success, "bare Field param should be rejected");
    assert!(c.stderr.contains("help:"), "rejection must include a help line; got: {}", c.stderr);
    assert!(
        c.stderr.contains("Private<Field>") || c.stderr.contains("Public<Field>"),
        "help should point at the visibility markers; got: {}",
        c.stderr
    );

    // An out-of-range fixed-width input width.
    let wide = write_case(
        "diag_wide_uint",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(x: Public<U<300>>, out: Public<Field>) {\n\
         \x20   assert_eq(x.value(), out);\n\
         }\n",
    );
    let c = compile_with_field(&wide, "diag_wide_uint", "bn254");
    assert!(!c.status_success, "U<300> input should be rejected");
    assert!(c.stderr.contains("1..=253"), "width error should state the valid range; got: {}", c.stderr);
}

/// Signed `I<N>`: construction, sign predicates, signed comparison and checked
/// add all solve — for positive and (field-encoded) negative values alike.
#[test]
fn signed_int_solves() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "signed_int",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>, sum: Public<Field>, lt: Public<Field>, a_pos: Public<Field>) {\n\
         \x20   let ia = I::<8>::new(a);\n\
         \x20   let ib = I::<8>::new(b);\n\
         \x20   assert_eq((ia + ib).value(), sum);\n\
         \x20   assert_eq(ia.lt(ib).value(), lt);\n\
         \x20   assert_eq(ia.is_positive().value(), a_pos);\n\
         }\n",
    );
    let c = compile_with_field(&src, "signed_int", "bn254");
    assert!(c.status_success, "signed_int failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let case = |a: &str, b: &str, sum: &str, lt: &str, a_pos: &str| {
        let mut m = BTreeMap::new();
        m.insert(id("a"), a.to_string());
        m.insert(id("b"), b.to_string());
        m.insert(id("sum"), sum.to_string());
        m.insert(id("lt"), lt.to_string());
        m.insert(id("a_pos"), a_pos.to_string());
        m
    };
    // r-k is the field encoding of -k.
    let neg2 = "21888242871839275222246405745257275088548364400416034343698204186575808495615";
    let neg5 = "21888242871839275222246405745257275088548364400416034343698204186575808495612";
    // a=3, b=5: 3+5=8; 3<5 -> 1; 3>0 -> 1.
    let assign = solver::solve_and_check(&program, &case("3", "5", "8", "1", "1")).expect("3,5 signed");
    assert!(solver::analyze_underconstrained(&program, &assign).is_empty(), "I<8> under-constrained");
    // a=-5, b=3: -5+3 = -2 (=r-2); -5<3 -> 1; -5>0 -> 0.
    solver::solve_and_check(&program, &case(neg5, "3", neg2, "1", "0")).expect("-5,3 signed");
    // A wrong sign claim is rejected.
    assert!(solver::solve_and_check(&program, &case(neg5, "3", neg2, "1", "1")).is_err(), "-5 is not positive");
}

/// Signed arithmetic is checked: a sum outside `[-2^(N-1), 2^(N-1))`, and the
/// classic `-I::MIN`, both make the circuit unsatisfiable.
#[test]
fn signed_int_overflow_rejected() {
    use std::collections::BTreeMap;
    use xark_ir::{primitive, solver};
    let src = write_case(
        "signed_overflow",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(a: Private<Field>, b: Private<Field>, out: Public<Field>) {\n\
         \x20   let ia = I::<8>::new(a);\n\
         \x20   let ib = I::<8>::new(b);\n\
         \x20   assert_eq((ia + ib).value(), out);\n\
         }\n",
    );
    let c = compile_with_field(&src, "signed_overflow", "bn254");
    assert!(c.status_success, "signed_overflow failed: {}", c.stderr);
    let program = primitive::from_json(&std::fs::read_to_string(c.out_dir.join("circuit.json")).unwrap()).unwrap();
    let id = |n: &str| program.vars.iter().find(|v| v.name == n).map(|v| v.id).unwrap();
    let case = |a: &str, b: &str, out: &str| {
        let mut m = BTreeMap::new();
        m.insert(id("a"), a.to_string());
        m.insert(id("b"), b.to_string());
        m.insert(id("out"), out.to_string());
        m
    };
    // 100 + 100 = 200, outside [-128, 128): overflow -> unsatisfiable.
    assert!(solver::solve_and_check(&program, &case("100", "100", "200")).is_err(), "signed add overflow must reject");
    // Sanity: 100 + 20 = 120 is in range and solves.
    solver::solve_and_check(&program, &case("100", "20", "120")).expect("100+20 in range");
}

/// `I<N>` as a raw input is rejected (a two-field struct would flatten into
/// unconstrained leaves) — the guard steers to `I::new`.
#[test]
fn signed_int_input_is_rejected() {
    let src = write_case(
        "signed_input",
        "#![no_std]\nuse xark::prelude::*;\n\
         pub fn circuit(x: Private<I<8>>, out: Public<Field>) {\n\
         \x20   assert_eq(x.value(), out);\n\
         }\n",
    );
    let c = compile_with_field(&src, "signed_input", "bn254");
    assert!(!c.status_success, "I<8> input must be rejected");
    assert!(
        c.stderr.contains("I::") && c.stderr.contains("help:"),
        "rejection should steer to I::new; got: {}",
        c.stderr
    );
}
