//! End to end: build example circuits with stable `cargo` for wasm32, lower them, and
//! check the result (needs the `wasm32-unknown-unknown` target; installed on demand).

use std::path::PathBuf;

fn example(name: &str) -> xark_frontend::Lowered {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let dir = root.join("examples").join(name).canonicalize().unwrap();
    let wasm = xark_frontend::build_crate(&dir, &dir.join("target/xark-wasm")).unwrap();
    xark_frontend::lower_module(&wasm, xark_ir::FieldSpec::named("bn254"), false, false)
        .unwrap_or_else(|e| panic!("{name}: {e}"))
}

fn check(name: &str, constraints: usize) -> xark_frontend::Lowered {
    let l = example(name);
    let out = &l.output;
    assert_eq!(
        out.r1cs.constraints.len(),
        constraints,
        "{name} constraint count"
    );
    let xbc = &out.xbc;
    xark_ir::function_decode::verify_blob_matches(xbc, &out.r1cs, &out.primitive)
        .unwrap_or_else(|e| panic!("{name}: circuit.xbc != lowering: {e}"));
    l
}

#[test]
fn cube() {
    let l = check("cube", 2);
    assert_eq!(l.entry.as_deref(), Some("cube"));
    assert_eq!(
        l.schema["public_inputs"],
        serde_json::json!(["result"]),
        "{}",
        l.schema
    );
}

#[test]
fn poseidon_keeps_large_sums_inline() {
    // Naming every multiplication operand over 8 terms (as the removed MIR
    // frontend's flat lowering did) costs 400 constraints; inline it's 241, less 3
    // for the constant capacity lane's first S-box (`rc⁵`, folded at compile time).
    check("poseidon", 238);
}

#[test]
fn sha256_with_byte_inputs() {
    let l = check("sha256", 35096);
    assert_eq!(l.schema["inputs"][0]["type"]["array"]["of"]["uint"], 8);
}
