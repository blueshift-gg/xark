//! Demonstrates the `Into<[Field; N]>` positional input path — the replacement for the
//! `NativeInput` (name-keyed decimal + `String` mirror) machinery. The host builds its
//! domain struct with `Field` values, `#[derive(CircuitInput)]` flattens it to
//! `[Field; N]`, `Field::to_decimal` renders each, and the prover binds them
//! POSITIONALLY to the circuit's inputs (flatten order = input-var order). No leaf
//! names, no parallel mirror struct.

use std::collections::BTreeMap;

use xark::{CircuitInput, Field};
use xark_ir::solver;

/// The host-side domain type — real `Field` values, one derive. In a real crate this is
/// the *same* struct the circuit body uses (cfg-split), here a standalone copy so the
/// test can build it host-side.
#[derive(CircuitInput)]
struct ZkId {
    id: Field,
    dob: Field,
    country: Field,
    nonce: Field,
}

fn compile(src: &str, name: &str) -> xark_test_harness::Compiled {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/test-cases");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{name}.rs"));
    std::fs::write(&path, src).unwrap();
    let c = xark_test_harness::compile_file(&path, name, "bn254");
    assert!(c.status_success, "compile failed: {}", c.stderr);
    c
}

#[test]
fn to_decimal_reads_a_constructed_field_back() {
    assert_eq!(Field::from(0u8).to_decimal(), "0");
    assert_eq!(Field::from(19900101u64).to_decimal(), "19900101");
    assert_eq!(Field::from(u128::MAX).to_decimal(), u128::MAX.to_string());
    let big = "218882428718392752222464057452572750885483644004160343436982041865758084956";
    assert_eq!(Field::constant(big).to_decimal(), big);
}

#[test]
fn from_bytes_constructors() {
    // Little-endian: `bytes[0]` is least significant.
    assert_eq!(Field::from_le_bytes(&[1]).to_decimal(), "1");
    assert_eq!(Field::from_le_bytes(&[0, 1]).to_decimal(), "256");
    assert_eq!(
        Field::from_le_bytes(&[0xff; 8]).to_decimal(),
        u64::MAX.to_string()
    );
    // Big-endian mirrors it: `bytes[0]` is most significant.
    assert_eq!(Field::from_be_bytes(&[1]).to_decimal(), "1");
    assert_eq!(Field::from_be_bytes(&[1, 0]).to_decimal(), "256");
    // Usable in `const` position (byte-encoded inputs become constants).
    const C: Field = Field::from_le_bytes(&[2, 1]); // 2 + 1·256
    assert_eq!(C.to_decimal(), "258");
}

#[test]
fn const_integer_construction() {
    // `.into()` can't appear in a `const` (traits aren't `const` on stable); the per-type
    // `from_*` constructors are the `const` integer transformers — no `as` cast needed.
    const DOB: Field = Field::from_u64(19900101);
    const COUNTRY: Field = Field::from_u16(u16::from_le_bytes(*b"US"));
    const FLAG: Field = Field::from_bool(true);
    const BYTE: Field = Field::from_u8(255);
    assert_eq!(DOB.to_decimal(), "19900101");
    assert_eq!(COUNTRY.to_decimal(), "21333"); // "US" little-endian
    assert_eq!(FLAG.to_decimal(), "1");
    assert_eq!(BYTE.to_decimal(), "255");
    // still `From` at runtime
    assert_eq!(Field::from(19900101u64).to_decimal(), DOB.to_decimal());
}

#[test]
fn positional_input_flattens_and_solves() {
    // Toy relation over a struct input: the four fields must sum to a public total.
    let src = "#![no_std]\nuse xark::prelude::*;\n\
        struct ZkId { id: Field, dob: Field, country: Field, nonce: Field }\n\
        pub fn circuit(u: Private<ZkId>, total: Public<Field>) {\n\
        require_eq(u.id + u.dob + u.country + u.nonce, total);\n\
        }\n";
    let c = compile(src, "positional_zkid");
    let p = c.program();

    // Host builds its domain value with `Field` values (an encoding lives here, once)…
    let user = ZkId {
        id: Field::from(1u64),
        dob: Field::from(2u64),
        country: Field::from(3u64),
        nonce: Field::from(4u64),
    };
    // …flattens via the derive, and renders each field to a decimal — no leaf names.
    let flat: [Field; 4] = user.into();
    let mut decimals: Vec<String> = flat.iter().map(|f| f.to_decimal()).collect();

    // Bind positionally to the circuit's inputs (flatten order == input-var id order).
    let bind = |decimals: &[String]| -> BTreeMap<u32, String> {
        let mut inputs: Vec<_> = p
            .vars
            .iter()
            .filter(|v| {
                matches!(
                    v.role,
                    xark_ir::primitive::VarRole::PublicInput
                        | xark_ir::primitive::VarRole::PrivateInput
                )
            })
            .collect();
        inputs.sort_by_key(|v| v.id);
        assert_eq!(decimals.len(), inputs.len());
        inputs
            .iter()
            .map(|v| v.id)
            .zip(decimals.iter().cloned())
            .collect()
    };

    // total = 1 + 2 + 3 + 4 = 10 → solves.
    decimals.push(Field::from(10u64).to_decimal());
    solver::solve_and_check(&p, &bind(&decimals)).expect("correct sum must solve");

    // A wrong total is rejected.
    let mut bad = decimals.clone();
    *bad.last_mut().unwrap() = Field::from(11u64).to_decimal();
    assert!(
        solver::solve_and_check(&p, &bind(&bad)).is_err(),
        "wrong total must be rejected"
    );
}
