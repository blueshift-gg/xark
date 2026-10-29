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

/// The check `xark build` runs catches an artifact that differs from the lowering:
/// constraints reordered, or one missing.
#[test]
fn a_mismatched_circuit_xbc_is_caught() {
    let l = example("poseidon");
    let out = &l.output;
    let verify = |r1cs: &xark_ir::r1cs::R1csProgram| {
        xark_ir::function_decode::verify_blob_matches(&out.xbc, r1cs, &out.primitive)
    };
    assert!(verify(&out.r1cs).is_ok());
    let mut swapped = out.r1cs.clone();
    let i = (1..swapped.constraints.len())
        .find(|&i| {
            let (x, y) = (&swapped.constraints[i], &swapped.constraints[0]);
            (&x.a, &x.b, &x.c) != (&y.a, &y.b, &y.c)
        })
        .unwrap();
    swapped.constraints.swap(0, i);
    assert!(verify(&swapped).is_err());
    let mut short = out.r1cs.clone();
    short.constraints.pop();
    assert!(verify(&short).is_err());
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
    // The byte inputs' range checks are reused where the hash splits them into bits.
    let l = check("sha256", 35069);
    assert_eq!(l.schema["inputs"][0]["type"]["array"]["of"]["uint"], 8);
}

/// Two `#[circuit]`s in one crate fail with the real cause, wherever they are,
/// not the clash of the entry symbols they both define.
#[test]
fn two_circuits_in_one_crate_are_explained() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let lang = root.join("crates/lang").canonicalize().unwrap();
    let base = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("two_circuits");
    let cases: [(&str, &[(&str, &str)]); 2] = [
        (
            "same_module",
            &[(
                "lib.rs",
                "use xark::{circuit, require_eq, Field, Private, Public};\n\
                 #[circuit]\npub fn cube(x: Private<Field>, y: Public<Field>) { require_eq(x.pow(3), y); }\n\
                 #[circuit]\npub fn square(x: Private<Field>, y: Public<Field>) { require_eq(x * x, y); }\n",
            )],
        ),
        (
            "two_modules",
            &[
                (
                    "lib.rs",
                    "use xark::{circuit, require_eq, Field, Private, Public};\nmod other;\n\
                     #[circuit]\npub fn cube(x: Private<Field>, y: Public<Field>) { require_eq(x.pow(3), y); }\n",
                ),
                (
                    "other.rs",
                    "use xark::{circuit, require_eq, Field, Private, Public};\n\
                     #[circuit]\npub fn square(x: Private<Field>, y: Public<Field>) { require_eq(x * x, y); }\n",
                ),
            ],
        ),
    ];
    for (name, files) in cases {
        let dir = base.join(name);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        std::fs::write(
            dir.join("Cargo.toml"),
            format!(
                "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
                 [dependencies]\nxark = {{ path = {:?} }}\n\n[workspace]\n\n\
                 [lints.rust]\nunexpected_cfgs = {{ level = \"warn\", check-cfg = ['cfg(xark)'] }}\n",
                lang.display().to_string()
            ),
        )
        .unwrap();
        for (file, text) in files {
            std::fs::write(dir.join("src").join(file), text).unwrap();
        }
        let err = xark_frontend::build_crate(&dir, &base.join("target")).unwrap_err();
        assert!(
            err.contains("2 #[circuit] functions") && err.contains("one circuit per crate"),
            "{name}: {err}"
        );
        let other = if name == "same_module" {
            "src/lib.rs:4"
        } else {
            "src/other.rs:2"
        };
        assert!(
            err.contains("src/lib.rs:") && err.contains(other),
            "{name}: {err}"
        );
    }
}
