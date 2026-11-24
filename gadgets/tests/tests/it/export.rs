//! `xark export` writes a Solana verifier crate whose own `cargo test` verifies
//! the bundled proof against the embedded key.

use crate::common::{run, tempdir, xark_build, xark_prove, xark_setup};
use std::path::Path;

#[test]
fn exported_verifier_passes_its_own_test() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let (ok, err) = xark_build("arithmetic_square", &out, &tmp.path().join("target"));
    assert!(ok, "build failed: {err}");
    let (ok, err) = xark_setup(&out);
    assert!(ok, "setup failed: {err}");
    let (ok, err) = xark_prove(&out, &[("x", "3"), ("y", "9")]);
    assert!(ok, "prove failed: {err}");

    // Any key exports, and the crate says how it was made: this one is seeded
    // (`xark_setup`'s seed 1), which anyone with the seed could forge proofs for.
    let out_s = out.to_str().unwrap();
    let verifier = tmp.path().join("verifier");
    let verifier_s = verifier.to_str().unwrap();
    let (ok, _, err) = run(&["export", out_s, "--out", verifier_s]);
    assert!(ok, "export failed: {err}");
    assert!(
        err.contains("seeded setup (--deterministic-rng 1)"),
        "{err}"
    );
    let lib = std::fs::read_to_string(verifier.join("src/lib.rs")).unwrap();
    assert!(
        lib.contains(r#"pub const SETUP: &str = "seeded";"#),
        "{lib}"
    );
    // A `CircuitProof` in Rust gives the same bytes as the sample files.
    let read = |f: &str| std::fs::read(out.join(f)).unwrap();
    let proof = xark_prover::CircuitProof {
        proof: read("proof.bin"),
        public_inputs: read("public_inputs.bin"),
    };
    let sample = |f: &str| std::fs::read(verifier.join(f)).unwrap();
    assert_eq!(proof.to_solana_proof().unwrap(), sample("proof.solana.bin"));
    assert_eq!(
        proof.to_solana_public_inputs().unwrap(),
        sample("public_inputs.solana.bin")
    );
    assert_eq!(
        proof.to_instruction_data().unwrap(),
        sample("instruction_data.bin")
    );
    // A newer proof leaves the bundled sample as it is, while that still verifies:
    // a proof is randomized, and regenerating mustn't change a committed crate.
    let bundled = sample("proof.solana.bin");
    let (ok, err) = xark_prove(&out, &[("x", "3"), ("y", "9")]);
    assert!(ok, "prove failed: {err}");
    let (ok, _, err) = run(&["export", out_s, "--out", verifier_s]);
    assert!(ok, "re-export failed: {err}");
    assert_eq!(sample("proof.solana.bin"), bundled);
    // Again over its own output is fine (regenerating) …
    let (ok, _, err) = run(&["export", out_s, "--out", verifier_s]);
    assert!(ok, "re-export failed: {err}");
    assert!(
        err.contains("isn't empty: writing the verifier crate there anyway"),
        "{err}"
    );
    // … but never over a crate it didn't write.
    let mine = tmp.path().join("mine");
    std::fs::create_dir_all(mine.join("src")).unwrap();
    std::fs::write(mine.join("src/lib.rs"), "// my program\n").unwrap();
    let (ok, _, err) = run(&["export", out_s, "--out", mine.to_str().unwrap()]);
    assert!(!ok && err.contains("refusing to overwrite"), "{err}");
    assert_eq!(
        std::fs::read_to_string(mine.join("src/lib.rs")).unwrap(),
        "// my program\n"
    );

    let log = cargo_test(&verifier);
    assert!(
        log.contains("4 passed"),
        "expected the bundled-proof, raw, typed-inputs and typed instruction-data tests:\n{log}"
    );
}

/// Without a proof, or with one for another key, the crate is written without a
/// self-test, and still builds; a proof given by flag must verify.
#[test]
fn a_proof_is_optional() {
    let tmp = tempdir();
    let out = tmp.path().join("out");
    let (ok, err) = xark_build("arithmetic_square", &out, &tmp.path().join("target"));
    assert!(ok, "build failed: {err}");
    let (ok, err) = xark_setup(&out);
    assert!(ok, "setup failed: {err}");
    let (out_s, verifier) = (out.to_str().unwrap(), tmp.path().join("verifier"));
    let export = |extra: &[&str]| {
        // Named apart from the other test's crate: they share a cargo target.
        let mut args = vec![
            "export",
            out_s,
            "--out",
            verifier.to_str().unwrap(),
            "--crate-name",
            "proofless-verifier",
        ];
        args.extend_from_slice(extra);
        run(&args)
    };
    let sample = [
        "proof.solana.bin",
        "public_inputs.solana.bin",
        "instruction_data.bin",
    ];

    let (ok, stdout, err) = export(&[]);
    assert!(ok, "export without a proof failed: {err}");
    assert!(!stdout.contains("cargo test"), "{stdout}");
    assert!(sample.iter().all(|f| !verifier.join(f).exists()));
    let lib = std::fs::read_to_string(verifier.join("src/lib.rs")).unwrap();
    assert!(lib.contains("pub const NUM_PUBLIC_INPUTS: usize = 1;") && !lib.contains("mod tests"));
    let log = cargo_test(&verifier);
    assert!(log.contains("0 passed"), "{log}");

    // A proof, then new keys: the old proof is for another key.
    let (ok, err) = xark_prove(&out, &[("x", "3"), ("y", "9")]);
    assert!(ok, "prove failed: {err}");
    let (ok, _, err) = export(&[]);
    assert!(
        ok && sample.iter().all(|f| verifier.join(f).exists()),
        "{err}"
    );
    let (ok, _, err) = run(&["setup", out_s, "--deterministic-rng", "2"]);
    assert!(ok, "setup failed: {err}");
    let (ok, _, err) = export(&[]);
    assert!(
        ok && err.contains("is for another key, so the crate gets no self-test"),
        "{err}"
    );
    assert!(
        sample.iter().all(|f| !verifier.join(f).exists()),
        "an old sample was kept"
    );
    // Named by flag, it has to verify.
    let proof = out.join("proof.bin");
    let (ok, _, err) = export(&["--proof", proof.to_str().unwrap()]);
    assert!(!ok && err.contains("doesn't verify"), "{err}");

    // Exported again without a name, the crate keeps the one it has, so a program
    // depending on it (a 0.4.0 `<name>-verifier`) still builds.
    let (ok, _, err) = run(&["export", out_s, "--out", verifier.to_str().unwrap()]);
    assert!(ok, "{err}");
    let manifest = std::fs::read_to_string(verifier.join("Cargo.toml")).unwrap();
    assert!(
        manifest.contains("name = \"proofless-verifier\""),
        "{manifest}"
    );
}

/// The exported crate's `PublicInputs` packs every kind of input as `#[input]`
/// does: its self-test writes the sample proof's public inputs by name (as
/// `xark_schema` decodes them), checks `to_fields()` gives the sample's field
/// elements, and verifies the proof with them.
#[test]
fn typed_public_inputs_match_the_proof() {
    let tmp = tempdir();
    let dir = tmp.path().join("kinds");
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap();
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"kinds\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[workspace]\n\
             [dependencies]\nxark = {{ path = {:?} }}\nxark-hash = {{ path = {:?} }}\n\
             [lints.rust]\nunexpected_cfgs = {{ level = \"warn\", check-cfg = ['cfg(xark)'] }}\n",
            root.join("crates/lang").display().to_string(),
            root.join("gadgets/xark-hash").display().to_string(),
        ),
    )
    .unwrap();
    // Packed runs (one with a 249-bit set and a bool), a choice, text, times of
    // two units, bytes, an array of structs, a hash's halves, an address (given in
    // base58, a `[u8; 32]` in the crate), and the extremes of signed and unsigned
    // integers.
    std::fs::write(dir.join("src/lib.rs"), KINDS).unwrap();
    std::fs::write(dir.join("inputs.json"), KINDS_INPUTS).unwrap();
    let d = dir.to_str().unwrap();
    for args in [
        vec!["build", d],
        vec!["setup", d],
        vec![
            "prove",
            d,
            "--inputs",
            dir.join("inputs.json").to_str().unwrap(),
        ],
        vec!["export", d],
    ] {
        let (ok, _, err) = run(&args);
        assert!(ok, "`xark {}` failed: {err}", args[0]);
    }
    let verifier = dir.join("clients/rust");
    let lib = std::fs::read_to_string(verifier.join("src/lib.rs")).unwrap();
    assert!(lib.contains("pub struct PublicInputs {"), "{lib}");
    assert!(lib.contains("    pub to: [u8; 32],"), "{lib}");
    // The proof and its inputs as one type, named after the circuit; with inputs
    // that aren't all byte arrays, it has no parser from instruction data, but the
    // generic `RawProof` still reads the field elements.
    assert!(lib.contains("pub struct KindsProof {"), "{lib}");
    assert!(
        lib.contains("impl xark_verifier::Verifiable for KindsProof"),
        "{lib}"
    );
    assert!(!lib.contains("TryFrom<&[u8]> for KindsProof"), "{lib}");
    let log = cargo_test(&verifier);
    assert!(log.contains("3 passed"), "{log}");
}

/// With every public input a byte array, the proof type parses from instruction data
/// with each input as its own bytes (a hash is its 32), while the generic `RawProof`
/// reads the elements as the prover writes them, 32 bytes each (a `Field` is one, a
/// `[u8; 3]` one per byte, a hash and an address two halves each). The self-tests
/// parse the sample both ways; a test of our own checks the values the typed one
/// reads, that they pack to the prover's elements, and that neither reads the
/// other's layout.
#[test]
fn byte_inputs_parse_from_instruction_data() {
    let tmp = tempdir();
    let dir = tmp.path().join("byte_inputs");
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap();
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"byte_inputs\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[workspace]\n\
             [dependencies]\nxark = {{ path = {:?} }}\nxark-hash = {{ path = {:?} }}\n\
             [lints.rust]\nunexpected_cfgs = {{ level = \"warn\", check-cfg = ['cfg(xark)'] }}\n",
            root.join("crates/lang").display().to_string(),
            root.join("gadgets/xark-hash").display().to_string(),
        ),
    )
    .unwrap();
    std::fs::write(dir.join("src/lib.rs"), BYTE_INPUTS).unwrap();
    std::fs::write(dir.join("inputs.json"), BYTE_INPUTS_INPUTS).unwrap();
    let d = dir.to_str().unwrap();
    for args in [
        vec!["build", d],
        vec!["setup", d],
        vec![
            "prove",
            d,
            "--inputs",
            dir.join("inputs.json").to_str().unwrap(),
        ],
        vec!["export", d],
    ] {
        let (ok, _, err) = run(&args);
        assert!(ok, "`xark {}` failed: {err}", args[0]);
    }
    let verifier = dir.join("clients/rust");
    let lib = std::fs::read_to_string(verifier.join("src/lib.rs")).unwrap();
    assert!(lib.contains("TryFrom<&[u8]> for ByteInputsProof"), "{lib}");
    std::fs::create_dir_all(verifier.join("tests")).unwrap();
    std::fs::write(verifier.join("tests/parse.rs"), BYTE_INPUTS_PARSE).unwrap();
    let log = cargo_test(&verifier);
    assert!(
        log.contains("4 passed") && log.contains("1 passed"),
        "expected the crate's 4 tests and the parse test:\n{log}"
    );
}

const BYTE_INPUTS: &str = r#"#![cfg_attr(xark, no_std)]
use xark::prelude::*;
use xark_hash::Hash;

#[circuit]
pub fn byte_inputs(
    x: Private<Field>,
    y: Public<Field>,
    bytes: Public<[u8; 3]>,
    digest: Public<Hash>,
    to: Public<Address>,
) {
    require_eq(x * x, y);
    bind(bytes);
    bind(digest);
    bind(to);
}
"#;

const BYTE_INPUTS_INPUTS: &str = r#"{"x": 3, "y": 9, "bytes": "0x01ff7e",
 "digest": "0x00112233445566778899aabbccddeeff102132435465768798a9bacbdcedfe0f",
 "to": "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA"}
"#;

/// The exported crate's `tests/parse.rs`. As their own bytes, the inputs are `y`'s
/// 32 (a `Field` is its element), `bytes`' 3, then the digest's and the address's
/// 32; as elements, `y`, `bytes[0..3]`, then the digest's and the address's halves.
const BYTE_INPUTS_PARSE: &str = r#"use byte_inputs_client::{
    verify, ByteInputsProof, RawProof, Verifiable, XarkError, NUM_PUBLIC_INPUTS,
};

fn hex(s: &str) -> [u8; 32] {
    core::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
}

const DIGEST: &str = "00112233445566778899aabbccddeeff102132435465768798a9bacbdcedfe0f";
// TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA
const TO: &str = "06ddf6e1d765a193d9cbe146ceeb79ac1cb485ed5f5b37913a8cf5857eff00a9";

#[test]
fn each_layout_parses_with_its_own_type_only() {
    let fields = std::fs::read(concat!(env!("CARGO_MANIFEST_DIR"), "/instruction_data.bin")).unwrap();
    assert_eq!(fields.len(), 256 + 8 * 32);
    let raw = RawProof::<NUM_PUBLIC_INPUTS>::try_from(&fields[..]).unwrap();
    assert!(verify(&raw.proof, raw.inputs));

    let mut typed = fields[..256].to_vec();
    typed.extend_from_slice(&raw.inputs[0]);
    typed.extend_from_slice(&[0x01, 0xff, 0x7e]);
    typed.extend_from_slice(&hex(DIGEST));
    typed.extend_from_slice(&hex(TO));
    assert_eq!(typed.len(), 256 + 32 + 3 + 32 + 32);
    let p = ByteInputsProof::try_from(&typed[..]).unwrap();
    assert_eq!(p.bytes, [0x01, 0xff, 0x7e]);
    assert_eq!(p.digest, hex(DIGEST));
    assert_eq!(p.to, hex(TO));
    assert_eq!(p.to_fields(), raw.inputs);
    assert_eq!(p.verify(), Ok(()));

    assert_eq!(ByteInputsProof::try_from(&fields[..]), Err(XarkError::TrailingBytes));
    assert_eq!(RawProof::<NUM_PUBLIC_INPUTS>::try_from(&typed[..]), Err(XarkError::Truncated));
}
"#;

const KINDS: &str = r#"#![cfg_attr(xark, no_std)]
use xark::prelude::*;
use xark_hash::Hash;

pub type Day = Days<1900, 2100>;

#[input]
pub struct Policy {
    pub today: Day,
    pub born_by: Day,
    pub min: u64,
    pub allowed: Bitfield<Country>,
    pub flag: bool,
    pub at: Time<3600, 2000, 2100>,
}

#[input]
pub struct Pair {
    pub a: u16,
    pub b: i32,
}

#[input]
pub struct Pt(pub u32, pub u64);

#[circuit]
pub fn kinds(
    x: Private<Field>,
    y: Public<Field>,
    policy: Public<Policy>,
    who: Public<Choice<Country>>,
    name: Public<Text>,
    when: Public<Timestamp>,
    bytes: Public<[u8; 3]>,
    pairs: Public<[Pair; 2]>,
    digest: Public<Hash>,
    to: Public<Address>,
    big: Public<u128>,
    neg: Public<i64>,
    pt: Public<Pt>,
) {
    require_eq(x * x, y);
    bind(policy);
    bind(who);
    bind(name);
    bind(when);
    bind(bytes);
    bind(pairs);
    bind(digest);
    bind(to);
    bind(big);
    bind(neg);
    bind(pt);
}
"#;

const KINDS_INPUTS: &str = r#"{"x": 3, "y": 9,
 "policy": {"today": "2026-11-11", "born_by": "2008-11-11", "min": "18446744073709551615", "allowed": ["DE","FR","ZW","AD"], "flag": true, "at": "2026-11-11T13:45:00Z"},
 "who": "GB", "name": "Ada Lovelace", "when": "1969-07-20T20:17:40Z",
 "bytes": "0x01ff7e", "pairs": [{"a": 65535, "b": -1}, {"a": 7, "b": -2147483648}],
 "digest": "0x00112233445566778899aabbccddeeff102132435465768798a9bacbdcedfe0f",
 "to": "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA",
 "big": "340282366920938463463374607431768211455", "neg": -42,
 "pt": {"0": 4000000000, "1": "18446744073709551615"}}
"#;

/// `cargo test` in an exported crate, against this checkout's `xark-verifier`
/// (the crate pins the published one); what it printed.
fn cargo_test(verifier: &Path) -> String {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap();
    let manifest = verifier.join("Cargo.toml");
    let mut toml = std::fs::read_to_string(&manifest).unwrap();
    toml += &format!(
        "\n[patch.crates-io]\nxark-verifier = {{ path = \"{}\" }}\nxark-prover = {{ path = \"{}\" }}\n",
        root.join("crates/verifier").display(),
        root.join("crates/prover").display()
    );
    std::fs::write(&manifest, toml).unwrap();
    let o = std::process::Command::new("cargo")
        .args(["test", "--quiet"])
        .current_dir(verifier)
        // A target shared across runs: the verifier's dependencies build once.
        .env("CARGO_TARGET_DIR", root.join("target/export-test"))
        .output()
        .expect("invoke cargo");
    let log = String::from_utf8_lossy(&o.stdout).into_owned() + &String::from_utf8_lossy(&o.stderr);
    assert!(
        o.status.success(),
        "the exported crate's tests failed:\n{log}"
    );
    log
}
