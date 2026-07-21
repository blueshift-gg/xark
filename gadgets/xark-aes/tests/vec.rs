//! End-to-end validation of the AES-128 gadget against FIPS-197 known answers.
//!
//! Each test compiles a small circuit source (calling into `xark_aes`) to the
//! primitive IR via the shared `xark-test-harness` crate, then runs the reference solver
//! on a known test vector and checks (a) it solves + satisfies every constraint,
//! (b) it is analyzer-clean (no under-constrained variables), and (c) a wrong
//! public output is rejected.
//!
//! Layers validated incrementally:
//!   * `gf256_mul` against known GF(2^8) products (0x53·0xCA=0x01, 0x57·0x83=0xC1).
//!   * S-box against FIPS-197 table entries (S(0x00)=0x63, S(0x53)=0xED, S(0xFF)=0x16).
//!   * full AES-128 block against the FIPS-197 KAT.

use std::collections::BTreeMap;

use xark_ir::primitive::PrimitiveProgram;
use xark_ir::solver;

/// Compile a circuit source string to its primitive program via the shared
/// test harness (see `xark-test-harness`).
fn compile(name: &str, src: &str) -> PrimitiveProgram {
    let c = xark_test_harness::compile_source(name, src, "bn254");
    assert!(c.status_success, "compile failed for {name}: {}", c.stderr);
    c.program()
}

fn id_of(p: &PrimitiveProgram, name: &str) -> u32 {
    p.vars
        .iter()
        .find(|v| v.name == name)
        .map(|v| v.id)
        .unwrap()
}

// --------------------------------------------------------------------------
// Layer 1: GF(2^8) multiplication.
// --------------------------------------------------------------------------

#[test]
fn gf_mul_matches_known_products() {
    let src = "#![no_std]\n\
        use xark::{require_eq, Field, Private, Public};\n\
        use xark_aes::gf_mul;\n\
        pub fn circuit(a: Private<Field>, b: Private<Field>, expected: Public<Field>) {\n\
            let r = gf_mul(a.to_bits::<8>(), b.to_bits::<8>());\n\
            require_eq(Field::from_bits::<8>(r), expected);\n\
        }\n";
    let p = compile("gf_mul", src);

    // Known GF(2^8) products (AES field, 0x11B).
    for &(a, b, c) in &[
        (0x53u32, 0xCAu32, 0x01u32),
        (0x57, 0x83, 0xC1),
        (0x02, 0x87, 0x15),
    ] {
        let mut inputs = BTreeMap::new();
        inputs.insert(id_of(&p, "a"), a.to_string());
        inputs.insert(id_of(&p, "b"), b.to_string());
        inputs.insert(id_of(&p, "expected"), c.to_string());
        let assign = solver::solve_and_check(&p, &inputs)
            .unwrap_or_else(|e| panic!("gf_mul {a:#x}·{b:#x} should = {c:#x}: {e:?}"));
        assert!(
            solver::analyze_underconstrained(&p, &assign).is_empty(),
            "gf_mul under-constrained"
        );
        // Wrong product must be rejected.
        inputs.insert(id_of(&p, "expected"), ((c + 1) & 0xff).to_string());
        assert!(
            solver::solve_and_check(&p, &inputs).is_err(),
            "wrong product accepted"
        );
    }
}

// --------------------------------------------------------------------------
// GHASH core: GF(2^128) multiplication in the GCM field, against the `ghash` crate.
// --------------------------------------------------------------------------

#[test]
fn gf128_mul_matches_ghash() {
    use ghash::GHash;
    use ghash::universal_hash::{KeyInit, UniversalHash};

    // Circuit: 16 x-bytes, 16 y-bytes (private), 16 z-bytes (public expected product).
    let mut src = String::from(
        "#![no_std]\n\
         use xark::{require_eq, Field, Private, Public};\n\
         use xark_aes::{gf128_mul, bytes_to_gf128, gf128_to_bytes};\n\
         pub fn circuit(\n",
    );
    for i in 0..16 {
        src.push_str(&format!("  x{i}: Private<Field>,\n"));
    }
    for i in 0..16 {
        src.push_str(&format!("  y{i}: Private<Field>,\n"));
    }
    for i in 0..16 {
        src.push_str(&format!("  z{i}: Public<Field>,\n"));
    }
    src.push_str(") {\n  let x = [");
    for i in 0..16 {
        src.push_str(&format!("x{i},"));
    }
    src.push_str("];\n  let y = [");
    for i in 0..16 {
        src.push_str(&format!("y{i},"));
    }
    src.push_str("];\n  let z = [");
    for i in 0..16 {
        src.push_str(&format!("z{i},"));
    }
    src.push_str(
        "];\n  let p = gf128_to_bytes(gf128_mul(bytes_to_gf128(x), bytes_to_gf128(y)));\n\
         let mut i = 0usize;\n  while i < 16usize { require_eq(p[i], z[i]); i += 1; }\n}\n",
    );
    let p = compile("gf128_mul", &src);
    eprintln!("gf128_mul circuit: {} constraints", p.constraints.len());

    // `GHash::new(H).update(Y)` finalizes to `Y · H` in the GCM field.
    let gf128 = |x: &[u8; 16], y: &[u8; 16]| -> [u8; 16] {
        let mut h = GHash::new(x.into());
        h.update(&[(*y).into()]);
        h.finalize().into()
    };

    let cases: [([u8; 16], [u8; 16]); 3] = [
        // The GCM spec worked example (NIST GCM, H·0 pattern) + arbitrary values.
        (
            [
                0x66, 0xe9, 0x4b, 0xd4, 0xef, 0x8a, 0x2c, 0x3b, 0x88, 0x4c, 0xfa, 0x59, 0xca, 0x34,
                0x2b, 0x2e,
            ],
            [
                0x03, 0x88, 0xda, 0xce, 0x60, 0xb6, 0xa3, 0x92, 0xf3, 0x28, 0xc2, 0xb9, 0x71, 0xb2,
                0xfe, 0x78,
            ],
        ),
        ([1u8; 16], [2u8; 16]),
        (
            [
                0xde, 0xad, 0xbe, 0xef, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99,
                0xaa, 0xbb,
            ],
            [0xff; 16],
        ),
    ];

    for (x, y) in cases.iter() {
        let z = gf128(x, y);
        let mut inputs = BTreeMap::new();
        for i in 0..16 {
            inputs.insert(id_of(&p, &format!("x{i}")), (x[i] as u32).to_string());
            inputs.insert(id_of(&p, &format!("y{i}")), (y[i] as u32).to_string());
            inputs.insert(id_of(&p, &format!("z{i}")), (z[i] as u32).to_string());
        }
        let assign = solver::solve_and_check(&p, &inputs)
            .unwrap_or_else(|e| panic!("gf128_mul {x:02x?}·{y:02x?} should = {z:02x?}: {e:?}"));
        assert!(
            solver::analyze_underconstrained(&p, &assign).is_empty(),
            "gf128_mul under-constrained"
        );
        // A wrong product byte must be rejected.
        inputs.insert(id_of(&p, "z0"), ((z[0] ^ 1) as u32).to_string());
        assert!(
            solver::solve_and_check(&p, &inputs).is_err(),
            "wrong gf128 product accepted"
        );
    }
}

/// Full AES-256 block against the FIPS-197 Appendix C.3 known-answer test:
///   key = 000102…1e1f (32 bytes), pt = 00112233…ff -> ct = 8ea2b7ca…6089
#[test]
fn aes256_matches_fips_kat() {
    let mut src = String::from(
        "#![no_std]\n\
         use xark::{Field, Private, Public};\n\
         use xark_aes::aes256_constrain;\n\
         pub fn circuit(\n",
    );
    for i in 0..16 {
        src.push_str(&format!("  p{i}: Private<Field>,\n"));
    }
    for i in 0..32 {
        src.push_str(&format!("  k{i}: Private<Field>,\n"));
    }
    for i in 0..16 {
        src.push_str(&format!("  c{i}: Public<Field>,\n"));
    }
    src.push_str(") {\n  let pt = [");
    for i in 0..16 {
        src.push_str(&format!("p{i},"));
    }
    src.push_str("];\n  let key = [");
    for i in 0..32 {
        src.push_str(&format!("k{i},"));
    }
    src.push_str("];\n  let ct = [");
    for i in 0..16 {
        src.push_str(&format!("c{i},"));
    }
    src.push_str("];\n  aes256_constrain(pt, key, ct);\n}\n");

    let p = compile("aes256", &src);

    let pt: [u32; 16] = [
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff,
    ];
    let key: [u32; 32] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
        0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d,
        0x1e, 0x1f,
    ];
    let ct: [u32; 16] = [
        0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf, 0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49, 0x60,
        0x89,
    ];

    let mut inputs = BTreeMap::new();
    for i in 0..16 {
        inputs.insert(id_of(&p, &format!("p{i}")), pt[i].to_string());
        inputs.insert(id_of(&p, &format!("c{i}")), ct[i].to_string());
    }
    for (i, k) in key.iter().enumerate() {
        inputs.insert(id_of(&p, &format!("k{i}")), k.to_string());
    }
    let assign = solver::solve_and_check(&p, &inputs).expect("AES-256 FIPS KAT must verify");
    assert!(
        solver::analyze_underconstrained(&p, &assign).is_empty(),
        "AES-256 under-constrained"
    );
    inputs.insert(id_of(&p, "c0"), "0".to_string());
    assert!(
        solver::solve_and_check(&p, &inputs).is_err(),
        "wrong AES-256 ciphertext accepted"
    );
}

// --------------------------------------------------------------------------
// Layer 2: S-box against the FIPS-197 table.
// --------------------------------------------------------------------------

#[test]
fn sbox_matches_fips_table() {
    let src = "#![no_std]\n\
        use xark::{require_eq, Field, Private, Public};\n\
        use xark_aes::sbox;\n\
        pub fn circuit(x: Private<Field>, y: Public<Field>) {\n\
            require_eq(Field::from_bits::<8>(sbox(x.to_bits::<8>())), y);\n\
        }\n";
    let p = compile("sbox", src);

    // Full FIPS-197 S-box table (256 entries), for exhaustive validation.
    const SBOX: [u32; 256] = [
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab,
        0x76, 0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4,
        0x72, 0xc0, 0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71,
        0xd8, 0x31, 0x15, 0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2,
        0xeb, 0x27, 0xb2, 0x75, 0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6,
        0xb3, 0x29, 0xe3, 0x2f, 0x84, 0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb,
        0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf, 0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45,
        0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8, 0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5,
        0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2, 0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44,
        0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73, 0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a,
        0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb, 0xe0, 0x32, 0x3a, 0x0a, 0x49,
        0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79, 0xe7, 0xc8, 0x37, 0x6d,
        0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08, 0xba, 0x78, 0x25,
        0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a, 0x70, 0x3e,
        0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e, 0xe1,
        0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
        0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb,
        0x16,
    ];

    let xid = id_of(&p, "x");
    let yid = id_of(&p, "y");
    for x in 0u32..256 {
        let mut inputs = BTreeMap::new();
        inputs.insert(xid, x.to_string());
        inputs.insert(yid, SBOX[x as usize].to_string());
        let assign = solver::solve_and_check(&p, &inputs)
            .unwrap_or_else(|e| panic!("S({x:#x}) should = {:#x}: {e:?}", SBOX[x as usize]));
        if x == 0 {
            assert!(
                solver::analyze_underconstrained(&p, &assign).is_empty(),
                "sbox under-constrained"
            );
        }
    }
    // Wrong output must be rejected.
    let mut inputs = BTreeMap::new();
    inputs.insert(xid, "83".to_string()); // 0x53
    inputs.insert(yid, "0".to_string()); // S(0x53)=0xED, not 0
    assert!(
        solver::solve_and_check(&p, &inputs).is_err(),
        "wrong sbox accepted"
    );
}

#[test]
fn key_schedule_matches_fips() {
    let src = "#![no_std]\n\
        use xark::{require_eq, Field, Private, Public};\n\
        use xark_aes::key_schedule_byte;\n\
        pub fn circuit(\n\
          k0: Private<Field>,k1: Private<Field>,k2: Private<Field>,k3: Private<Field>,\n\
          k4: Private<Field>,k5: Private<Field>,k6: Private<Field>,k7: Private<Field>,\n\
          k8: Private<Field>,k9: Private<Field>,k10: Private<Field>,k11: Private<Field>,\n\
          k12: Private<Field>,k13: Private<Field>,k14: Private<Field>,k15: Private<Field>,\n\
          e16: Public<Field>, e17: Public<Field>, e18: Public<Field>, e19: Public<Field>,\n\
          e160: Public<Field>, e175: Public<Field>) {\n\
          let key = [k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15];\n\
          require_eq(key_schedule_byte(key, 16), e16);\n\
          require_eq(key_schedule_byte(key, 17), e17);\n\
          require_eq(key_schedule_byte(key, 18), e18);\n\
          require_eq(key_schedule_byte(key, 19), e19);\n\
          require_eq(key_schedule_byte(key, 160), e160);\n\
          require_eq(key_schedule_byte(key, 175), e175);\n\
        }\n";
    let p = compile("ks", src);
    let key: [u32; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    let mut inputs = BTreeMap::new();
    for (i, k) in key.iter().enumerate() {
        inputs.insert(id_of(&p, &format!("k{i}")), k.to_string());
    }
    // FIPS-197 A.1: word4=0xd6aa74fd; word40 byte0=0x13; word43 byte3=0xc5.
    for (n, v) in [
        ("e16", 0xd6u32),
        ("e17", 0xaa),
        ("e18", 0x74),
        ("e19", 0xfd),
        ("e160", 0x13),
        ("e175", 0xc5),
    ] {
        inputs.insert(id_of(&p, n), v.to_string());
    }
    let a = solver::solve_and_check(&p, &inputs);
    if let Err(e) = &a {
        eprintln!("KS solve err at {e:?}");
    }
    a.expect("key schedule must match FIPS-197");
}

// --------------------------------------------------------------------------
// Layer 3: full AES-128 block against the FIPS-197 known-answer test.
//   key = 000102...0f, pt = 00112233...ff -> ct = 69c4e0d8...c55a
// --------------------------------------------------------------------------

#[test]
fn aes128_matches_fips_kat() {
    let mut src = String::from(
        "#![no_std]\n\
         use xark::{Field, Private, Public};\n\
         use xark_aes::aes128_constrain;\n\
         pub fn circuit(\n",
    );
    for i in 0..16 {
        src.push_str(&format!("  p{i}: Private<Field>,\n"));
    }
    for i in 0..16 {
        src.push_str(&format!("  k{i}: Private<Field>,\n"));
    }
    for i in 0..16 {
        src.push_str(&format!("  c{i}: Public<Field>,\n"));
    }
    src.push_str(") {\n  let pt = [");
    for i in 0..16 {
        src.push_str(&format!("p{i},"));
    }
    src.push_str("];\n  let key = [");
    for i in 0..16 {
        src.push_str(&format!("k{i},"));
    }
    src.push_str("];\n  let ct = [");
    for i in 0..16 {
        src.push_str(&format!("c{i},"));
    }
    src.push_str("];\n  aes128_constrain(pt, key, ct);\n}\n");

    let p = compile("aes128", &src);
    eprintln!(
        "AES-128 circuit: {} vars, {} constraints",
        p.vars.len(),
        p.constraints.len()
    );

    let pt: [u32; 16] = [
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff,
    ];
    let key: [u32; 16] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
        0x0f,
    ];
    let ct: [u32; 16] = [
        0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30, 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4, 0xc5,
        0x5a,
    ];

    let mut inputs = BTreeMap::new();
    for i in 0..16 {
        inputs.insert(id_of(&p, &format!("p{i}")), pt[i].to_string());
        inputs.insert(id_of(&p, &format!("k{i}")), key[i].to_string());
        inputs.insert(id_of(&p, &format!("c{i}")), ct[i].to_string());
    }
    let assign = solver::solve_and_check(&p, &inputs).expect("AES-128 FIPS KAT must verify");
    let holes = solver::analyze_underconstrained(&p, &assign);
    assert!(holes.is_empty(), "AES-128 under-constrained: {holes:?}");

    // A wrong ciphertext byte must be rejected.
    inputs.insert(id_of(&p, "c0"), "0".to_string());
    assert!(
        solver::solve_and_check(&p, &inputs).is_err(),
        "wrong ciphertext accepted"
    );
}
