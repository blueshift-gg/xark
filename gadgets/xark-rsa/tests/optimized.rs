//! Differential and edge-case tests for the optimized RSA-2048 proving path.
//!
//! The KAT in `known_answer.rs` proves one generated RSA vector. These tests
//! exercise the relation itself: generated keys and digests, the edge
//! signatures, an even modulus (the relation is mathematical; key validity is
//! the caller's), the SHA-256-word entry point, and a host `pow` differential
//! for `mod_exp_65537`.

use std::collections::BTreeMap;

use num_bigint::BigUint;
use xark_ir::{primitive, solver};

const LIMBS: usize = 17;
const BITS: u32 = 121;

const KEY1_N: &str = "C2E2FF352E07AAD69235351D2D535F8CBE3DA97AB8FE82403193F468F92647C7EBD7F8C0B795799CD584837DA22DFBA13116B3E1A1087BC3A31C1B3901933AB127EF1BF0F70C03E19B6673A70329B743C0611DE6EF0C76D5CBF318B6969E036D09700928C65B1062FF0E0F75B264AFBA5FFDE4D0505EC27F2C4A1795F1BB88EECD94971D52ECB53D90B7B68F110A8CCB06383012285D63C1DC2E99A62A21538047F2C9C64BCC49A47D2697520BB4D54E7F4D185601C1B5D5DBADC5DAF5284FD85AECF9633E6E05859CC6771FD23FB2F5ADE4F3E0727E2CE8D3B8C9E30A071446B83DCB067FB55C386718FEE30C98DB1538265651DA379B4BCF71B0CC670F3F99";
const KEY1_D: &str = "52a920162e5a9230f0a820c9d4afc841ff6efd5e5043a326173694def17935ce564faf480e9617e9ada6c71eed40690fb5ad2b7448193bbad48982026be89c11b2c9232626f85c57bf7cca6677064ff52cb959e02f04850da9b3dd323f859b6e6427b6657fbca04c07b80456a793e29fea9730b62ab6069e6a4002ebabdc74a217b930664784ffc9e9d6128f31239d60f2adfc1bf37d6efe8c4dfd5f6f61f74c6af5c7ca9dd159125b87cea9de02e9b91900e379b0668488ab286814cad0b06d1e3e7ab15bde66c7c87270dfac5f8c78f00b1197330f0a895886deb2d299d077a7babdaff841ca0cf30cb68aa5fe4b52986743896bcb71b6187101a7ecccb5";
const KEY2_N: &str = "912C77138481054462E04A009C9C3834EA36B25B2742C005B30FB920E596BAA8F52F9EBF2AA5D85408637B9940730D3BE3F53F97803A02C8B4F703B387DE5ABA2E604F1FADD4943076B34249EE5764BE0B5D59C32AC421C7DA0F1053265DA4E4DE190ED7E026BDAA0B10BAD2A33DDA2F38C5E9AD61F4FEE5D7DA76BA1667010AABB68DBACE1C8468A59E1166C7C6FCC9978AA1144F00D7BBAE23F9A3DA6E64D8C0DC13BA9991A099CD3C768AD0463C5CCCEB24719E28F1EB830535C5C5E3A38D6B751D31B37AE2BA8559637130727025ABC56DAAE2986F1CE2EA9DE143FB18101C7721D91D8760E99CBD7D477595AF667F9D63AC926417958305DF6048354A49";
const KEY2_D: &str = "02977aa0bc92d9173974ab9d8b2e36caab0bc2ef61aa0d678ca4d137472203bf14717f32067ee377cc968a145854357e463990a311c4f75bc1ef4eff9b835ab74c30a7f8f6cf7ebdc6c0b8843d5f0e0b5e84921fabd9c8889ad9fdfe9e06b9f4e40a2a7bac22c4ec0e3a843b5272be3c6d950af0ef78c23c3438503a4e401482a75ff6716fb60115ed7019785536f6d356c7b3a59a7a8457210ad4c0f57a6f9f024e1de870cfb505b15aeff3fd2db6d01ad86760b1b08cf1e9673b59447d517b1dcfb1807f92176a2ef1dcf2ec5ebe8d842acea08c8199eed503a0e4d21bcc93cb8d87f454289ac24e1f6d9de734dc414dce4181a54e44f8a25caf4e38790569";

/// An even modulus `n = 2q`, `q` a 2047-bit prime, with `d = 65537^-1 mod q-1`.
/// The relation `s^65537 == EM (mod n)` holds, though `n` is not an RSA key.
const EVEN_N: &str = "de2e6f01d5ff9b918d31f67e3ba61e91727ebcaf6d4d92c9267039321982d2c62532c522d83157bac12f048adba12a213a2ee5479e1383fda48904cfe0926071defa7fcfd840038f7e68dfe1d1445cf07c3abf2484b1273ff48dd64f14ab935024be64eb19311f07814bc02c7e8599e9fbc572eba20cabcd4085db5f52fdabca52e598fbc0f3897459c5a53ea82b964693b317f8140bf9ca77278247c4c3f7cc00718bf27212d794a69b916cf3527b1d510a89b55e36f93b88658a7233aab9ab37b7a3094adcf36b3cb5e7aabfb4c9a41ab69ca3bd7a3a64d364c75014d23c6b2262a6c152aa8b28354a7543bbe250564d0861790456708373825ed29f375406";
const EVEN_D: &str = "2c274e282f3efccb9023bdb898620af11cafd30f89c940c278c1149cc0351f6e013675b6d6fff74f45d4f2322633810bd964386c631dbdbd4a55707f5f41b7a8e9871e9f4f7a693abb045c79a3fcd1fb78b4b407add706d5cee3e113162882be0a8f4bbeece2b627e7aa0626d17dfb78647078c61b0e2996409c595c3841f141e3f77ccf8b28dac8248f02a7d103d8796e20c942a3b93d8adee31b20e81989c520d16fde5e8d200a8a919ff4e6e61d515629a1f44924e3a2d1185ccb1539786c6e4630404880605f8f511718f7c015d266fca36466e34377860b2110e9125eaf6bc5ef1dbc2fe837b55f76ae5f483a6eec201e3ece7ddf1e40764821d3424b9";

/// SHA-256("abc"), the NIST FIPS 180-4 vector.
const SHA256_ABC: &str = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";

fn big(hex: &str) -> BigUint {
    BigUint::parse_bytes(hex.as_bytes(), 16).unwrap()
}

fn key(n: &str, d: &str) -> (BigUint, BigUint) {
    (big(n), big(d))
}

fn digest(hex: &str) -> [u8; 32] {
    hex::decode(hex).unwrap().try_into().unwrap()
}

/// EMSA-PKCS1-v1_5 for SHA-256, exactly as RFC 8017 section 9.2 specifies.
fn em(digest: &[u8; 32]) -> BigUint {
    let digest_info = hex::decode("3031300d060960864801650304020105000420").unwrap();
    let mut bytes = vec![0x00u8, 0x01];
    bytes.extend(std::iter::repeat_n(0xffu8, 202));
    bytes.push(0x00);
    bytes.extend(digest_info);
    bytes.extend(digest.iter());
    assert_eq!(bytes.len(), 256);
    BigUint::from_bytes_be(&bytes)
}

fn sign(n: &BigUint, d: &BigUint, digest: &[u8; 32]) -> BigUint {
    em(digest).modpow(d, n)
}

fn limbs_121(x: &BigUint) -> Vec<BigUint> {
    let mask = (BigUint::from(1u8) << BITS) - 1u8;
    (0..LIMBS)
        .map(|i| (x >> (BITS * i as u32)) & &mask)
        .collect()
}

fn load(name: &str) -> primitive::PrimitiveProgram {
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(format!("{name}.rs"));
    let c = xark_test_harness::compile_file(&src, name, "bn254");
    assert!(c.status_success, "compiling {name} failed: {}", c.stderr);
    let p = c.program();
    println!(
        "{name}: {} primitive constraints, {} multiplication gates",
        p.constraints.len(),
        c.mul_gate_count()
    );
    p
}

fn id_of(p: &primitive::PrimitiveProgram, name: &str) -> u32 {
    p.vars
        .iter()
        .find(|v| v.name == name)
        .unwrap_or_else(|| panic!("missing `{name}`"))
        .id
}

fn insert_limbs(
    p: &primitive::PrimitiveProgram,
    out: &mut BTreeMap<u32, String>,
    prefix: &str,
    x: &BigUint,
) {
    for (i, l) in limbs_121(x).into_iter().enumerate() {
        out.insert(id_of(p, &format!("{prefix}[{i}]")), l.to_string());
    }
}

fn rsa_inputs(
    p: &primitive::PrimitiveProgram,
    n: &BigUint,
    sig: &BigUint,
    digest: &[u8; 32],
) -> BTreeMap<u32, String> {
    let mut out = BTreeMap::new();
    insert_limbs(p, &mut out, "n", n);
    insert_limbs(p, &mut out, "sig", sig);
    for (i, b) in digest.iter().enumerate() {
        out.insert(id_of(p, &format!("digest[{i}]")), b.to_string());
    }
    out
}

fn words_flat(p: &primitive::PrimitiveProgram, digest: &[u8; 32]) -> BTreeMap<u32, String> {
    let mut out = BTreeMap::new();
    for w in 0..8usize {
        let v = u32::from_be_bytes(digest[4 * w..4 * w + 4].try_into().unwrap());
        for b in 0..32usize {
            out.insert(
                id_of(p, &format!("flat[{}]", 32 * w + b)),
                ((v >> b) & 1).to_string(),
            );
        }
    }
    out
}

fn accepts(p: &primitive::PrimitiveProgram, inputs: &BTreeMap<u32, String>) {
    let assign = solver::solve_and_check(p, inputs)
        .unwrap_or_else(|e| panic!("honest input must solve: {e:?}"));
    assert!(
        solver::analyze_underconstrained(p, &assign).is_empty(),
        "circuit must be fully constrained"
    );
}

fn rejects(p: &primitive::PrimitiveProgram, inputs: &BTreeMap<u32, String>) {
    assert!(
        solver::solve_and_check(p, inputs).is_err(),
        "input must be rejected"
    );
}

/// Reject at a specific constraint row. This keeps the top-bit and `sig < n`
/// checks regression-protected: without the check the input usually still
/// fails later at the EM equality, so a bare `is_err` would pass.
fn rejects_at(p: &primitive::PrimitiveProgram, inputs: &BTreeMap<u32, String>, row: u32) {
    let e = solver::solve_and_check(p, inputs).expect_err("input must be rejected");
    let msg = format!("{e:?}");
    assert!(
        msg.contains(&row.to_string()),
        "expected row {row} in {msg}"
    );
}

#[test]
fn accepts_generated_signatures() {
    let p = load("rsa2048");
    let digests = [
        [0u8; 32],
        [0xffu8; 32],
        digest(SHA256_ABC),
        digest("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"),
    ];
    for (n, d) in [key(KEY1_N, KEY1_D), key(KEY2_N, KEY2_D)] {
        for dg in &digests {
            let s = sign(&n, &d, dg);
            assert!(s < n);
            accepts(&p, &rsa_inputs(&p, &n, &s, dg));
        }
    }
}

#[test]
fn rejects_edge_signatures() {
    let p = load("rsa2048");
    let (n, d) = key(KEY1_N, KEY1_D);
    let dg = [0u8; 32];
    for s in [
        BigUint::from(0u8),
        BigUint::from(1u8),
        &n - 1u8,
        n.clone(),
        &n + 1u8,
    ] {
        rejects(&p, &rsa_inputs(&p, &n, &s, &dg));
    }
    // A valid signature over a different digest is not accepted.
    let s = sign(&n, &d, &dg);
    let mut other = dg;
    other[0] ^= 1;
    rejects(&p, &rsa_inputs(&p, &n, &s, &other));
}

#[test]
fn even_modulus_relation_is_accepted() {
    let p = load("rsa2048");
    let n = big(EVEN_N);
    let d = big(EVEN_D);
    assert_eq!(&n % 2u8, BigUint::from(0u8));
    let dg = [0u8; 32];
    let s = sign(&n, &d, &dg);
    // The gadget verifies `s^65537 mod n == EM`; it does not claim `n` is a
    // valid RSA key. Callers take `n` from a trusted key, as the README says.
    accepts(&p, &rsa_inputs(&p, &n, &s, &dg));
}

#[test]
fn n_must_have_exactly_2048_bits() {
    let p = load("rsa2048");
    let dg = [0u8; 32];
    // 2047-bit modulus: the top-bit check, not the later EM check, must reject it.
    let n = (BigUint::from(1u8) << 2046u32) + 1u8;
    rejects_at(&p, &rsa_inputs(&p, &n, &BigUint::from(0u8), &dg), 14216);
    // 2049-bit modulus: `convert_wide` rejects the non-zero top carry.
    let n = (BigUint::from(1u8) << 2048u32) + (BigUint::from(1u8) << 2047u32) + 1u8;
    rejects_at(&p, &rsa_inputs(&p, &n, &BigUint::from(0u8), &dg), 9309);
}

#[test]
fn sig_equal_or_above_n_is_rejected_at_require_lt() {
    let p = load("rsa2048");
    let (n, _) = key(KEY1_N, KEY1_D);
    let dg = [0u8; 32];
    // Without `require_lt`, `sig = n` still fails at the EM pin; assert the
    // rejection is the comparison, not the EM.
    rejects_at(&p, &rsa_inputs(&p, &n, &n, &dg), 14366);
}

#[test]
fn words_path_matches_the_byte_path() {
    let p = load("rsa2048_words");
    let (n, d) = key(KEY1_N, KEY1_D);
    for dg in [[0u8; 32], digest(SHA256_ABC)] {
        let s = sign(&n, &d, &dg);
        let mut inputs = BTreeMap::new();
        insert_limbs(&p, &mut inputs, "n", &n);
        insert_limbs(&p, &mut inputs, "sig", &s);
        inputs.extend(words_flat(&p, &dg));
        accepts(&p, &inputs);
    }
    // A non-boolean "bit" must be rejected: the word entry point constrains
    // its digest bits, so the encoded message stays a bounded affine vector.
    let s = sign(&n, &d, &[0u8; 32]);
    let mut inputs = BTreeMap::new();
    insert_limbs(&p, &mut inputs, "n", &n);
    insert_limbs(&p, &mut inputs, "sig", &s);
    inputs.extend(words_flat(&p, &[0u8; 32]));
    let first = id_of(&p, "flat[0]");
    inputs.insert(first, "2".to_string());
    rejects(&p, &inputs);
    // And a genuine one-bit change to the digest is a different message.
    let mut inputs = BTreeMap::new();
    insert_limbs(&p, &mut inputs, "n", &n);
    insert_limbs(&p, &mut inputs, "sig", &s);
    inputs.extend(words_flat(&p, &[0u8; 32]));
    let bit = id_of(&p, "flat[0]");
    inputs.insert(bit, "1".to_string());
    rejects(&p, &inputs);
}

#[test]
fn modexp_matches_host_pow() {
    let src = r#"
use xark::{Field, Private, circuit};
use xark_rsa::mod_exp_65537;
#[circuit]
pub fn modexp(n: Private<[Field; 17]>, sig: Private<[Field; 17]>, want: Private<[Field; 17]>) {
    let m1 = xark_bignum::minus_one::<17, 121>(n);
    let r = mod_exp_65537(sig, n, m1);
    let mut i = 0usize;
    while i < 17usize { xark::require_eq(r[i], want[i]); i += 1; }
}
"#;
    let c = xark_test_harness::compile_source("rsa_modexp", src, "bn254");
    assert!(c.status_success, "compiling modexp failed: {}", c.stderr);
    let p = c.program();
    let e = BigUint::from(65537u32);
    let odd_n = big(KEY1_N);
    let even_n = big(EVEN_N);
    let near_low = (BigUint::from(1u8) << 2047u32) + 1u8;
    let near_high = (BigUint::from(1u8) << 2048u32) - 1u8;
    let mut seed = 0x1234_5678_9abc_def0u64;
    let mut rng = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for n in [&odd_n, &even_n, &near_low, &near_high] {
        for sig in [
            BigUint::from(0u8),
            BigUint::from(1u8),
            n - 1u8,
            (BigUint::from(rng()) << 1024u32) | BigUint::from(rng()),
        ] {
            let want = sig.modpow(&e, n);
            let mut inputs = BTreeMap::new();
            insert_limbs(&p, &mut inputs, "n", n);
            insert_limbs(&p, &mut inputs, "sig", &sig);
            insert_limbs(&p, &mut inputs, "want", &want);
            accepts(&p, &inputs);
            // A wrong expected value must be rejected.
            let wrong = (&want + 1u8) % n;
            insert_limbs(&p, &mut inputs, "want", &wrong);
            rejects(&p, &inputs);
        }
    }
}

#[test]
fn sha256_em_matches_rfc8017() {
    let src = r#"
use xark::{Field, Private, circuit};
use xark_rsa::sha256_em;
#[circuit]
pub fn em_check(digest: Private<[u8; 32]>, want: Private<[Field; 17]>) {
    let em = sha256_em(digest);
    let mut i = 0usize;
    while i < 17usize { xark::require_eq(em[i], want[i]); i += 1; }
}
"#;
    let c = xark_test_harness::compile_source("rsa_em_check", src, "bn254");
    assert!(c.status_success, "compiling em_check failed: {}", c.stderr);
    let p = c.program();
    for dg in [
        [0u8; 32],
        [0xffu8; 32],
        digest(SHA256_ABC),
        digest("c37a1c1585bccadb102bba2ee173596132d6a355e9dbf4921096564937f690be"),
    ] {
        let mut inputs = BTreeMap::new();
        for (i, b) in dg.iter().enumerate() {
            inputs.insert(id_of(&p, &format!("digest[{i}]")), b.to_string());
        }
        insert_limbs(&p, &mut inputs, "want", &em(&dg));
        accepts(&p, &inputs);
        // Any wrong limb must fail.
        let wrong = em(&dg) + 1u8;
        insert_limbs(&p, &mut inputs, "want", &wrong);
        rejects(&p, &inputs);
    }
}
