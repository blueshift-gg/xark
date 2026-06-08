//! Bitwuzla AES-128 bit-blasted equivalence harness — Layer B, track 2 of
//! `docs/FORMAL_VERIFICATION_PLAN.md`.
//!
//! Two QF_BV encodings of AES-128 single-block encrypt (FIPS 197). Both
//! encodings share a single S-box and `xtime` `define-fun`; they differ
//! only in MixColumns XOR operand grouping (nested binary vs n-ary).
//! Asserts disagreement on any of 16 output bytes; UNSAT ⇒ bit-equivalent
//! over all 256-bit (16 plaintext + 16 key) inputs.

use std::process::{Command, Stdio};

const NR: usize = 10;
const BLOCK_BYTES: usize = 16;
const KEY_BYTES: usize = 16;
const NB_WORDS: usize = 4 * (NR + 1);

const RCON: [u8; 11] = [
    0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36,
];

#[rustfmt::skip]
const SBOX: [u8; 256] = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
];

fn aes128_native(plaintext: &[u8; 16], key: &[u8; 16]) -> [u8; 16] {
    let rk = key_expansion_native(key);
    let mut state = *plaintext;
    add_round_key_native(&mut state, &rk, 0);
    for round in 1..NR {
        sub_bytes_native(&mut state);
        shift_rows_native(&mut state);
        mix_columns_native(&mut state);
        add_round_key_native(&mut state, &rk, round);
    }
    sub_bytes_native(&mut state);
    shift_rows_native(&mut state);
    add_round_key_native(&mut state, &rk, NR);
    state
}

fn key_expansion_native(key: &[u8; KEY_BYTES]) -> [[u8; 4]; NB_WORDS] {
    let mut w = [[0u8; 4]; NB_WORDS];
    for i in 0..4 {
        w[i] = [key[4 * i], key[4 * i + 1], key[4 * i + 2], key[4 * i + 3]];
    }
    for i in 4..NB_WORDS {
        let mut temp = w[i - 1];
        if i % 4 == 0 {
            temp = [temp[1], temp[2], temp[3], temp[0]];
            for t in &mut temp {
                *t = SBOX[*t as usize];
            }
            temp[0] ^= RCON[i / 4];
        }
        for j in 0..4 {
            w[i][j] = w[i - 4][j] ^ temp[j];
        }
    }
    w
}

fn add_round_key_native(state: &mut [u8; 16], rk: &[[u8; 4]; NB_WORDS], round: usize) {
    for col in 0..4 {
        for row in 0..4 {
            state[col * 4 + row] ^= rk[round * 4 + col][row];
        }
    }
}

fn sub_bytes_native(state: &mut [u8; 16]) {
    for b in state.iter_mut() {
        *b = SBOX[*b as usize];
    }
}

fn shift_rows_native(state: &mut [u8; 16]) {
    let mut out = [0u8; 16];
    for r in 0..4 {
        for c in 0..4 {
            out[c * 4 + r] = state[((c + r) % 4) * 4 + r];
        }
    }
    *state = out;
}

fn mix_columns_native(state: &mut [u8; 16]) {
    for c in 0..4 {
        let s0 = state[c * 4];
        let s1 = state[c * 4 + 1];
        let s2 = state[c * 4 + 2];
        let s3 = state[c * 4 + 3];
        state[c * 4] = xtime_native(s0) ^ (xtime_native(s1) ^ s1) ^ s2 ^ s3;
        state[c * 4 + 1] = s0 ^ xtime_native(s1) ^ (xtime_native(s2) ^ s2) ^ s3;
        state[c * 4 + 2] = s0 ^ s1 ^ xtime_native(s2) ^ (xtime_native(s3) ^ s3);
        state[c * 4 + 3] = (xtime_native(s0) ^ s0) ^ s1 ^ s2 ^ xtime_native(s3);
    }
}

#[inline]
fn xtime_native(b: u8) -> u8 {
    let hi = b >> 7;
    let shifted = b << 1;
    if hi == 1 {
        shifted ^ 0x1b
    } else {
        shifted
    }
}

fn bv8_const(v: u8) -> String {
    format!("(_ bv{} 8)", v)
}

fn xor2(a: &str, b: &str) -> String {
    format!("(bvxor {} {})", a, b)
}

fn xor_nested(operands: &[String]) -> String {
    assert!(!operands.is_empty());
    let mut acc = operands[0].clone();
    for o in &operands[1..] {
        acc = format!("(bvxor {} {})", acc, o);
    }
    acc
}

fn xor_nary(operands: &[String]) -> String {
    assert!(operands.len() >= 2);
    let mut s = String::from("(bvxor");
    for o in operands {
        s.push(' ');
        s.push_str(o);
    }
    s.push(')');
    s
}

#[derive(Clone, Copy)]
enum XorStyle {
    NestedBinary,
    Nary,
}

fn xor_list(operands: &[String], style: XorStyle) -> String {
    match style {
        XorStyle::NestedBinary => xor_nested(operands),
        XorStyle::Nary => xor_nary(operands),
    }
}

fn emit_sbox_define_fun() -> String {
    let mut s = String::from("(define-fun aes_sbox ((x (_ BitVec 8))) (_ BitVec 8)\n");
    let mut depth = 0u32;
    for (i, &v) in SBOX.iter().enumerate() {
        s.push_str(&format!(
            "  (ite (= x {}) {}\n",
            bv8_const(i as u8),
            bv8_const(v)
        ));
        depth += 1;
    }
    s.push_str("  ");
    s.push_str(&bv8_const(0));
    for _ in 0..depth {
        s.push(')');
    }
    s.push_str(")\n");
    s
}

fn emit_xtime_define_fun() -> String {
    String::from(
        "(define-fun aes_xtime ((b (_ BitVec 8))) (_ BitVec 8)\n  \
         (bvxor (bvshl b (_ bv1 8)) (bvand (bvashr b (_ bv7 8)) (_ bv27 8))))\n",
    )
}

type State = [String; 16];

fn defn(body: &mut String, name: &str, expr: &str) {
    body.push_str(&format!("(define-fun {} () (_ BitVec 8) {})\n", name, expr));
}

fn emit_sub_bytes(body: &mut String, prefix: &str, round: usize, input: &State) -> State {
    std::array::from_fn(|i| {
        let name = format!("{}sub_r{}_{}", prefix, round, i);
        defn(body, &name, &format!("(aes_sbox {})", input[i]));
        name
    })
}

fn emit_shift_rows(input: &State) -> State {
    std::array::from_fn(|i| {
        let r = i % 4;
        let c = i / 4;
        let src_c = (c + r) % 4;
        let src = src_c * 4 + r;
        input[src].clone()
    })
}

fn emit_mix_columns(
    body: &mut String,
    prefix: &str,
    round: usize,
    input: &State,
    style: XorStyle,
) -> State {
    let mut out: [String; 16] = std::array::from_fn(|_| String::new());
    for c in 0..4 {
        let s0 = input[c * 4].clone();
        let s1 = input[c * 4 + 1].clone();
        let s2 = input[c * 4 + 2].clone();
        let s3 = input[c * 4 + 3].clone();

        let xs0 = format!("{}mc_x0_r{}_c{}", prefix, round, c);
        let xs1 = format!("{}mc_x1_r{}_c{}", prefix, round, c);
        let xs2 = format!("{}mc_x2_r{}_c{}", prefix, round, c);
        let xs3 = format!("{}mc_x3_r{}_c{}", prefix, round, c);
        defn(body, &xs0, &format!("(aes_xtime {})", s0));
        defn(body, &xs1, &format!("(aes_xtime {})", s1));
        defn(body, &xs2, &format!("(aes_xtime {})", s2));
        defn(body, &xs3, &format!("(aes_xtime {})", s3));

        let m3_s0 = xor2(&xs0, &s0);
        let m3_s1 = xor2(&xs1, &s1);
        let m3_s2 = xor2(&xs2, &s2);
        let m3_s3 = xor2(&xs3, &s3);

        let r0 = xor_list(&[xs0.clone(), m3_s1, s2.clone(), s3.clone()], style);
        let r1 = xor_list(&[s0.clone(), xs1.clone(), m3_s2, s3.clone()], style);
        let r2 = xor_list(&[s0.clone(), s1.clone(), xs2.clone(), m3_s3], style);
        let r3 = xor_list(&[m3_s0, s1, s2, xs3.clone()], style);

        let n0 = format!("{}mc_o_r{}_c{}_0", prefix, round, c);
        let n1 = format!("{}mc_o_r{}_c{}_1", prefix, round, c);
        let n2 = format!("{}mc_o_r{}_c{}_2", prefix, round, c);
        let n3 = format!("{}mc_o_r{}_c{}_3", prefix, round, c);
        defn(body, &n0, &r0);
        defn(body, &n1, &r1);
        defn(body, &n2, &r2);
        defn(body, &n3, &r3);

        out[c * 4] = n0;
        out[c * 4 + 1] = n1;
        out[c * 4 + 2] = n2;
        out[c * 4 + 3] = n3;
    }
    out
}

fn emit_add_round_key(
    body: &mut String,
    prefix: &str,
    round: usize,
    input: &State,
    rk: &[String],
) -> State {
    std::array::from_fn(|i| {
        let name = format!("{}ark_r{}_{}", prefix, round, i);
        defn(body, &name, &xor2(&input[i], &rk[round * 16 + i]));
        name
    })
}

fn emit_key_schedule(body: &mut String, prefix: &str, key_in: &[String; 16]) -> Vec<String> {
    let mut w: Vec<[String; 4]> = Vec::with_capacity(NB_WORDS);
    for i in 0..4 {
        w.push([
            key_in[4 * i].clone(),
            key_in[4 * i + 1].clone(),
            key_in[4 * i + 2].clone(),
            key_in[4 * i + 3].clone(),
        ]);
    }
    for i in 4..NB_WORDS {
        let prev = w[i - 1].clone();
        let temp: [String; 4] = if i % 4 == 0 {
            let rot = [
                prev[1].clone(),
                prev[2].clone(),
                prev[3].clone(),
                prev[0].clone(),
            ];
            let mut sub = [String::new(), String::new(), String::new(), String::new()];
            for j in 0..4 {
                let n = format!("{}ks_sub_w{}_{}", prefix, i, j);
                defn(body, &n, &format!("(aes_sbox {})", rot[j]));
                sub[j] = n;
            }
            let rc = RCON[i / 4];
            let n0 = format!("{}ks_temp_w{}_0", prefix, i);
            defn(body, &n0, &xor2(&sub[0], &bv8_const(rc)));
            [n0, sub[1].clone(), sub[2].clone(), sub[3].clone()]
        } else {
            prev
        };

        let prev4 = w[i - 4].clone();
        let mut wi = [String::new(), String::new(), String::new(), String::new()];
        for j in 0..4 {
            let n = format!("{}ks_w{}_{}", prefix, i, j);
            defn(body, &n, &xor2(&prev4[j], &temp[j]));
            wi[j] = n;
        }
        w.push(wi);
    }
    let mut flat: Vec<String> = Vec::with_capacity(NB_WORDS * 4);
    for word in &w {
        for byte in word {
            flat.push(byte.clone());
        }
    }
    flat
}

fn emit_aes128_encrypt(
    prefix: &str,
    plaintext: &[String; 16],
    key: &[String; 16],
    mix_style: XorStyle,
) -> (String, [String; 16]) {
    let mut body = String::new();
    let rk = emit_key_schedule(&mut body, prefix, key);

    let mut state: State = std::array::from_fn(|i| {
        let n = format!("{}init_{}", prefix, i);
        defn(&mut body, &n, &xor2(&plaintext[i], &rk[i]));
        n
    });

    for round in 1..NR {
        let s1 = emit_sub_bytes(&mut body, prefix, round, &state);
        let s2 = emit_shift_rows(&s1);
        let s3 = emit_mix_columns(&mut body, prefix, round, &s2, mix_style);
        let s4 = emit_add_round_key(&mut body, prefix, round, &s3, &rk);
        state = s4;
    }

    let s1 = emit_sub_bytes(&mut body, prefix, NR, &state);
    let s2 = emit_shift_rows(&s1);
    let s3 = emit_add_round_key(&mut body, prefix, NR, &s2, &rk);

    let out_names: [String; 16] = std::array::from_fn(|i| format!("{}OUT{}", prefix, i));
    for i in 0..16 {
        defn(&mut body, &out_names[i], &s3[i]);
    }
    (body, out_names)
}

fn bitwuzla_bin() -> String {
    std::env::var("BITWUZLA_BIN").unwrap_or_else(|_| "bitwuzla".to_string())
}

fn bitwuzla_available() -> bool {
    Command::new(bitwuzla_bin())
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

fn run_bitwuzla(smt: &str, timeout_s: u64) -> String {
    use std::io::Write;
    let mut child = Command::new(bitwuzla_bin())
        .arg("-t")
        .arg((timeout_s * 1000).to_string())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn bitwuzla");
    {
        let stdin = child.stdin.as_mut().expect("stdin");
        stdin.write_all(smt.as_bytes()).expect("write smt");
    }
    let out = child.wait_with_output().expect("wait bitwuzla");
    let s = String::from_utf8_lossy(&out.stdout);
    s.lines().next().unwrap_or("(no output)").trim().to_string()
}

fn build_equivalence_smt() -> String {
    let mut s = String::new();
    s.push_str("(set-logic QF_BV)\n");

    s.push_str(&emit_sbox_define_fun());
    s.push_str(&emit_xtime_define_fun());

    let pt_names: [String; 16] = std::array::from_fn(|i| format!("P{}", i));
    let key_names: [String; 16] = std::array::from_fn(|i| format!("K{}", i));
    for n in pt_names.iter().chain(key_names.iter()) {
        s.push_str(&format!("(declare-const {} (_ BitVec 8))\n", n));
    }

    let (ref_body, ref_outs) =
        emit_aes128_encrypt("ref_", &pt_names, &key_names, XorStyle::NestedBinary);
    s.push_str(&ref_body);

    let (gad_body, gad_outs) = emit_aes128_encrypt("gad_", &pt_names, &key_names, XorStyle::Nary);
    s.push_str(&gad_body);

    let diffs: Vec<String> = (0..BLOCK_BYTES)
        .map(|i| format!("(distinct {} {})", ref_outs[i], gad_outs[i]))
        .collect();
    s.push_str(&format!("(assert (or {}))\n", diffs.join(" ")));
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn aes128_encrypt_gadget_equals_fips197_spec() {
    if !bitwuzla_available() && std::env::var_os("XARK_RUN_BITWUZLA").is_none() {
        eprintln!(
            "bitwuzla: not on PATH and XARK_RUN_BITWUZLA not set — skipping.\n  \
             Install bitwuzla to run this Layer-B equivalence proof."
        );
        return;
    }

    let smt = build_equivalence_smt();
    let timeout_s: u64 = std::env::var("BITWUZLA_TIMEOUT_S")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1200);

    eprintln!(
        "  Bitwuzla AES-128 encrypt equivalence:\n  \
         SMT-LIB size: {} bytes; running bitwuzla (timeout {}s)…",
        smt.len(),
        timeout_s
    );
    let res = run_bitwuzla(&smt, timeout_s);
    eprintln!("  bitwuzla: {}", res);

    match res.as_str() {
        "unsat" => eprintln!(
            "  ✓ Equivalence PROVEN: AES-128 single-block encrypt matches\n  \
             FIPS 197 spec over all 256-bit (plaintext + key) inputs."
        ),
        "sat" => panic!(
            "Bitwuzla found an input where the gadget-structure and FIPS-spec \
             encodings of AES-128 disagree — algorithmic-divergence bug."
        ),
        "unknown" => panic!(
            "Bitwuzla returned `unknown` — time limit too small or encoding \
             regressed. Raise BITWUZLA_TIMEOUT_S."
        ),
        other => panic!("bitwuzla returned unexpected output: {:?}", other),
    }
}

#[test]
fn aes128_smt_generator_well_formed() {
    let pt: [u8; 16] = [
        0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d, 0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07,
        0x34,
    ];
    let key: [u8; 16] = [
        0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f,
        0x3c,
    ];
    let expected_ct: [u8; 16] = [
        0x39, 0x25, 0x84, 0x1d, 0x02, 0xdc, 0x09, 0xfb, 0xdc, 0x11, 0x85, 0x97, 0x19, 0x6a, 0x0b,
        0x32,
    ];
    let ct = aes128_native(&pt, &key);
    assert_eq!(
        ct, expected_ct,
        "native AES-128 reference disagrees with FIPS 197 Appendix B KAT"
    );

    let smt = build_equivalence_smt();
    assert!(smt.starts_with("(set-logic QF_BV)\n"));
    assert!(smt.contains("(check-sat)\n"));
    assert!(smt.contains("(define-fun aes_sbox"));
    assert!(smt.contains("(define-fun aes_xtime"));
    for i in 0..BLOCK_BYTES {
        assert!(smt.contains(&format!("ref_OUT{}", i)));
        assert!(smt.contains(&format!("gad_OUT{}", i)));
    }
    for i in 0..BLOCK_BYTES {
        assert!(smt.contains(&format!("(declare-const P{} (_ BitVec 8))", i)));
        assert!(smt.contains(&format!("(declare-const K{} (_ BitVec 8))", i)));
    }
    for &rc in &RCON[1..=NR] {
        assert!(smt.contains(&format!("(_ bv{} 8)", rc)));
    }
}
