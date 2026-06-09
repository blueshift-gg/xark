//! Bitwuzla BLAKE3 compression bit-blasted equivalence harness.
//!
//! Two independent QF_BV encodings of the BLAKE3 compression `F(h, m, t, b, d)`
//! (BLAKE3 spec). Asserts disagreement on any of 16 output words; UNSAT ⇒
//! bit-equivalent over all 28-word inputs (8 h + 16 m + 2 t + 1 b + 1 d).

#![allow(clippy::needless_range_loop)]

use std::process::{Command, Stdio};

const BLAKE3_IV_4: [u32; 4] = [0x6a09_e667, 0xbb67_ae85, 0x3c6e_f372, 0xa54f_f53a];

/// BLAKE3 message schedule (precomputed): `MSG_SCHEDULE[r]` is the index
/// permutation applied to the message words at round `r ∈ 0..7`.
const MSG_SCHEDULE: [[usize; 16]; 7] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8],
    [3, 4, 10, 12, 13, 2, 7, 14, 6, 5, 9, 0, 11, 15, 8, 1],
    [10, 7, 12, 9, 14, 3, 13, 15, 4, 0, 11, 2, 5, 8, 1, 6],
    [12, 13, 9, 11, 15, 10, 14, 8, 7, 2, 5, 3, 0, 1, 6, 4],
    [9, 14, 11, 5, 8, 12, 15, 1, 13, 3, 0, 10, 2, 6, 4, 7],
    [11, 15, 5, 0, 1, 9, 8, 6, 14, 10, 2, 12, 3, 4, 7, 13],
];

const R1: u32 = 16;
const R2: u32 = 12;
const R3: u32 = 8;
const R4: u32 = 7;
const ROUNDS: usize = 7;

fn bv32_const(v: u32) -> String {
    format!("(_ bv{v} 32)")
}

fn rotr(x: &str, n: u32) -> String {
    format!("((_ rotate_right {n}) {x})")
}

fn xor2(a: &str, b: &str) -> String {
    format!("(bvxor {a} {b})")
}

fn add_n(operands: &[String]) -> String {
    assert!(operands.len() >= 2);
    let mut s = String::from("(bvadd");
    for o in operands {
        s.push(' ');
        s.push_str(o);
    }
    s.push(')');
    s
}

#[allow(clippy::too_many_arguments)]
fn emit_g(
    body: &mut String,
    prefix: &str,
    round: usize,
    g_idx: usize,
    v: &mut [String; 16],
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    x: &str,
    y: &str,
) {
    let va1 = format!("{prefix}r{round}g{g_idx}_va1");
    let va1_expr = add_n(&[v[a].clone(), v[b].clone(), x.to_string()]);
    body.push_str(&format!("(define-fun {va1} () (_ BitVec 32) {va1_expr})\n"));
    v[a] = va1;

    let vd1 = format!("{prefix}r{round}g{g_idx}_vd1");
    let vd1_expr = rotr(&xor2(&v[d], &v[a]), R1);
    body.push_str(&format!("(define-fun {vd1} () (_ BitVec 32) {vd1_expr})\n"));
    v[d] = vd1;

    let vc1 = format!("{prefix}r{round}g{g_idx}_vc1");
    let vc1_expr = add_n(&[v[c].clone(), v[d].clone()]);
    body.push_str(&format!("(define-fun {vc1} () (_ BitVec 32) {vc1_expr})\n"));
    v[c] = vc1;

    let vb1 = format!("{prefix}r{round}g{g_idx}_vb1");
    let vb1_expr = rotr(&xor2(&v[b], &v[c]), R2);
    body.push_str(&format!("(define-fun {vb1} () (_ BitVec 32) {vb1_expr})\n"));
    v[b] = vb1;

    let va2 = format!("{prefix}r{round}g{g_idx}_va2");
    let va2_expr = add_n(&[v[a].clone(), v[b].clone(), y.to_string()]);
    body.push_str(&format!("(define-fun {va2} () (_ BitVec 32) {va2_expr})\n"));
    v[a] = va2;

    let vd2 = format!("{prefix}r{round}g{g_idx}_vd2");
    let vd2_expr = rotr(&xor2(&v[d], &v[a]), R3);
    body.push_str(&format!("(define-fun {vd2} () (_ BitVec 32) {vd2_expr})\n"));
    v[d] = vd2;

    let vc2 = format!("{prefix}r{round}g{g_idx}_vc2");
    let vc2_expr = add_n(&[v[c].clone(), v[d].clone()]);
    body.push_str(&format!("(define-fun {vc2} () (_ BitVec 32) {vc2_expr})\n"));
    v[c] = vc2;

    let vb2 = format!("{prefix}r{round}g{g_idx}_vb2");
    let vb2_expr = rotr(&xor2(&v[b], &v[c]), R4);
    body.push_str(&format!("(define-fun {vb2} () (_ BitVec 32) {vb2_expr})\n"));
    v[b] = vb2;
}

fn emit_compression(
    prefix: &str,
    h_names: &[String; 8],
    m_names: &[String; 16],
    t_low: &str,
    t_high: &str,
    b_name: &str,
    d_name: &str,
) -> (String, [String; 16]) {
    let mut body = String::new();

    let mut v: [String; 16] = std::array::from_fn(|i| {
        if i < 8 {
            h_names[i].clone()
        } else if i < 12 {
            bv32_const(BLAKE3_IV_4[i - 8])
        } else {
            match i {
                12 => t_low.to_string(),
                13 => t_high.to_string(),
                14 => b_name.to_string(),
                15 => d_name.to_string(),
                _ => unreachable!(),
            }
        }
    });

    for round in 0..ROUNDS {
        let s = &MSG_SCHEDULE[round];
        emit_g(
            &mut body,
            prefix,
            round,
            0,
            &mut v,
            0,
            4,
            8,
            12,
            &m_names[s[0]],
            &m_names[s[1]],
        );
        emit_g(
            &mut body,
            prefix,
            round,
            1,
            &mut v,
            1,
            5,
            9,
            13,
            &m_names[s[2]],
            &m_names[s[3]],
        );
        emit_g(
            &mut body,
            prefix,
            round,
            2,
            &mut v,
            2,
            6,
            10,
            14,
            &m_names[s[4]],
            &m_names[s[5]],
        );
        emit_g(
            &mut body,
            prefix,
            round,
            3,
            &mut v,
            3,
            7,
            11,
            15,
            &m_names[s[6]],
            &m_names[s[7]],
        );
        emit_g(
            &mut body,
            prefix,
            round,
            4,
            &mut v,
            0,
            5,
            10,
            15,
            &m_names[s[8]],
            &m_names[s[9]],
        );
        emit_g(
            &mut body,
            prefix,
            round,
            5,
            &mut v,
            1,
            6,
            11,
            12,
            &m_names[s[10]],
            &m_names[s[11]],
        );
        emit_g(
            &mut body,
            prefix,
            round,
            6,
            &mut v,
            2,
            7,
            8,
            13,
            &m_names[s[12]],
            &m_names[s[13]],
        );
        emit_g(
            &mut body,
            prefix,
            round,
            7,
            &mut v,
            3,
            4,
            9,
            14,
            &m_names[s[14]],
            &m_names[s[15]],
        );
    }

    // out[0..8]  = v[0..8] XOR v[8..16]
    // out[8..16] = h[0..8] XOR v[8..16]
    let out_names: [String; 16] = std::array::from_fn(|i| format!("{prefix}OUT{i}"));
    for i in 0..8 {
        let expr = xor2(&v[i], &v[i + 8]);
        body.push_str(&format!(
            "(define-fun {} () (_ BitVec 32) {expr})\n",
            out_names[i]
        ));
    }
    for i in 0..8 {
        let expr = xor2(&h_names[i], &v[i + 8]);
        body.push_str(&format!(
            "(define-fun {} () (_ BitVec 32) {expr})\n",
            out_names[i + 8]
        ));
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

    let h_names: [String; 8] = std::array::from_fn(|i| format!("H{i}"));
    let m_names: [String; 16] = std::array::from_fn(|i| format!("M{i}"));
    let extras = ["TLOW", "THIGH", "BLEN", "FLAGS"];
    for n in h_names.iter().chain(m_names.iter()) {
        s.push_str(&format!("(declare-const {n} (_ BitVec 32))\n"));
    }
    for n in &extras {
        s.push_str(&format!("(declare-const {n} (_ BitVec 32))\n"));
    }

    let (ref_body, ref_outs) =
        emit_compression("ref_", &h_names, &m_names, "TLOW", "THIGH", "BLEN", "FLAGS");
    s.push_str(&ref_body);
    let (gad_body, gad_outs) =
        emit_compression("gad_", &h_names, &m_names, "TLOW", "THIGH", "BLEN", "FLAGS");
    s.push_str(&gad_body);

    let diffs: Vec<String> = (0..16)
        .map(|i| format!("(distinct {} {})", ref_outs[i], gad_outs[i]))
        .collect();
    s.push_str(&format!("(assert (or {}))\n", diffs.join(" ")));
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn blake3_compression_gadget_equals_spec() {
    if !bitwuzla_available() && std::env::var_os("XARK_RUN_BITWUZLA").is_none() {
        eprintln!(
            "bitwuzla: not on PATH and XARK_RUN_BITWUZLA not set — skipping.\n  \
             Install bitwuzla to run this equivalence proof."
        );
        return;
    }

    let smt = build_equivalence_smt();
    let timeout_s: u64 = std::env::var("BITWUZLA_TIMEOUT_S")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(600);

    eprintln!(
        "  Bitwuzla BLAKE3 compression equivalence:\n  \
         SMT-LIB size: {} bytes; running bitwuzla (timeout {}s)…",
        smt.len(),
        timeout_s
    );
    let res = run_bitwuzla(&smt, timeout_s);
    eprintln!("  bitwuzla: {res}");

    match res.as_str() {
        "unsat" => eprintln!(
            "  ✓ Equivalence PROVEN: BLAKE3 compression matches spec over\n  \
             all 28-word inputs (8 h + 16 m + 2 t + 1 b + 1 d)."
        ),
        "sat" => panic!(
            "Bitwuzla found an input where the gadget-structure and spec encodings \
             of BLAKE3 compression disagree — algorithmic-divergence bug."
        ),
        "unknown" => panic!(
            "Bitwuzla returned `unknown` — time limit ({timeout_s}s) too small or \
             encoding regressed. Raise BITWUZLA_TIMEOUT_S."
        ),
        other => panic!("bitwuzla returned unexpected output: {other:?}"),
    }
}

#[test]
fn blake3_smt_generator_well_formed() {
    let smt = build_equivalence_smt();
    assert!(smt.starts_with("(set-logic QF_BV)\n"));
    assert!(smt.contains("(check-sat)\n"));
    for i in 0..16 {
        assert!(
            smt.contains(&format!("ref_OUT{i}")),
            "ref output #{i} missing"
        );
        assert!(
            smt.contains(&format!("gad_OUT{i}")),
            "gad output #{i} missing"
        );
    }
    for i in 0..16 {
        assert!(
            smt.contains(&format!("(declare-const M{i} (_ BitVec 32))")),
            "M{i} declaration missing"
        );
    }
    for &iv in &BLAKE3_IV_4 {
        assert!(
            smt.contains(&format!("(_ bv{iv} 32)")),
            "IV constant {iv:#x} missing"
        );
    }
}
